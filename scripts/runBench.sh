#!/bin/bash
#set -x
shopt -s globstar nullglob

# CONFIG

# Send SIGHUP after this much time
EXTERNAL_TIMEOUT="11m"

# Send SIGKILL this much time after SIGHUP was sent
KILL_AFTER="3m"

JOBS="50%"

INPUT_DIR="$(realpath $(dirname $0)/../16_bench/)"

MODE_NAMES=( "MeGA" "MeGAb" "SMT" )
MODE_OPTIONS=( " " "-b" "-x" )
GLOBAL_OPTIONS="--json --time=600"

# CODE

panic() {
  echo "$1" > /dev/stderr
  exit 1
}

original_dir=$(dirname $0)
sampler_dir=$(realpath "${original_dir}/..")


#parse input
[ $# -ge 1 ] || panic "Script arguments should receive at least one argument: output_dir."

output_dir="$1"
[[ -d "${output_dir}" ]] || panic "First argument (output directory) is not a directory: $output_dir"
output_dir="$(realpath "${output_dir}")"
echo "Output directory is: '${output_dir}'"

newdir="${output_dir}/$(date -Iseconds)"
mkdir "${newdir}"
for mode in ${MODE_NAMES[@]}
do
    mkdir ${newdir}/${mode}
done

cat > "${newdir}/README.rst" <<EOF
Started run at $(date -Iseconds)
Input dir is: "${INPUT_DIR}"
Git commit is: $(git rev-parse --short HEAD)
External timeout: ${EXTERNAL_TIMEOUT} (+${KILL_AFTER})
EOF

# run sampler and collect json files
for f in "${INPUT_DIR}"/**/*.smt2
do
  # Process benchmarks that are marked as satisfiable (not unsat or unknown)
  grep ":status" ${f} | grep unsat > /dev/null && continue
  # X: Actually unknowns are fine
  # grep ":status" ${f} | grep sat > /dev/null || continue
  echo "Processing: ${f}"
  for i in {0..2}
  do
      cur_output_dir="${newdir}/${MODE_NAMES[$i]}/$(dirname ${f#$INPUT_DIR})"
      echo "Output to: ${cur_output_dir}"
      pushd ${sampler_dir}
      sem -j${JOBS} --id "$0" -- \
          timeout --foreground -k${KILL_AFTER} -sHUP ${EXTERNAL_TIMEOUT} \
          ./megasampler ${GLOBAL_OPTIONS} -o ${cur_output_dir} \
          ${MODE_OPTIONS[$i]} "${@:3}" "${f}"
      popd
  done
done
sem --id "$0" --wait

cat >> "${newdir}/README.rst" <<EOF
Done running benchmarks at $(date -Iseconds)
EOF

if [ -e ${sampler_dir}/pypyvenv ]
then
    cat >> "${newdir}/README.rst" <<EOF
Found pypy, using that for metric calculation.
EOF
    source ${sampler_dir}/pypyvenv/bin/activate
fi

python ${original_dir}/calc_dir_metrics.py -f ${INPUT_DIR} \
       ${MODE_NAMES[@]/#/ -s ${newdir}/}

cat >> "${newdir}/README.rst" <<EOF
Done calculating metric at $(date -Iseconds)

Results [ mode samples|metric ]:
EOF

for f in "${INPUT_DIR}"/**/*.smt2
do
    echo ${f#${INPUT_DIR}} | tee -a "${newdir}/README.rst"
    for mode in ${MODE_NAMES[@]}
    do
        curr="${newdir}/${mode}/${f#${INPUT_DIR}}"
        echo -n ${mode} $(jq '.["unique valid samples"]' "${curr}.json")"|"$(jq '.["wire_coverage"]' "${curr}.json") " " | tee -a "${newdir}/README.rst"
    done
    echo | tee -a "${newdir}/README.rst"
done


cat >> "${newdir}/README.rst" <<EOF

Finished run at $(date -Iseconds)
EOF
