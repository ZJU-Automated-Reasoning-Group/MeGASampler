#!/bin/bash
#set -x
shopt -s globstar nullglob

# CONFIG

# Send SIGHUP after this much time
EXTERNAL_TIMEOUT="31m"

# Send SIGKILL this much time after SIGHUP was sent
KILL_AFTER="6m"

JOBS="50%"

MODE_NAMES=( "MeGA" "MeGAb" "SMT" "Z3" )
MODE_OPTIONS=( "-a mega" "-a megab" "-a smt" "-a z3" )
GLOBAL_OPTIONS="--json"

# CODE

panic() {
  echo "$1" > /dev/stderr
  exit 1
}

original_dir=$(dirname $0)
sampler_dir=$(realpath "${original_dir}/..")

#parse input
[ $# -ge 2 ] || panic "Script arguments should receive at least two arguments: input_dir and output_dir."

input_dir="$1"
[[ -d "${input_dir}" ]] || panic "First argument (input directory) is not a directory: $input_dir"
input_dir="$(realpath "${input_dir}")"
echo "Input directory is: $input_dir"

output_dir="$2"
[[ -d "${output_dir}" ]] || panic "Second argument (output directory) is not a directory: $output_dir"
output_dir="$(realpath "${output_dir}")"
echo "Output directory is: '${output_dir}'"

newdir="${output_dir}/$(basename "$input_dir")_$(date -Iseconds)"
mkdir "${newdir}"


cat > "${newdir}/README.rst" <<EOF
Started run at $(date -Iseconds)
Input dir is: "${INPUT_DIR}"
Git commit is: $(git rev-parse --short HEAD)
External timeout: ${EXTERNAL_TIMEOUT} (+${KILL_AFTER})
EOF

function handle_sample_files() {
    f=$1
    while /usr/bin/pgrep -f 'megasampler.*'"${f#${input_dir}}"'$' > /dev/null
    do
        # wait for megasampler to finish
        sleep 5
    done
    sem -j${JOBS} --id "$0" -- python ${original_dir}/calc_dir_metrics.py \
        -i ${f} -f ${input_dir} ${MODE_NAMES[@]/#/-s ${newdir}\//} -d
}

# run sampler and collect json files
for f in "${input_dir}"/**/*.smt2
do
  # Process benchmarks that are marked as satisfiable (not unsat or unknown)
  grep ":status" ${f} | grep unsat > /dev/null && continue
  # X: Actually unknowns are fine
  # grep ":status" ${f} | grep sat > /dev/null || continue
  echo "Processing: ${f}"
  for (( i = 0; i < ${#MODE_NAMES[@]}; i++ ))
  do
      cur_output_dir="${newdir}/${MODE_NAMES[$i]}/$(dirname ${f#$input_dir})"
      echo "Output to: ${cur_output_dir}"
      pushd ${sampler_dir} > /dev/null
      sem -j${JOBS} --id "$0" -- \
          timeout --foreground -k${KILL_AFTER} -sHUP ${EXTERNAL_TIMEOUT} \
          ./megasampler ${GLOBAL_OPTIONS} -o ${cur_output_dir} \
          ${MODE_OPTIONS[$i]} "${@:3}" "${f}"
      popd > /dev/null
  done
  handle_sample_files "${f}" &
done
sem --id "$0" --wait

cat >> "${newdir}/README.rst" <<EOF
Finished run at $(date -Iseconds)
EOF
