#!/bin/bash
#set -x
shopt -s globstar nullglob

# CONFIG

# Send SIGHUP after this much time
EXTERNAL_TIMEOUT="31m"

# Send SIGKILL this much time after SIGHUP was sent
KILL_AFTER="6m"

JOBS="50%"

# CODE

panic() {
  echo "$1" > /dev/stderr
  exit 1
}

original_dir=$(pwd)
sampler_dir=$(realpath ..)

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
External timeout: ${EXTERNAL_TIMEOUT} (+${KILL_AFTER})
Additional arguments: ${@:3}
EOF

# run sampler and collect json files
for f in "${input_dir}"/**/*.smt2
do
  # Process benchmarks that are marked as satisfiable (not unsat or unknown)
  grep ":status" ${f} | grep unsat > /dev/null && continue
  # X: Actually unknowns are fine 
  # grep ":status" ${f} | grep sat > /dev/null || continue
  echo "Processing: ${f}"
  cur_output_dir="${newdir}$(dirname ${f#$input_dir})"
  echo "Output to: ${cur_output_dir}"
  pushd ${sampler_dir}
  sem -j${JOBS} --id "$0" -- \
      timeout --foreground -k${KILL_AFTER} -sHUP ${EXTERNAL_TIMEOUT} \
      ./smtsampler --json -o ${cur_output_dir} "${@:3}" "${f}"
  popd
done
sem --id "$0" --wait

cat >> "${newdir}/README.rst" <<EOF
Finished run at $(date -Iseconds)
EOF
