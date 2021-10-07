#!/bin/bash
#set -x

panic() {
  echo "$1" > /dev/stderr
  exit 1
}

original_dir=$(pwd)
sampler_dir=$(realpath ..)

#parse input
[ $# -ge 2 ] || panic "Script arguments should receive at least two arguments: input_dir and output_dir."

input_dir="$1"
[[ -d "$input_dir" ]] || panic "First argument (input directory) is not a directory: $input_dir"
input_dir=$(realpath "$input_dir")
echo "Input directory is: $input_dir"

output_dir="$2"
[[ -d "$output_dir" ]] || panic "Second argument (output directory) is not a directory: $output_dir"
output_dir=$(realpath "$output_dir")
echo "Output directory is: $output_dir"

newdir="${output_dir}/$(basename "$input_dir")_$(date -Iseconds)"
mkdir "$newdir"

# run sampler and collect json files
shopt -s globstar nullglob
for f in "$input_dir"/**/*.smt2
do
  # Process benchmarks that are marked as satisfiable (not unsat or unknown)
  grep ":status" ${f} | grep unsat > /dev/null && continue
  grep ":status" ${f} | grep sat > /dev/null || continue
  echo "Processing: ${f}"
  cur_output_dir="${newdir}$(dirname ${f#$input_dir})"
  echo "Output to: ${cur_output_dir}"
  pushd ${sampler_dir}
  sem -j50% --id "$0" -- ./smtsampler --json -o ${cur_output_dir} "${@:3}" "${f}"
  popd
done
sem --id "$0" --wait
