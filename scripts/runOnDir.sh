#!/bin/bash
#set -x

original_dir=$(pwd)
sampler_dir=$(realpath ..)

#parse input
if [ ! $# -ge 2 ]; then
    echo "Script arguments should receive at least two arguments: input_dir and output_dir."
    exit 1
fi
input_dir="$1"
if [[ ! -d "$input_dir" ]]; then
  echo "First argument (input directory) is not a directory: $input_dir"
  exit 1
else
  input_dir=$(realpath "$input_dir")
  echo "Input directory is: $input_dir"
fi
output_dir="$2"
if [[ ! -d "$output_dir" ]]; then
  echo "Second argument (output directory) is not a directory: $output_dir"
  exit 1
else
  output_dir=$(realpath "$output_dir")
  echo "Output directory is: $output_dir"
fi

newdir="$output_dir/$(basename "$input_dir")_$(date '+%d-%m-%Y-%H-%M-%S')_json"
mkdir "$newdir"
# run sampler and collect json files
shopt -s globstar nullglob
for file in "$input_dir"/**/*.smt2
do
  echo "$file"
  cd "$sampler_dir" || ( echo "couldn't find directory $sampler_dir" && exit 1 )
  ./smtsampler --json "${@:3}" "$file"
#  move json files to new_dir while keeping original dir structure as in input_dir
  new_json_file=$newdir${file#$input_dir}.json
  echo "Attempting to move json file to $new_json_file"
  mkdir -p "$(dirname "$new_json_file")"
  mv "$file.json" "$new_json_file" || ( echo "could not find file $file.json" && echo "$file" >> "$newdir/missing_jsons.txt" )
  cd "$original_dir" || ( echo "couldn't find directory $original_dir" && exit 1 )
done
