shopt -s nullglob globstar

INPUT=$1
OUTPUT=$2

THIS_TALL=15

[ -z "${INPUT}" ] || [ -z "${OUTPUT}" ] && { echo "$0 INPUT_DIR OUTPUT_DIR"; exit 1; }

find ${INPUT} -maxdepth 1 -type d -and -not -iname '.' | while read inputdir; do
	dir="$(realpath --relative-to="${INPUT}" "${inputdir}")"
	benchmarks=("${INPUT}/${dir}"/**/*.smt2)
	echo ${dir}: ${#benchmarks[@]}
	if [ ${#benchmarks[@]} -lt ${THIS_TALL} ]; then continue; fi
	#echo "${dir}: More than ${THIS_TALL} benchmarks, picking some"
	#echo mkdir -p "${OUTPUT}/${dir}"
	#find "${INPUT}/${dir}" -name '*.smt2' -maxdepth 1 -print0 | shuf -z -n ${THIS_TALL} | xargs -0 echo cp -at "${OUTPUT}/${dir}"
done
