#!/bin/bash

MIN_SAMPLES=100


OPTIND=1
while getopts "o:i:p:e:" opt; do
	case ${opt} in
		o) 
			output="${OPTARG}"
			;;
		i)
			input="$OPTARG"
			;;
		p) 
			prune_by="${OPTARG}"
			;;
		e)
			exceptions="${OPTARG}"
			;;
		*)
			echo "Unknown parameter"
			exit 1
			;;
	esac
done
shift "$((OPTIND-1))"

[ -z "${input}" ] || [ ! -d "${input}" ] && { echo "Bad input: ${input}"; exit 1; }
[ -z "${output}" ] && { echo "No output"; exit 1; }
[ -z "${exceptions}" ] && { echo "No exceptions"; exit 1; }
[ -z "${prune_by}" ] || [ ! -d "${prune_by}" ] && { echo "Bad prune by dir: ${prune_by}"; exit 1; }

[ -e "${output}" ] && { echo "Output already exists!"; exit 1; }
[ -e "${exceptions}" ] && { echo "Exceptions already exists!"; exit 1; }

mkdir -p "${output}"
mkdir -p "${exceptions}"
shopt -s globstar nullglob
for f in "${input}"/**/*.smt2; do
	benchmark="$(realpath --relative-to="${input}" "${f}")"
	json="${prune_by}/${benchmark}.json"
	samples="${prune_by}/${benchmark}.samples"
	sat=$(grep -c ":status.*[^n]sat" "${input}/${benchmark}")
	if [ "${sat}" -eq 0 ]; then
		# its unsat or unknown, ignore
		continue
	fi
	if [ -e "${samples}" ] && [ ! -e "${json}" ]; then
		echo "${benchmark}: Found samples file but no JSON, uncaught exception or OOM killer?"
		mkdir -p "$(dirname "${exceptions}/${benchmark}")"
		cp -a "${input}/${benchmark}" "${exceptions}/${benchmark}" 
		continue
	fi
	if [ ! -e "${json}" ]; then
		echo "${benchmark}: No JSON, yet sat -- didn't run?"
		mkdir -p "$(dirname "${exceptions}/${benchmark}")"
		cp -a "${input}/${benchmark}" "${exceptions}/${benchmark}" 
		continue
	fi
	nsamples=$(jq '.["valid samples"]' "${json}")
	if [ -z "${nsamples}" ] || [ "${nsamples}" -lt ${MIN_SAMPLES} ]; then
		echo "${benchmark}: Valid samples=<${nsamples}> < ${MIN_SAMPLES}, pruning"
		continue
	fi
	echo "${benchmark}: Good. :)"
	mkdir -p "$(dirname "${output}/${benchmark}")"
	cp -a "${input}/${benchmark}" "${output}/${benchmark}"
done
