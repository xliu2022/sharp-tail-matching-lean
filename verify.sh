#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"

check_kernels=false
check_comparator=false
for option in "$@"; do
  case "$option" in
    --kernels) check_kernels=true ;;
    --comparator) check_comparator=true ;;
    -h|--help)
      echo 'Usage: bash verify.sh [--kernels] [--comparator]'
      echo 'Default: source checks, metadata validation, build, statement and axiom audit.'
      echo '--kernels: also replay exported proofs with Lean, NanoDa and con-ron.'
      echo '--comparator: also run protected Comparator; requires Linux and bubblewrap.'
      exit 0 ;;
    *) echo "Unknown option: $option" >&2; exit 2 ;;
  esac
done

python3 scripts/check-lean-sources.py
python3 verification/check_sources.py
ruby scripts/validate-formalization.rb formalization.yaml
lake build
if "$check_kernels"; then
  python3 verification/run_checks.py --kernels
else
  python3 verification/run_checks.py
fi
if "$check_comparator"; then
  bash scripts/verify-comparator.sh
fi
