#!/bin/bash

# Pretty rough approximations
echo "CLOCing impl files"
IMPL_FILES=("Impl.v" "Util.v")
cloc "${IMPL_FILES[@]}"

echo "CLOCing spec files"
SPEC_FILES=("Spec.v" "Theorem.v")
cloc "${SPEC_FILES[@]}"

echo "CLOCing proof files"
PROOF_FILES=("ProofImpl.v" "ProofSim.v" "ProofSpec.v" "Proof.v")
cloc "${PROOF_FILES[@]}"



