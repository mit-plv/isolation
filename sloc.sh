#!/bin/bash

echo "CLOCing impl files"
IMPL_FILES=("coq/examples/ResourceIsolation_Impl.v" "coq/examples/ResourceIsolation_Util.v")
cloc "${IMPL_FILES[@]}"

echo "CLOCing spec files"
SPEC_FILES=("coq/examples/ResourceIsolation_Spec.v" "coq/examples/ResourceIsolation_Theorem.v")
cloc "${SPEC_FILES[@]}"

echo "CLOCing proof files"
PROOF_FILES=("coq/examples/ResourceIsolation_ProofImpl.v" "coq/examples/ResourceIsolation_ProofSim.v" "coq/examples/ResourceIsolation_ProofSpec.v" "coq/examples/ResourceIsolation_Proof.v")
cloc "${PROOF_FILES[@]}"



