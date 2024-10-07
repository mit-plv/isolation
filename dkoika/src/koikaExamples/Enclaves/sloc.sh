#!/bin/bash

# Pretty rough approximations

echo "CLOCing spec files"
SPEC_FILES=("Spec.v" "Theorem.v")
cloc "${SPEC_FILES[@]}"

echo "CLOCing all files"
cloc *.v

echo "CLOCing modular_pfsim"
cloc Modular_PfSim.v

echo "CLOCing monolithic_pfsim"
cloc Monolithic_PfSim.v


spec_lines=$(cloc "${SPEC_FILES[@]}" --csv --quiet | tail -n 1 | cut -d ',' -f 5)
echo $spec_lines
all_lines=$(cloc *.v --csv --quiet | tail -n 1 | cut -d ',' -f 5)
echo $all_lines
monolithic_lines=$(cloc "Monolithic_PfSim.v" --csv --quiet | tail -n 1 | cut -d ',' -f 5)
modular_lines=$(cloc "Modular_PfSim.v" --csv --quiet | tail -n 1 | cut -d ',' -f 5)

monolithic=$(($all_lines - $spec_lines-$modular_lines))
modular=$(($all_lines - $spec_lines-$monolithic_lines))

echo "Proof lines: monolithic:$monolithic, modular:$modular" 




