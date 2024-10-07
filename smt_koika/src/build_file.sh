#! /bin/sh
#

file_switch="file_switch.ml"
file_extracted="extracted.ml"
file=$1
base=$(basename "$file")
mod_name="${base%.*}"
echo $1
cp "$file" "$file_extracted"
echo "let file = Extracted.$mod_name.file" > "$file_switch"
dune build 


