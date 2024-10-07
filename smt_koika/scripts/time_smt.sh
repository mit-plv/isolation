#! /bin/sh
#

src_dir=$1
smt_dir="src"
# files=("$src_dir"/*.ml)
out_dir=$2 
file_switch="$smt_dir/file_switch.ml"
mkdir -p $out_dir

#for filename in "${files[@]}"; do
for filename in $src_dir/*.ml; do
  base=$(basename "$filename")
  mod_name="${base%.*}"
#  echo $filename $base $mod_name
  echo "let file = Extracted.$mod_name.file" > "$file_switch"
  echo "$filename"
  cp "$filename" "$smt_dir/extracted.ml"
  dune build "$smt_dir"
  output=$( (/usr/bin/time --format="%Uuser %Ssystem %eelapsed" "./_build/default/src/main.exe") 2>&1)
  last_line=$(echo "$output" | tail -n 2 | head -n 1)
  echo "Result: $last_line"
  user_time=$(echo "$output"| tail -n 1 | grep -oP '\d+\.\d+(?=user)')
  echo "Time: $user_time seconds"
  log=$out_dir/$base.log
  debug_log=$out_dir/$base.debug_log
  > $debug_log
  echo "$output" > $debug_log

  > $log

  echo "$filename" >>  "$log"
  echo "Result: $last_line" >> "$log"
  echo "Time: $user_time" >> "$log"
done


#dune build deps/koika/coq
#dune build koika/src/koika
#time dune build koika/src/koikaExamples/Enclaves
