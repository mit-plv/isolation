#! /bin/sh

# Brought to you by... ChatGPT! 
src_dir=$1
total_time=0
times=()

# Extract time from each log file
for file in $1/*.log; do
    time_str=$(grep 'Time:' $file | awk '{print $2}')
#    echo $time_str
    time_in_seconds=$time_str
    echo "$file - $time_in_seconds seconds"

    total_time=$(bc <<< "$total_time + $time_in_seconds")
    times+=($time_in_seconds)
done

# Calculate total time
echo "Total time: $total_time seconds"

calculate_max() {
  local vmax=($(printf '%s\n' "$@" | sort -n | tail -1))
  echo $vmax
}

# Max time
max_time=$(calculate_max "${times[@]}")

echo "Max time: $max_time seconds"

# Function to calculate median
calculate_median() {
    local arr=($(printf '%s\n' "$@" | sort -n))
    local count=${#arr[@]}
    if (( $count % 2 == 1 )); then
        echo ${arr[$((count/2))]}
    else
        local lower_mid=${arr[$((count/2-1))]}
        local upper_mid=${arr[$((count/2))]}
        echo $(bc <<< "scale=2; ($lower_mid+$upper_mid)/2")
    fi
}

# Calculate and print median time
median_time=$(calculate_median "${times[@]}")

echo "Median time: $median_time seconds"


