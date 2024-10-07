#!/bin/bash

 make pretty-timed

log_file="time-of-build-pretty.log"

convert_time_to_seconds() {
    local time_str=$1
    local mins=$(echo $time_str | cut -d'm' -f1)
    local secs=$(echo $time_str | cut -d's' -f1 | cut -d'm' -f2)
    echo $(echo "$mins * 60 + $secs" | bc)
}

total_time_in_seconds=0

while read -r line; do
    # Check if line contains 'coq/examples'
    if [[ $line == *"coq/examples"* ]]; then
        # Extract time and memory
        time_str=$(echo $line | awk '{print $1}')

        # Convert time to seconds and add to total
        time_in_seconds=$(convert_time_to_seconds $time_str)
        total_time_in_seconds=$(echo "$total_time_in_seconds + $time_in_seconds" | bc)

    fi
done < "$log_file"

# Output the results
echo "Total Time: $total_time_in_seconds seconds" 
echo "Total Time: $total_time_in_seconds seconds" >> "$log_file"


