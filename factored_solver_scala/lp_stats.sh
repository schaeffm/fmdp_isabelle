#!/bin/bash

# Check if file is provided as an argument
if [ -z "$1" ]; then
  echo "Usage: $0 <filename>"
  exit 1
fi

# Get the filename from the argument
filename="$1"

# Check if the file exists
if [ ! -f "$filename" ]; then
  echo "File not found!"
  exit 1
fi


# Get the last line that starts with "y" followed by a number
last_y_line=$(grep -E '^y[0-9]+' "$filename" | tail -n 1)

# Check if a line was found and extract the number
if [[ $last_y_line =~ ^y([0-9]+) ]]; then
	echo "Constraints: $((${BASH_REMATCH[1]} + 1))"
else
  echo "No line starting with 'y' followed by a number was found."
fi

# Get the second to last line
second_to_last_line=$(tail -n 2 "$filename" | head -n 1)

# Check if the second to last line starts with "x" followed by a number
if [[ $second_to_last_line =~ ^x([0-9]+) ]]; then
  x_number="${BASH_REMATCH[1]}"
  echo "Variables: $((x_number + 1))"
else
  echo "The second to last line does not start with 'x' followed by a number."
fi
