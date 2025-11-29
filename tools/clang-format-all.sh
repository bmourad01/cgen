#!/bin/sh

# C/C++ sources
files_to_indent='.*\.\(c\|h\|cc\|cpp\|cxx\|hpp\)$'

VERSION=$(clang-format --version 2>/dev/null)

if [ -z "$VERSION" ]; then
    echo "Please install clang-format"
    exit 1
else
    echo "Reindenting with $VERSION"
fi

git ls-files | grep -e "$files_to_indent" | while read file
do
    clang-format -i "$file"
done
