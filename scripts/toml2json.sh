#!/usr/bin/env bash
# convert all .toml files in directory testdata to .json files via toml2json

if [ ! -d "./scripts" ]; then
    echo "please run from project directory"
    exit 1
fi

function t2j() {
    FILE=$(echo "$1" | sed 's/toml/json/')
    toml2json --pretty "$1" > ${FILE}
}

export -f t2j

# why are these files excluded from the testdata
#   substring.toml: not valid for api
#   utf8.toml: only unicode is valid
#   overlapping.toml: not vaild for BoundedBacktracker algorithm
#   no-unicode.toml: only unicode is valid
#   regex-lite.toml: only valid for the regex-lite algorithm

find testdata/ -not -name "substring.toml" \
  -not -name "utf8.toml" -not -name "overlapping.toml" \
  -not -name "no-unicode.toml" -not -name "regex-lite.toml" \
  -name "*.toml" -exec bash -c "t2j \"{}\"" \;
