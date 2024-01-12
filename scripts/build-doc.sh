#!/usr/bin/env bash

if [ ! -d "./scripts" ]; then
    echo "please run from project directory"
    exit 1
fi

rm -rf .lake/build/doc/
lake -R -Kenv=dev build Regex:docs

bash -c "cd .lake/build/doc/ && python3 -m http.server"
