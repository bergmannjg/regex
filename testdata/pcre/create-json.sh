#! /bin/sh

# create json from perltest.sh

if [ $# -eq 0 ] ; then
  echo "usage: create-json.sh filename "
  exit 1
fi

FILE=$1

./perltest.sh -json ${FILE} | grep '##' | sed 's/##//' | jq 'del(recurse | select(. == {}))'
