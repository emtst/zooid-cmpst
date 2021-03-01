#!/bin/bash

ZOOID_DIR="$( cd "$(dirname "$0")" >/dev/null 2>&1 ; cd .. ; pwd -P )"

pushd $ZOOID_DIR

echo "WARNING!!"
echo
echo "About to run 'git clean -xdf'. Press ENTER if you are sure."
read -r input

git clean -xdf

echo "Building docker image (requires 'sudo')"
sudo docker build -t zooid-cmpst -f docker/Dockerfile .

popd
