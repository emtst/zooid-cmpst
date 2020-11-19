#!/usr/bin/env bash

unameOut="$(uname -s)"

case "${unameOut}" in
    Linux*) find ./runtime/examples -type f -exec sed -i'' "s/Pervasives/Stdlib/g" {} \; 2> /dev/null ;;
    Darwin*) find ./runtime/examples -type f -exec sed -i '' "s/Pervasives/Stdlib/g" {} \; 2> /dev/null ;;
    *) echo "UNKNOWN OPERATING SYSTEM"
esac
