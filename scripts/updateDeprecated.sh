#!/usr/bin/env bash
find ./runtime/examples -type f -exec sed -i '' "s/Pervasives/Stdlib/g" {} \; 2> /dev/null
