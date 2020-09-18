#!/usr/bin/env zsh
find ./runtime/examples -type f -exec sed -i '' "s/Pervasives/Stdlib/g" {} \;
