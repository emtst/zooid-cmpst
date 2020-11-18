#!/bin/bash

if [ ! -d "scripts" ]; then
    cd ..
fi

if [ -d "scripts" ]; then

make && ./scripts/updateDeprecated.sh && cd runtime && dune build

fi
