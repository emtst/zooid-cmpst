#!/bin/bash

if [ ! -d "scripts" ]; then
    cd ..
fi

if [ -d "runtime" ]; then

echo "Running the PingPong server" &&
cd runtime &&
dune exec -- ppsvr &

sleep 1 &&
echo "Running Client 4" &&
cd runtime &&
dune exec -- ppc4

fi
