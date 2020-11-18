#!/bin/bash

if [ ! -d "scripts" ]; then
    cd ..
fi

if [ -d "runtime" ]; then

echo "Running the PingPong server" &&
cd runtime &&
dune exec -- ppsvr &

sleep 1 &&
echo "Running Client 2" &&
cd runtime &&
dune exec -- ppc2

fi
