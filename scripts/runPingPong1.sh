#!/bin/bash

if [ ! -d "scripts" ]; then
    cd ..
fi

if [ -d "runtime" ]; then

echo "Warning: this is a non-terminating protocol, stop it with Ctrl+C"
read -p "Press [Enter] key to start..."

echo "Running the PingPong server" &&
cd runtime &&
dune exec -- ppsvr &

sleep 1 &&
echo "Running Client 1" &&
cd runtime &&
dune exec -- ppc1

fi
