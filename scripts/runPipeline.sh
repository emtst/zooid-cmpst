#!/bin/bash

if [ ! -d "scripts" ]; then
    cd ..
fi

if [ -d "runtime" ]; then

echo "Warning: this is a non-terminating protocol, stop it with Ctrl+C"
read -p "Press [Enter] key to start..."


echo "Running Alice" &&

cd runtime &&

../scripts/nums.sh | dune exec -- malice > /dev/null &

sleep 1 &&
echo "Running Bob" &&
cd runtime &&

 dune exec -- mbob &

sleep 2  &&

echo "Running Carol" &&
cd runtime &&

dune exec -- mcarol

fi
