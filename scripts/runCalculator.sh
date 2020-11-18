#!/bin/bash

if [ ! -d "scripts" ]; then
    cd ..
fi

if [ -d "runtime" ]; then

cd runtime &&

echo "Running the calculator server" &&

dune exec -- calcsvr &

sleep 1 &&
echo "Running the calculator client" &&

dune exec -- calcc

fi
