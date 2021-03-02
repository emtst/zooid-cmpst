#!/bin/bash

if [ ! -d "scripts" ]; then
    cd ..
fi

if [ -d "runtime" ]; then

echo "Running the seller" &&

cd runtime &&

dune exec -- seller &

sleep 1 &&
echo "Running buyer A" &&
cd runtime &&

echo 30 | dune exec -- buyerA &

sleep 2 &&

echo "Running buyer B" &&
cd runtime &&

dune exec -- buyerB

fi
