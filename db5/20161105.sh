#!/usr/bin/env bash

if [ "$#" -eq 1 ]; then
    python3 20161105_2.py  $@ # recovery
fi

if [ "$#" -eq 2 ]; then
    python3 20161105_1.py  $@ # logging
fi
