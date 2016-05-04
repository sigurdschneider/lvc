#!/bin/bash

NUM=`grep "admit" $(find . -type f | grep -v '\.glob' | grep -v '\.sh') | wc -l`

echo "There are $NUM admits left in the developement" 
