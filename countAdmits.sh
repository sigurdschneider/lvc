#!/bin/bash

grep -c "[Aa]dmit" $(find . -type f -iname '*.v') | sed '/:0$/d'
