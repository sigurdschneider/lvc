#!/bin/bash

grep -c "admit" $(find . -type f -iname '*.v') | sed '/:0$/d'
