#!/bin/bash

time $(./lvcc.native examples/foo-large.il)
time $(./lvcc.native examples/foo-large2.il)
time $(./lvcc.native examples/foo-large3.il)
