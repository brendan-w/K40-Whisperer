#!/bin/bash

# k40_whisperer is written with CRLF line endings, which makes linux barf when it attempts to read
# the shebang line. This can be fixed with a simple `dos2unix`, but that would make upgrading versions
# a nightmare. Keeping a wrapper runscript with unix line endings instead.
python2 ./k40_whisperer.py