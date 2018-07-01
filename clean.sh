#!/bin/bash
find /home/papa/verified-exact-real/ -name "*~" -delete
~/.cabal/bin/idris --clean verified-exact-real.ipkg
