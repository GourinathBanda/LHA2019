#!/bin/sh
# $1 - file containing LHA specification
# $2 - CTL property



LHA_ROOT="."
LHA_COMPILE="$LHA_ROOT"/LHACompilation
LHA_VERIFY="$LHA_ROOT"/CTLModelChecking



LHAFILE=`pwd`/"$1"


# First generate the .spec file from the LHA specification

cd "$LHA_COMPILE"
make --always-make -f makefileWithNoEvents_NewDriver INPUTLHAFILE="$LHAFILE"
cd ..

# Now remove all line

# Generate thresholds and make convex polyhedral approximation
# Note,  this used the thresholds1 program from chclibs

SPECFILE="$LHAFILE"New.spec 

# Remove first two lines which are junk

sed -i '' '1,2d' "$SPECFILE"

