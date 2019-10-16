#!/bin/sh
# $1 - file containing compiled LHA (.spec file)
# $2 - list of variables and CTL property (Vars,Phi)




LHA_ROOT="."
LHA_COMPILE="$LHA_ROOT"/LHACompilation
LHA_VERIFY="$LHA_ROOT"/CTLModelChecking



# Generate thresholds and make convex polyhedral approximation
# Note,  this used the thresholds1 program from chclibs

SPECFILE="$1"
f=${SPECFILE%.spec} # remove .spec extension

thresholds1 -prg "$SPECFILE" -o wut.props
cpascc -prg "$SPECFILE" -cex "traceterm.out" -widenpoints widenpoints -widenout widencns -narrowout narrowcns -withwut bounded -wfunc h79 -o cha.out -threshold "wut.props"

# Make the versions.out file a disjoint partition
$LHA_VERIFY/makeDisjoint "versions.out"

# Generate the PredExists table
$LHA_VERIFY/predExistsTable "$SPECFILE" "versions.out.disjoint" 

# Check the property
$LHA_VERIFY/amc_all "$SPECFILE" "versions.out.disjoint" "$f".predExistsTable "$2" 


