#!/bin/bash

if [ -z $ISABELLE ]; then
  echo please assign the variable ISABELLE to an Isabelle2021-1 binary
  exit -1
fi

exercise=`basename $PWD`
exercise=${exercise/-/}
exercise=${exercise/[0-9]/}

echo " session ${exercise} in ex = \"Main\" +">ROOT
echo "  description \"Homework 2\"">>ROOT
echo "  options [timeout = 601]">>ROOT
echo "  theories">>ROOT
echo "   ${exercise}">>ROOT
echo "  document_files">>ROOT
echo "    \"root.tex\"">>ROOT

${ISABELLE} build -o quick_and_dirty -cv -o threads=4 -o document=pdf -o document_output=. -d . $exercise
cp ex/document.pdf ${exercise}.pdf
