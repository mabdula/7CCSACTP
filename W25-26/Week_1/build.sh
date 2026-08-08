#!/bin/bash

if [ -z $ISABELLE ]; then
  echo please assign the variable ISABELLE to an Isabelle2021-1 binary
  exit -1
fi

exercise=`basename $PWD`

echo " session ${exercise} in ex = \"Main\" +">ROOT
echo "  description \"Homework 2\"">>ROOT
echo "  options [timeout = 601]">>ROOT
echo "  theories">>ROOT
echo "   ${exercise}">>ROOT
echo "  document_files">>ROOT
echo "    \"root.tex\"">>ROOT

echo "session ${exercise}_sol in sol = \"Main\" +">>ROOT
echo " description \"Solution 2\"">>ROOT
echo " options [timeout = 601]">>ROOT
echo " theories">>ROOT
echo "  \"${exercise}_sol\"">>ROOT
echo " document_files">>ROOT
echo "   \"root.tex\"">>ROOT


${ISABELLE} build -cv -o threads=4 -o document=pdf -o document_output=. -d . $exercise
cp ex/document.pdf ${exercise}.pdf


cp ex/${exercise}.thy sol/${exercise}_sol.thy


sed -i "s/${exercise}/${exercise}_sol/g" sol/${exercise}_sol.thy

sed -i "s/(\*<\*)//g" sol/${exercise}_sol.thy
sed -i "s/(\*>\*)//g" sol/${exercise}_sol.thy
sed -i 's/\\ExerciseSheet/\\vspace\{15ex\}\\ExerciseSheet/g' sol/${exercise}_sol.thy


${ISABELLE} build -cv -o threads=4 -o document=pdf -o document_output=. -d . ${exercise}_sol
cp sol/document.pdf ${exercise}_sol.pdf
