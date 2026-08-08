rm presentation.aux presentation.snm presentation.toc
pdflatex presentation.tex
grep -v "setbeameroption{show notes on second screen}"  presentation.tex > /tmp/presentation_no_notes.tex
pdflatex /tmp/presentation_no_notes.tex

