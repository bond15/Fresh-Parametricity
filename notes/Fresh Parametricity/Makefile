#stolen from Steven :) 
fresh-param.pdf:	fresh-param.tex fresh-param.bib
	latexmk -pdf -bibtex fresh-param --synctex=1
clean:
	latexmk -C
diff:
	latexdiff --math-markup=fine --graphics-markup=both --allow-spaces submission.tex fresh-param.tex > diff.tex
	latexmk -pdf diff
