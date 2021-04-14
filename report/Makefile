paper.pdf: paper.tex references.bib
	xelatex -synctex=1 -interaction=nonstopmode paper.tex
	biber paper
	xelatex -synctex=1 -interaction=nonstopmode paper.tex
	biber paper
	xelatex -synctex=1 -interaction=nonstopmode paper.tex
	xelatex -synctex=1 -interaction=nonstopmode paper.tex

.PHONY: clean
clean:
	rm -f *.pdf *.bbl *.blg *.aux *.log *.synctex* *.xml *.bcf *.toc *.maf *.mtc*
