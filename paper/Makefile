paper.pdf: paper.tex Makefile biblio.bib
	pdflatex paper
	bibtex paper
	pdflatex paper
	pdflatex paper

clean:
	rm -f paper.aux paper.bbl paper.log paper.pdf paper.out paper.blg