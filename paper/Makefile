# install python-pygments to use minted package

paper.pdf: paper.tex Makefile biblio.bib
	pdflatex -shell-escape paper
	bibtex paper
	pdflatex -shell-escape paper
	pdflatex -shell-escape paper

clean:
	rm -f paper.aux paper.bbl paper.log paper.pdf paper.out paper.blg