default: bib
	pdflatex docs
	bibtex docs
	pdflatex docs
	pdflatex docs

bib:
	cat bibliography/*.bib > bibliography.bib

clean:
	rm -vf *.aux *.log *.toc *.bbl *.blg sections/*.aux
