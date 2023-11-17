SRC := .
SCT := $(SRC)/sections $(SRC)/appendices

LATEXMK = latexmk -r $(SRC)/latexmkrc
# LATEXMK = latexmk

SOURCES := $(wildcard $(SCT)/*.lhs)
FMTS := $(wildcard $(SRC)/fmts/*.fmt)

# paper.pdf: build $(SRC)/paper.lhs.tex $(SOURCES) $(FMTS) sections/*.lhs
# Wenhao: the above command does not correctly recognise updates in files for me
paper.pdf: build $(SRC)/paper.lhs.tex $(SOURCES) $(FMTS) sections/*.lhs appendices/*.lhs macros.tex
	cd $(SRC) && lhs2TeX --poly "paper.lhs.tex" > "paper.tex"
	$(LATEXMK) -cd "$(SRC)/paper.tex"
	cp "build/paper.pdf" "paper.pdf"

build:
	mkdir $@

.PHONY: all clean

all: paper.pdf 

clean:
	$(LATEXMK) -C
	rm -f $(SRC)/paper.tex
	rm -f paper.pdf
	rm -rf build
