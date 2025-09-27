TARGET=Core.vo Angle_Div_Nat.vo
FILESFORDEP=`LC_ALL=C ls *.v`
ROCQ=rocq compile
ROCQ_OPT=

all: $(TARGET)

pa_coq.cmo: pa_coq.ml
	ocamlc -I $$(camlp5 -where) -pp camlp5r -c $<

clean:
	rm -f *.glob *.vo *.cm[iox] *.out *.o *.vok *.vos
	rm -f .*.bak .*.aux .*.cache

depend:
	mv .depend .depend.bak
	rocq dep $(FILESFORDEP) | sed -e " s|$$HOME[^ ]*||" | \
	LC_ALL=C sort |	sed -e 's/  *$$//' > .depend

install:
	@echo "Installing TrigoWithoutPi..."
	@mkdir -p $(OPAM_SWITCH_PREFIX)/lib/coq/user-contrib
	@cp -r . $(OPAM_SWITCH_PREFIX)/lib/coq/user-contrib/TrigoWithoutPi

uninstall:
	@echo "Uninstalling TrigoWithoutPi..."
	@rm -rf $(OPAM_SWITCH_PREFIX)/lib/coq/user-contrib/TrigoWithout_pi

local_opam_pin_add:
	opam pin add rocq-trigo-without-pi . -n -y
	opam reinstall rocq-trigo-without-pi -y -w

doc:
	rocq doc -html -utf8 --no-index -d ../gh-pages/ -R . TrigoWithoutPi -s -g -toc *.v

doc_links:
	find ../gh-pages/. -name '*.html' -exec sed -i 's/\[<span class="id" title="var">TrigoWithoutPi\.\([a-zA-Z_]*\)<\/span>\]/<a class="idref" href="TrigoWithoutPi.\1.html">TrigoWithoutPi.\1<\/a>/g' {} +

doc_index:
	pandoc index.md -s -c style.css -o ../gh-pages/index.html

.SUFFIXES: .v .vo

%.vo: %.v
	$(ROCQ) $(ROCQ_OPT) -R . TrigoWithoutPi $<

.PHONY: all clean depend install uninstall

include .depend
