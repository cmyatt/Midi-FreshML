
fml: parser.mly lexer.mll abSyn.ml tyCheck.ml interpreter.ml run_interpreter.ml
	ocamllex lexer.mll; \
	ocamlyacc parser.mly; \
	ocamlc abSyn.ml parser.mli; \
	ocamlfind ocamlc -o fml -annot abSyn.ml parser.ml lexer.ml tyCheck.ml interpreter.ml str.cma run_interpreter.ml

fml-opt: parser.mly lexer.mll abSyn.ml tyCheck.ml interpreter.ml run_interpreter.ml
	ocamllex lexer.mll; \
	ocamlyacc parser.mly; \
	ocamlopt -c abSyn.ml parser.mli; \
	ocamlfind ocamlopt -noassert -o bin/fml-opt abSyn.ml parser.ml lexer.ml tyCheck.ml interpreter.ml str.cmxa run_interpreter.ml

clean:
	-$(RM) fml *.cmi *.cmo *.cache
