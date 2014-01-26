
fml: parser.mly lexer.mll abSyn.ml tyCheck.ml interpreter.ml run_interpreter.ml
	ocamllex lexer.mll; \
	ocamlyacc parser.mly; \
	ocamlc abSyn.ml parser.mli; \
	ocamlfind ocamlc -o fml abSyn.ml parser.ml lexer.ml tyCheck.ml interpreter.ml str.cma run_interpreter.ml

clean:
	-$(RM) *.cmi *.cmo *.cache
