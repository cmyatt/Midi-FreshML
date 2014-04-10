
fml: parser.mly lexer.mll abSyn.ml tyCheck.ml interpreter.ml run_interpreter.ml
	ocamllex lexer.mll; \
	ocamlyacc parser.mly; \
	ocamlc abSyn.ml parser.mli; \
	ocamlfind ocamlc -o fml -annot abSyn.ml parser.ml lexer.ml tyCheck.ml str.cma interpreter.ml run_interpreter.ml

bench: parser.mly lexer.mll abSyn.ml tyCheck.ml interpreter.ml dpBenchmark.ml
	ocamllex lexer.mll; \
	#ocamlyacc parser.mly;
	ocamlc abSyn.ml parser.mli; \
	#ocamlfind ocamlc -o bin/bench-fml abSyn.ml parser.ml lexer.ml tyCheck.ml str.cma interpreter.ml unix.cma benchmark.cma dpBenchmark.ml
	ocamlfind ocamlopt -noassert -o bin/bench-fml abSyn.ml parser.ml lexer.ml tyCheck.ml str.cmxa interpreter.ml unix.cmxa benchmark.cmxa dpBenchmark.ml

fml-opt: parser.mly lexer.mll abSyn.ml tyCheck.ml interpreter.ml run_interpreter.ml
	ocamllex lexer.mll; \
	ocamlyacc parser.mly; \
	ocamlopt -c abSyn.ml parser.mli; \
	ocamlfind ocamlopt -noassert -o bin/fml-opt abSyn.ml parser.ml lexer.ml tyCheck.ml interpreter.ml str.cmxa run_interpreter.ml

clean:
	-$(RM) fml *.cmi *.cmo *.cache
