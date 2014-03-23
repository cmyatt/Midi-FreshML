output='typechecker'
build='./_build'
bin='./bin'

while test $# -gt 0; do
  case "$1" in
    -h|--help)
      echo './make [options]'
      echo " "
      echo "  Compiles Midi-FreshML implementation."
      echo " "
      echo "options:"
      echo "  -t, --typechecker   compile typechecker [default]"
      echo "  -i, --interpreter   compile interpreter test"
      echo "  -c                  clean the _build/ and bin/ directories"
      echo "  -h, --help          show this help message"
      exit 0
      ;;
    -c)
      shift
      ./clean
      ;;
    -t|--typechecker)
      shift
      output='typechecker'
      ;;
    -i|--interpreter)
      shift
      output='int-test'
      ;;
     *)
     shift
     echo "Invalid option. Type -h for help"
     exit 1
     ;;
  esac
done

function compile {
  echo 'Running ocamlc...'
  if [ $output = 'typechecker' ]; then
    # Run lex and yacc to generate all .ml files
    echo 'Running ocamllex...'
    ocamllex $1/*.mll
    echo 'Running ocamlyacc...'
    ocamlyacc $1/*.mly

    ocamlc -c $1/abSyn.ml $1/parser.mli 2>> $build/log.txt
    ocamlc -c $1/abSyn.ml $1/parser.ml 2>> $build/log.txt
    ocamlc -c -annot $1/abSyn.ml $1/parser.ml $1/lexer.ml $1/tyCheck.ml $1/run_parser.ml 2>> $build/log.txt
  else
    if [ $output = 'int-test' ]; then
      ocamlc -c -annot -I $1 $1/abSyn.ml $1/interpreter.ml $1/tests/interpTest.ml 2>> $build/log.txt
    fi
  fi
}

function move {
  # Move all generated files from dir ($1) to $build
  echo "Moving output files to $build/"
  echo 'mv:' >> $build/log.txt
  mv $1/*.cm* $build/ 2>> $build/log.txt
  mv $1/*.output $build/ 2>> $build/log.txt
  mv $1/*.annot $build/ 2>> $build/log.txt
  mv $1/tests/*.cm* $build/ 2>> $build/log.txt
  mv $1/tests/*.output* $build/ 2>> $build/log.txt
  mv $1/tests/*.annot* $build/ 2>> $build/log.txt
}

function link {
  # Link all bytecode files into single executable
  echo 'Linking...'
  if [ $output = 'typechecker' ]; then
    ocamlc $build/abSyn.cmo $build/parser.cmo $build/lexer.cmo $build/tyCheck.cmo $build/run_parser.cmo -o $bin/$1
  else
    if [ $output = 'int-test' ]; then
      ocamlc $build/abSyn.cmo $build/interpreter.cmo $build/interpTest.cmo -o $bin/$1
    fi
  fi
}

# Clean log file
echo `> $build/log.txt` > /dev/null

# Compile individual modules
compile '.'
move '.'
link $output
rm lexer.ml parser.ml parser.mli 2> /dev/null

