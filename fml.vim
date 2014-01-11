" Vim syntax file
" Language: Midi-FreshML
" Maintainer: Chris Myatt
" Latest Revisoin: 11 January 2014

if exists("b:current_syntax")
  finish
endif

" Keywords
syn keyword fmlKeywords name type where if then else match with let
syn keyword fmlKeywords fun in fresh swap list
syn keyword fmlTypes int real bool string unit
syn match fmlSymbols '|'
syn match fmlSymbols '\['
syn match fmlSymbols '\]'
syn match fmlSymbols ';'
syn match fmlSymbols '_'
syn match fmlSymbols '<<'
syn match fmlSymbols '>>'
syn match fmlSymbols '('
syn match fmlSymbols ')'
syn match fmlSymbols '<'
syn match fmlSymbols '->'
syn match fmlSymbols '>'
syn match fmlSymbols '='
syn match fmlSymbols '{'
syn match fmlSymbols '}'
syn match fmlSymbols '*'

" Literals
syn keyword fmlBoolLiteral true false
syn match fmlIntLiteral '\d\+'
syn match fmlIntLiteral '[~]\d\+'
syn match fmlRealLiteral '\d\+\.\d*'
syn match fmlRealLiteral '[~]\d\+\.\d*'
syn region fmlStringLiteral start="\"" end="\""
syn match fmlCtor '[A-Z][A-Z a-z 0-9 _]*'

" Comments
syn keyword fmlTodo contained TODO FIXME NOTE
syn region fmlComment start="(\*" end="\*)" contains=fmlTodo

" Select highlight colours
let b:current_syntax = "fml"
hi def link fmlKeywords       Statement
hi def link fmlSymbols        Statement
hi def link fmlTypes          PreProc
hi def link fmlBoolLiteral    Constant
hi def link fmlIntLiteral     Constant
hi def link fmlRealLiteral    Constant
hi def link fmlStringLiteral  Constant
hi def link fmlCtor           Constant
hi def link fmlTodo           Todo
hi def link fmlComment        Comment

