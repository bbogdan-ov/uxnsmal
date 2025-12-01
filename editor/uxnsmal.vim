" Vim syntax file
" Language: Uxnsmal

" Thanks to https://gitlab.com/tsoding/porth/-/blob/d4095557cca4e76c9031e64537f5ee3a125de975/editor/porth.vim

" Usage:
" - Put this file into `~/.vim/syntax/uxnsmal.vim`
" - Add the next line into your .vimrc:
"   `autocmd BufRead,BufNewFile *.smal set filetype=uxnsmal`

if exists("b:current_syntax")
	finish
endif

set comments=s1:/*,mb:*,ex:*/,://
set commentstring=//\ %s
set iskeyword=a-z,A-Z,_,48-57,45
syntax iskeyword a-z,A-Z,_,48-57,45,46

syntax keyword smalKeyword data loop jump if elif else while return
syntax keyword smalKeyword var const type nextgroup=smalType skipwhite skipempty
syntax match smalIntrinsic "\<\(add\|sub\|mul\|div\|inc\|shift\|and\|or\|xor\|eq\|neq\|gth\|lth\|pop\|swap\|nip\|rot\|dup\|over\|sth\|load\|store\|input\|input2\|output\)\(-\(r\|k\|kr\|rk\)\)\?\>" display
syntax match smalLabel "@\<\k\+\>" display
syntax match smalType "\(\<--\>\|->\)\@!:\@1<!\<\k\+\>" contains=smalBuiltinType display contained
syntax keyword smalBuiltinType byte short fun contained
syntax region smalStackSignature start="(" end=")" contains=smalType contained

syntax keyword smalKeyword fun nextgroup=smalFunction skipwhite skipempty
syntax match smalFunction "\<\k\+\>" nextgroup=smalStackSignature skipwhite skipempty contained display

syntax keyword smalKeyword as nextgroup=smalStackSignature skipwhite skipempty

syntax region smalComment start="//" end="$" oneline display
syntax region smalCommentInline start="/\*" end="\*/"

syntax region smalString start=/"/ skip=/\\./ end=/"/ oneline display contains=smalEscape
syntax match smalChar "'\\\?.'" display contains=smalEscape
syntax match smalEscape "\\[0abtnvfr\\'\"]" contained display

syntax match smalDecNumber "\<[0-9]\+\>\(\s*\*\)\?" display
syntax match smalHexNumber "\<0x[0-9a-fA-F]\+\>\(\s*\*\)\?" display
syntax match smalOctNumber "\<0o[0-7]\+\>\(\s*\*\)\?" display
syntax match smalBinNumber "\<0b[0-1]\+\>\(\s*\*\)\?" display contains=smalOneBit
syntax match smalOneBit "1" contained display

highlight default link smalKeyword Keyword
highlight default link smalType Type
highlight default link smalIntrinsic Function
highlight default link smalLabel Special
highlight default link smalBuiltinType Special
highlight default link smalComment Comment
highlight default link smalCommentInline smalComment
highlight default link smalString String
highlight default link smalChar Character
highlight default link smalEscape SpecialChar
highlight default link smalDecNumber Number
highlight default link smalHexNumber smalDecNumber
highlight default link smalOctNumber smalDecNumber
highlight default link smalBinNumber Comment
highlight default link smalOneBit smalDecNumber

let b:current_syntax = "uxnsmal"
