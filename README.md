# UXNSMAL

> [!WARNING]
> **WIP**
> This language is very experimental, anything can be changed or removed without notice!!!
> So i don't recommend you to use it for your projects untill it is ready. Have fun

UXNSMAL or SMAL is a [concatenative][] [stack-oriented][] and staticaly typed
programming language made for [UXN][] virtual machine

[concatenative]: https://en.wikipedia.org/wiki/Concatenative_programming_language
[stack-oriented]: https://en.wikipedia.org/wiki/Stack-oriented_programming
[UXN]: https://100r.co/site/uxn.html

## TODO

List of features i want to implement

- [ ] Syntax sugar
	- [ ] If-else and While blocks\
	      Currently only blocks and infinite loops are available
	- [ ] Enums
	- [ ] Including/importing any file in any place
- [ ] Better error reporting
	- [ ] Collect as many errors as possible before exiting.\
	      Currently only one error is being reported
	- [ ] Help messages with small examples based on the error context
- [ ] Code optimization\
      Currently there is no optimizations at all
	- [ ] Dead code elimination (code that will never be executed)
	- [ ] Function inlining
	- [ ] Compile-time evaluation
	- [ ] [Peephole optimization][]
- [ ] [Metaprogramming][]?
- [ ] Something else?...

[Peephole optimization]: https://en.wikipedia.org/wiki/Peephole_optimization
[Metaprogramming]: https://en.wikipedia.org/wiki/Metaprogramming

## Building

```sh
cargo build --release
cp ./target/release/uxnsmal-cli ./uxnsmal
./uxnsmal examples/hello.smal
uxnemu output.rom
```

or

```sh
cargo run --release -- examples/hello.smal
uxnemu output.rom
```

## Examples

<!-- TODO: would be cool to add tests for the examples in README.md -->

"Hello world"

See `examples/print` for more explanation

```uxnsmal
const byte Console.write { 0x18 }

// Print "Hello world!!" to the console
fun on-reset ( -> ) {
	"Hello world!!\n\0" -> (str-ptr)

	loop @break {
		load-k 0 eq jumpif @break

		load-k Console.write output
		str-ptr inc
	}

	str-ptr pop
}
```

## Reference

### Literals

#### Numbers

There are two types of numbers in UXNSMAL: `byte` and `short`

Byte is represented simply as a number (e.g. `255`) and store as, let's say, one byte (8 bits).\
Short is represented as a number followed by an asterisk `*` (e.g. `65535*`) and stored as two bytes (16 bits).

You can specify radix of both byte and short by prefixing them with:

- `0x` - hexadecimal
- `0b` - binary
- `0o` - octal
- no prefix - decimal

Example:

```uxnsmal
10 // push byte
0xff // this is also byte
256 // this will error because it exceeded its max value (255)
0b10100011 // also byte

256* // this one is short because of *
0xffff*
```

#### Strings and characters

Strings are sequences of ASCII characters inside `"` (e.g. `"hey\0"`).\
Chars are a single ASCII character inside `'` (e.g. `'a'`, `'\n'`).

String and chars are significantly different from each other:

- Using string literal will push its [absolute realative address short][]
  (`ptr2 byte`) onto the working stack, then this string will be implicitly
  stored in the ROM itself

- Using char literal will push `byte` associated with this ASCII char onto the
  working stack

[absolute realative address short]: https://wiki.xxiivv.com/site/uxntal_labels.html

Both strings and chars can have these escaped chars inside:

- `\0` -> `0` (null character)
- `\a` -> `0x07` (bell)
- `\b` -> `0x08` (backspace)
- `\t` -> `\t` (tab)
- `\n` -> `\n` (new line)
- `\v` -> `0x0B` (vertical tab)
- `\f` -> `0x0C` (form feed)
- `\r` -> `\r` (carriage ret)
- `\\` -> `\` (backslash)
- `\'` -> `'` (single quote)
- `\"` -> `"` (double quotes)

UTF-8/32 is not handled niether for chars or strings, so it can produce crazy results.

Example:

```uxnsmal
"hello\0" // push `ptr2 byte` to this string
load // -> 'h', load the first char of the string

'\n' // -> 0x0a, push "new line" char byte
'ab' // this will error because only one char must be inside `'`
```

## Resources

- [UXN reference](https://wiki.xxiivv.com/site/uxntal_reference.html)
- [WebAssembly type-checking](https://binji.github.io/posts/webassembly-type-checking)
- [PORTH](https://gitlab.com/tsoding/porth)
- [PORTH development series](https://youtube.com/playlist?list=PLpM-Dvs8t0VbMZA7wW9aR3EtBqe2kinu4&si=7HwCcRhAZqfkGGC_)
