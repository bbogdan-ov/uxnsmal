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

TODO:

## Resources

- [UXN reference](https://wiki.xxiivv.com/site/uxntal_reference.html)
- [WebAssembly type-checking](https://binji.github.io/posts/webassembly-type-checking)
- [PORTH](https://gitlab.com/tsoding/porth)
- [PORTH development series](https://youtube.com/playlist?list=PLpM-Dvs8t0VbMZA7wW9aR3EtBqe2kinu4&si=7HwCcRhAZqfkGGC_)
