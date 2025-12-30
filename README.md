<div align="center">
	<img src="./res/logo.png" height="180" style="image-rendering: pixelated;">

# UXNSMAL

</div>

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

- [ ] Features
	- [x] Bindings (binding a name to a stack item)
	- [x] Type casting
	- [x] Custom types
	- [x] Enums
	- [x] Structs
	- [x] Arrays
	- [ ] Other small features...
- [ ] Code optimization. Currently there is no optimizations at all
	- [ ] Dead code elimination
	- [ ] Function inlining
	- [ ] Compile-time evaluation
	- [ ] [Peephole optimization][]
- [ ] [Metaprogramming][]?

[Peephole optimization]: https://en.wikipedia.org/wiki/Peephole_optimization
[Metaprogramming]: https://en.wikipedia.org/wiki/Metaprogramming

## Building

```sh
cargo build --release
cp ./target/release/uxnsmal-cli COMPILER
./COMPILER examples/hello.smal
uxnemu output.rom
```

or

```sh
cargo run --release -- examples/hello.smal
uxnemu output.rom
```

## Examples

"Hello world"

See `examples/print.smal` for more explanation

```uxnsmal
const byte Console-write { 0x18 }

// Print "Hello world!!" to the console
fun on-reset ( -> ) {
	"Hello world!!\n\0" as (*byte)

	while load-k 0 neq {
		load-k Console-write output
		inc
	}

	pop
}
```

## Reference

You can read about the things that the language has [here](./REFERENCE.md)

## Resources

- [UXN reference](https://wiki.xxiivv.com/site/uxntal_reference.html)
- [WebAssembly type-checking](https://binji.github.io/posts/webassembly-type-checking)
- [PORTH](https://gitlab.com/tsoding/porth)
- [PORTH development series](https://youtube.com/playlist?list=PLpM-Dvs8t0VbMZA7wW9aR3EtBqe2kinu4&si=7HwCcRhAZqfkGGC_)
