# UXNSMAL REFERENCE

> [!IMPORTANT]
> It is assumed that you have been using a computer for some time, know what
> [stack-oriented][] and [concatenative][] programming is and have some knowlege in [UXN][].

[concatenative]: https://en.wikipedia.org/wiki/Concatenative_programming_language
[stack-oriented]: https://en.wikipedia.org/wiki/Stack-oriented_programming
[UXN]: https://100r.co/site/uxn.html

## Symbol names

UXNSMAL symbol (functions, variables, etc...) names can contain `A-Z`, `a-z`, `-`, `_`, `.`:

```uxnsmal
my-name
my_name
MY_COOL.name
```

## Comments

```
// Line comment

/(
Hello
I'm a block comment
)/
```

## Numbers

There are two types of numbers:

- **Bytes**, represents a one byte (8 bit) number. (e.g. `255`)
- **Shorts**, represents a two byte (16 bit) number.\
  Written as a number followed by an asterisk `*`. (e.g. `65535*`)

You can specify radix for both byte and short by prefixing them with these, it
will only affect how numbers look:

- no prefix - decimal
- `0x` - hexadecimal
- `0b` - binary
- `0o` - octal

Because UXN memory is **[big-endian][]** shorts are obviously also stored in
big-endian order. For example `0xabcd*` is stored as `0xab 0xcd` on the stack.
So take it into a count when casting bytes around.

(TODO: there is no type casting yet)

[big-endian]: https://wiki.xxiivv.com/site/uxntal_memory.html

**Example:**

```uxnsmal
10
0xff
0b101010
0o777

1*
65535*
0xffff*

256 // errors because byte exceeded it max value (255)
256* // ok, because it is a short (max value is 65535)
```

## Strings and characters

String and characters are significantly different from eachother:

- **Char literals** are a single ASCII char surrounded by `'`. (e.g. `'a'`, `'\n'`)\
  Using char literal will push byte associated with this ASCII char onto the
  working stack.

- **String literals** are sequences of ASCII chars surrounded by `"`. (e.g. `"hey\0"`)\
  Using string literal will push its pointer (`ptr2 byte`) onto the working
  stack, then contents of this string will be implicitly stored into the output ROM.

Both strings and chars can have these escaped characters:

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

> [!NOTE]
> Unicode chars are not handled neither in strings or chars, so using them may lead to unexpected results.

## Types

> [!IMPORTANT]
> You cannot define custom types yet

There are 5 built-in types:

- `byte` - size is 1 byte
- `short` - 2 bytes
- `ptr <type>` - a 1 byte pointer to `<type>`
- `ptr2 <type>` - a 2 byte pointer to `<type>`
- `funptr <signature>` - a 2 byte pointer to a function with
  a signature equal to `<signature>`

There is a difference between `ptr <type>` and `ptr2 <type>`:

- `ptr <type>` represents an [absolute address byte][] in [zero-page][] memory
- `ptr2 <type>` represents an absolute address short in ROM memory

[absolute address byte]: https://wiki.xxiivv.com/site/uxntal_labels.html
[zero-page]: https://wiki.xxiivv.com/site/uxntal_memory.html

There is no way to use or specify a relative address byte (yet?).

You can do arithmetic operations (`add`, `mul`, `sub`, etc...) on these types:

| A            | B            | Result       |
|--------------|--------------|--------------|
| `byte`       | `byte`       | `byte`       |
| `short`      | `short`      | `short`      |
| `byte`       | `ptr <T>`    | `ptr <T>`    |
| `short`      | `ptr2 <T>`   | `ptr2 <T>`   |
| `short`      | `funptr <T>` | `funptr <T>` |
| `ptr <T>`    | `ptr <T>`    | `ptr <T>`    |
| `ptr2 <T>`   | `ptr2 <T>`   | `ptr2 <T>`   |
| `funptr <T>` | `funptr <T>` | `funptr <T>` |

> [!IMPORTANT]
> There is no generic types in the language at all, so anything that resembles
> generic types is just a compiler magic.

**Example:**

```uxnsmal
var byte my-var
var ptr2 byte my-var
var funptr( byte ptr byte -- short ) my-ptr-to-func

// A pointer to a pointer to a short pointer...
var ptr ptr ptr2 ptr ptr2 short my-var
```

## Functions

There are two types of functions:

- **Procedure function**, can have any number of inputs and any number of
  outputs, just like regular functions in other languages.
- **Vector function**, cannot have inputs or outputs at all and cannot be
  called, but you can take a pointer to a vector function
  (e.g. `&my-vector-func`).\
  Vector functions are used to "subscribe" to certain device events
  (e.g. key press or screen redraw)

> [!NOTE]
> It is like that because UXN has a term of ["vectors"][].
>
> **Vectors** are parts of code that are being executed when a certain event
> has occured (e.g. mouse press) and they are evaluated untill a `BRK` opcode
> and that differs them from **procedure functions**, because procedures are
> evaluated untill `JMP2r` opcode.

["vectors"]: https://wiki.xxiivv.com/site/uxntal_devices.html

**Definition:**

```uxnsmal
// Vector function
fun <name> ( -> ) { ... }

// Procedure function
fun <name> ( [input-types...] -- [output-types...] ) { ... }
```

Any UXNSMAL program must have an entry point defined by `on-reset ( -> )`
vector function:

```uxnsmal
// This is your program entry point
fun on-reset ( -> ) {
	// Some code goes here...
}
```

**Procedure functions** can be called by writing their name (e.g. `my-func`):

```uxnsmal
fun on-reset ( -> ) {
	10 20
	// Calling our procedure will produce 69, yay
	my-plus
}

// Define procedure with 2 inputs and 1 output
fun my-plus ( byte byte -- byte ) {
	pop pop
	34 35 add
}
```

## Variables

**Definition:**

```unxsmal
var <type> <name>
```

**Pointer to a variable** (`&my-var`) pushes `ptr <var-type>` onto the working
stack:

```uxnsmal
var short my-short
var ptr2 byte my-var
var funptr( -- ) my-fun-ptr

fun on-reset ( -> ) {
	&my-short // this is `ptr short`
	&my-var // this is `ptr ptr2 byte`
	&my-fun-ptr // this is `ptr funptr( -- )`
}
```

**Variables** are always zero-initialized.

If you want to set an initial value, you have to explicitly store it using
`store` intrinsic:

```uxnsmal
var byte my-num // zero-initialized

fun on-reset ( -> ) {
	128 &my-num store
}
```

> [!NOTE]
> It is like that because variables are always stored in the
> [zero-page memory][] which cannot be pre-initialized.

[zero-page memory]: https://wiki.xxiivv.com/site/uxntal_memory.html

To load/access value from a **variable** you can either write its name
(e.g. `my-var`) or load it from a pointer (e.g. `&my-var load`):

```uxnsmal
var short my-short

fun on-reset ( -> ) {
	// Store something
	0x1234* &my-short store

	my-short // pushes `short`
	&my-short load // this is the same
}
```

## Data definition/block

**Definition:**

```uxnsmal
data <name> { [data...] }
```

**Data blocks** are used to store any kind of data that can be represented as a
sequence of bytes (e.g. strings, sprites or anything!!!):

```uxnsmal
// Store null-terminated string
data my-cool-string { "hello!" 0xa 0 }
// This is the same
data my-cool-string { "hello!\n\0" }

// 8x8 1bit smiley face sprite
data my-sprite {
	0b01111110
	0b11111111
	0b10111101
	0b10111101
	0b11111111
	0b10111101
	0b11000011
	0b01111110
}
```

Data inside **data blocks** can be represented using **strings**, **chars**,
**numbers** and **paddings** (e.g. `$1024`):

```uxnsmal
data some-data {
	10 20 0xff
	0b1010
	0xab 0xcd
	0xabcd*
	"hello\0" 'a' 'b'

	$1024 // fill 1024 zero bytes
	$0xff // also with prefixes
}
```

**Pointer to a data block** (`&my-data`) ALWAYS pushes `ptr2 byte` onto the
working stack:

```uxnsmal
fun on-reset ( -> ) {
	// This is `ptr2 byte`, no matter
	// what is inside the data block
	&my-data

	// Set `Screen/addr` port
	&my-sprite 0x2c output
}

data my-data { 0xabcd* "uuuh\0" }

// 8x8 1bit smiley face sprite
data my-sprite {
	0b01111110
	0b11111111
	0b10111101
	0b10111101
	0b11111111
	0b10111101
	0b11000011
	0b01111110
}
```

To load/access value from a **data block** you can either write its name
(e.g. `my-data`) or load it from a pointer (e.g. `&my-data load`):

```uxnsmal
fun on-reset ( -> ) {
	my-data // always pushes `byte`
	&my-data load // this is the same
}

data my-data { 0xabcd* "uuuh\0" }
```

Storing a value into a **data block** example:

```uxnsmal

fun on-reset ( -> ) {
	0xff &my-buffer store // set the first byte to 0xff

	// Pointer arithmetic!!!
	0x12
	10* &my-buffer add // set pointer to point to 10th byte in the buffer (0-based)
	store // set the 10th byte to 0x12

	// Storing something beside bytes will error
	0xffff* &my-buffer store
}

// Zero-initialized 64 byte buffer
data my-buffer { $64 }
```

TODO: to be done
