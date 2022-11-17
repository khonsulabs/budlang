A safe, dynamically-typed virtual machine

This crate provides a stack-based virtual machine that can be used to implement
dynamically typed languages. [Bud][budlang] is the language that this crate was
originally designed for.

## Safety

This crate uses `#[forbid(unsafe_code)]` and has no external dependencies. The
only unsafe code blocks are located within Rust's standard library. Any panics
encountered should be considered a bug and reported.

## How to use

[Bud][budlang] can be used as a complete example of how to build a language and
REPL with this crate. There are two simpler examples demonstrating a recursive
fibonacci number function:

* [fib-vm][fib-vm]: Implemented using virtual machine instructions.
* [fib-ir][fib-ir]: Implemented using intermediate representation (IR) with
      conveniences like variable management and labels.

In all cases, the [`VirtualMachine`][vm] type is used to execute instructions.
Its documentation goes into detail how it operates.

[budlang]: https://github.com/khonsulabs/budlang
[vm]: $$vm$$
[fib-vm]: https://github.com/khonsulabs/budlang/blob/main/budvm/examples/fib-vm.rs
[fib-ir]: https://github.com/khonsulabs/budlang/blob/main/budvm/examples/fib-ir.rs
