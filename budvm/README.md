# Bud Virtual Machine (budvm)

**WARNING: This crate is not anywhere near being ready to publish.**

![budvm forbids unsafe code](https://img.shields.io/badge/unsafe-forbid-success)
[![crate version](https://img.shields.io/crates/v/budvm.svg)](https://crates.io/crates/budvm)
[![Live Build Status](https://img.shields.io/github/workflow/status/khonsulabs/budlang/Tests/main)](https://github.com/khonsulabs/budlang/actions?query=workflow:Tests)
[![HTML Coverage Report for `main` branch](https://khonsulabs.github.io/budlang/coverage/badge.svg)](https://khonsulabs.github.io/budlang/coverage/)
[![Documentation](https://img.shields.io/badge/docs-main-informational)](https://khonsulabs.github.io/budvm/main/budvm)

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
[vm]: $vm$
[fib-vm]: https://github.com/khonsulabs/budlang/blob/main/budvm/examples/fib-vm.rs
[fib-ir]: https://github.com/khonsulabs/budlang/blob/main/budvm/examples/fib-ir.rs

## Open-source Licenses

This project, like all projects from [Khonsu Labs](https://khonsulabs.com/), are
open-source. This repository is available under the [MIT License](./LICENSE-MIT)
or the [Apache License 2.0](./LICENSE-APACHE).

To learn more about contributing, please see [CONTRIBUTING.md](./CONTRIBUTING.md).
