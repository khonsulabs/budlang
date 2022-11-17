# Bud: A Safe Dynamic Language Toolchain

![budlang forbids unsafe code](https://img.shields.io/badge/unsafe-forbid-success)
[![Live Build Status](https://img.shields.io/github/workflow/status/khonsulabs/budlang/Tests/main)](https://github.com/khonsulabs/budlang/actions?query=workflow:Tests)
[![HTML Coverage Report for `main` branch](https://khonsulabs.github.io/budlang/coverage/badge.svg)](https://khonsulabs.github.io/budlang/coverage/)

This repository is where the Bud language is implemented. The virtual machine
and related functionality are implemented separately from the language, making
it language agnostic.

## [`budlang`][budlang]

[![crate version](https://img.shields.io/crates/v/budlang.svg)](https://crates.io/crates/budlang) [![Documentation](https://img.shields.io/badge/docs-main-informational)]($docs-base$)

The [`budlang`][budlang] crate is where the Bud language is implemented. It is
built using [`budvm`][budvm].

## [`budlang-cli`][budlang-cli]

[![crate version](https://img.shields.io/crates/v/budlang-cli.svg)](https://crates.io/crates/budlang-cli)

The [`budlang-cli`][budlang-cli] crate provides utilities to execute Bud scripts
from the command line or using a REPL environment.

## [`budvm`][budvm]

[![crate version](https://img.shields.io/crates/v/budvm.svg)](https://crates.io/crates/budvm) [![Documentation](https://img.shields.io/badge/docs-main-informational)]($vm-docs-base$)

The [`budvm`][budvm] crate defines a `#[forbid(unsafe_code)]` virtual machine
implementation.

[budlang]: $$budlang$$
[budvm]: $$budvm$$
[budlang-cli]: $$budlang-cli$$
