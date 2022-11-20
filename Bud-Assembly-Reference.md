# Bud Assembly Language Reference

Bud Assembly is a near perfect mapping to `budvm`'s intermediate representation
(IR). As with most assembly languages, it is very simple. These are the shared
types of arguments instructions may take:

- `LiteralOrSource`: These parameters can be one of:
  - a literal string
  - a literal integer
  - a literal real number (floating point)
  - a literal boolean
  - an argument (`@name`)
  - a variable (`$name`)
- `Destination`: These parameters can be one of:
  - `$`: Store the result on the stack
  - `$$`: Store the result in the return register
  - `$name`: a variable
- `#label`: A unique-per-function code label

## Add

`add <LiteralOrSource> <LiteralOrSource> <Destination>`

Adds the value from the first argument and the value from the second argument
and stores the result in the provided destination.

## Subtract

`sub <LiteralOrSource> <LiteralOrSource> <Destination>`

Subtracts the value from the second argument from the value from the first
argument and stores the result in the provided destination.

## Multiplication

`mul <LiteralOrSource> <LiteralOrSource> <Destination>`

Multiplies the value from the first argument and the value from the second
argument and stores the result in the provided destination.

## Division

`div <LiteralOrSource> <LiteralOrSource> <Destination>`

Divides the value from the first argument by the value from the second argument
and stores the result in the provided destination.

## Logical And

`and <LiteralOrSource> <LiteralOrSource> <Destination>`

Evaluates the truthiness of the first argument and the truthiness of the second
argument, and stores a boolean result of performing a logical and of the two
values.

This operator short circuits and does not evaluate the second argument if the
first argument is falsey.

## Logical Or

`or <LiteralOrSource> <LiteralOrSource> <Destination>`

Evaluates the truthiness of the first argument and the truthiness of the second
argument, and stores a boolean result of performing a logical or of the two
values.

This operator short circuits and does not evaluate the second argument if the
first argument is true.

## Logical Xor

`xor <LiteralOrSource> <LiteralOrSource> <Destination>`

Evaluates the truthiness of the first argument and the truthiness of the second
argument, and stores a boolean result of performing a logical xor of the two
values.

## Bitwise And

`bitand <LiteralOrSource> <LiteralOrSource> <Destination>`

Performs a bitwise and between two integer values. If either argument is not an integer, a fault will be returned from the virtual machine.

## Bitwise Or

`bitor <LiteralOrSource> <LiteralOrSource> <Destination>`

Performs a bitwise or between two integer values. If either argument is not an integer, a fault will be returned from the virtual machine.

## Bitwise Xor

`bitxor <LiteralOrSource> <LiteralOrSource> <Destination>`

Performs a bitwise exclusive-or between two integer values. If either argument is not an integer, a fault will be returned from the virtual machine.

## Bitwise Shift Left

`shl <LiteralOrSource> <LiteralOrSource> <Destination>`

Performs a bitwise shift left of the first argument by the second argument. If either argument is not an integer, a fault will be returned from the virtual machine.

## Bitwise Shift Right

`shr <LiteralOrSource> <LiteralOrSource> <Destination>`

Performs a bitwise shift right of the first argument by the second argument. If either argument is not an integer, a fault will be returned from the virtual machine.

## Not (Logical and Bitwise)

`not <LiteralOrSource> <Destination>`

If the argument is an integer, the bitwise not of the value is stored in the
destination. Otherwise, the argument's truthiness is evaluated and the opposite
boolean value is stored in the destination.

## Conditional Jump

`ifnot <LiteralOrSource> <Label>`

The `ifnot` instruction evaluates the first argument's truthiness. If the argument is not truthy, execution is jumped to the label. If the argument is truthy, execution continues to the next instruction.

## Jump

`jump <Label>`

Jumps execution to the next instruction after the label provided.

## Label

`<Label>`

When a stand-alone label is encountered, the next instruction will be the target
of any jumps to the named label. Labels are only used in intermediate
representation and are replaced with absolute instruction offsets when linked.

## Comparisons

```budasm
<Comparison> <LiteralOrSource> <LiteralOrSource> <Destination>
<Comparison> <LiteralOrSource> <LiteralOrSource> jump <Label>
```

The available comparison instructions are:

- `lt`: True if the first argument is less than the second argument.
- `lte`: True if the first argument is less than or equal to the second argument.
- `gt`: True if the first argument is greater than the second argument.
- `gte`: True if the first argument is greater than or equal to the second argument.
- `eq`: True if the first and second argument are equal.
- `neq`: True if the first and second argument are not equal.

If the form with a `<Destination>` is used, the boolean result of the comparison
will be stored in the destination.

If `jump` is used, the label will be jumped to if the comparison is not true,
acting as a conditional jump. If the comparison is true, execution will continue to the next instruction.

## Push

`push <LiteralOrSource>`

Pushes a value to the stack from another location. This is primarily used when passing arguments to functions.

## Load

`load <LiteralOrSource> <Variable>`

Loads a value and stores it in the specified variable.

## Return

```budasm
return
return <LiteralOrSource>
```

Returns from the currently executing function. If a value is provided, it will
be returned. If no value was stored in the return register, void will be
returned.

## Function Calls

```budasm
call <FunctionName> <ArgCount> <Destination>
recurse <ArgCount> <Destination>
```

Calls a function, allocating `ArgCount` values from the stack as arguments to
the function call. The result of the function will be stored in the provided
destination.

When a function needs to call itself, the `recurse` form can be used.

## Intrinsics

```budasm
intrinsic <InstrinsicName> <ArgCount> <Destination>
```

Calls an intrinsic function, allocating `ArgCount` values from the stack as
arguments to the function call. The result of the function will be stored in the
provided destination.

## Invoke (Instance Functions)

```budasm
invoke <Target> <FunctionName> <ArgCount> <Destination>
```

Calls a function with the provided name on a given value, allocating `ArgCount`
values from the stack as arguments to the function call. The result of the
function will be stored in the provided destination.

If the function can not be found on the value contained in `Target`, a fault
will be returned from the virtual machine.

Target can be a `LiteralOrSource` or the top value on the stack (`$`).

## Defining Functions

`function <FunctionName> <Arguments>*`

When a `function` instruction is encountered, the current function is finished
and a new function is created. All future instructions will be long to this
function, until another `function` instruction is encountered.

Each function has a name and optionally a list of arguments. Here's an example function definition that multiplies the two arguments together:

```budasm
function multiply @a @b
mul @a @b $$
```
