# Bud Language Reference

Bud is a compiled, dynamically typed language. Bud code is divided into three
concepts: comments, declarations, and expressions.

Each line of code is ended by a carriage return (CR), line feed (LF), or
combination of the two (CRLF).

## Comments

Comments are a way to document extra information about code that may help
someone in the future understand why the code is written the way it is. Bud
currently only supports single-line comments using two slashes (`//`). After two
slashes are encountered, the rest of the line is ignored by the compiler.

```bud
// This is a comment.
pi := 3.14 // Two digits of pi is good enough
```

## Declarations

Currently, Bud only has one declaration: a function declaration. In the future,
modules will be added, and there may be additional declarations added
eventually.

### Functions

A function is a reusable expression that can be passed parameters and return a
value. Functions can call other functions, including themselves.

* A function with no parameters:

    ```bud
    function myfunction()
        "Hello, World!"
    end

    myfunction()
    ```

    This snippet evaluates to `"Hello, World!"`.

* A function with parameters:

    ```bud
    function greet(name)
        "Hello, " + name + "!"
    end

    greet("World")
    ```

Functions can only be defined at the top-level of a source file currently. This
means that nested functions are currently not supported.

## Expressions

Below is a list of every expression Bud supports. The headings are ordered based
on precedence when parsing. That is to say that this code:

```bud
a := 3 * 4 / 2 < 2 + 2 + 3 * 4
```

is equivalent to this code:

```bud
a := (((3 * 4) / 2) < (2 + (3 * 4))
```

### Control Flow

#### If Expression

The If expression allows for one or more statements to be run if an expression
is [truthy](#truthy) or not.

```bud
if <expression>
    // expression was truthy
end
```

For situations where code should be run in either case, the `else` statement can
be used to specify both branches.

```bud
if <expression>
    // expression was truthy
else
    // expression was not truthy
end
```

If expressions generate the value of whichever branch is taken, which allows
them to be used as sub-expressions. This snippet assigns 10 to `a` because input
is longer than 10 characters.

```bud
input := "Hello, World!"
a := (if input.len() > 10
        10
      else
        input.len()
      end)
```

#### Return Expression

The `return` expression allows returning early from a function, preventing any
additional code from running in the currently executing function. If a value is
provided, it will be returned. For example, this code results in 42 not 0:

```bud
function example()
    return 42
    0
end

example()
```

#### Loop Expression

The `loop` expression allows repeating a block of code. Each loop can be given a
label, and that label can be used in `continue` or `break` expressions.

```bud
// An unlabeled loop
loop
  break
end

// An labeled loop
loop #myloop
  break #myloop
end
```

The label must be directly after the `loop` keyword, if it is provided at all.

##### While/Until loops

This style of loop can cause the block to repeat `until` a condition is true or
`while` a condition is true.

```bud
loop until some_condition()
  // code repeats until some_condition() returns a truthy value
  break
end

loop while some_condition()
  // code repeats until some_condition() returns a falsey value.
  break
end
```

##### For loops

This style of loop allows a flexible way of iterating over ranges:

```bud
loop for x := 0 to 5
  // repeats once with x being 0, 1, 2, 3, and 4
end

loop for x := 0 to 5 inclusive
  // repeats once with x being 0, 1, 2, 3, 4, and 5
end

loop for x := 0 to 10 step 2
  // repeats once with x being 0, 2, 4, 6, and 8
end

loop for x := 0 to 10 inclusive step 2
  // repeats once with x being 0, 2, 4, 6, 8, and 10
end

loop for x := 5 down to 0
  // repeats once with x being 5, 4, 3, 2, and 1
end

loop for x := 5 down to 0
  // repeats once with x being 5, 4, 3, 2, 1, and 0
end
```

### Assignment Expression

The assignment expression defines a new variable in the local function's scope.

```bud
<variable-name> := <expression>
```

For example, this snippet evaluates to 42:

```bud
a := 13
b := 4
a * b
```

Assignment expressions propogate the value being assigned. For example, this
code initializes both `a` and `b` to 42:

```bud
a := b := 42
```

### Logical Binary Expressions

Logical binary expressions use the `and`, `or`, and `xor` keywords. These
operators perform boolean logic.

```bud
// And operator
true and true // produces true
true and false // produces false
false and true // produces false
false and false // produces false

// Or operator
true or true // produces true
true or false // produces true
false or true // produces true
false or false // produces false

// Xor operator
true xor true // produces false
true xor false // produces true
false xor true // produces true
false xor false // produces false
```

The `and` and `or` operators support short circuting. Once the result is known,
the remaining operands are not evaluated. In this snippet, the function
`not_called()` will not be called because the result of the operation is already
known without invoking the function:

```bud
function not_called()
end

true or not_called()
false and not_called()
```

### Bitwise Binary Expressions

Bitwise binary expresssions use the `&`, `|`, `^`, `<<` and `>>` symbols that
many other
programming languages use.

* `&` **Bitwise And**: Each bit of the resulting integer will be set only if the
  bit is set in both the left and right operands.
* `|` **Bitwise Or**: Each bit of the resulting integer will be set if the bit
  is set in either the left or right operands.
* `^` **Bitwise Xor**: Each bit of the resulting integer will be set if the bit
  is set in either the left or right operand, but not both.
* `<<` **Bitwise Shift Left**: The left hand integer's bits are shifted left,
  leaving 0s behind. If the right hand side is larger than the number of bits in
  an integer, the result will be 0.
* `>>` **Bitwise Shift Right**: The left hand integer's bits are shifted right,
  leaving 0s behind. If the right hand side is larger than the number of bits in
  an integer, the result will be 0.

```bud
// Bitwise and
1 & 3 // produces 1
// Bitwise or
1 | 3 // produces 3
// Bitwise xor
1 ^ 3 // produces 2
// Bitwise Shift Left
1 << 3 // produces 8
// Bitwise Shift Right
8 >> 3 // produces 1
```

### Comparison Expression

Comparison expressions generate `true` if the condition is met or `false` if the
condition is not met. These are commonly used in If expressions or Loop
conditions to control code flow.

Bud supports these comparison operators:

* `a < b`: true if `a` is less than `b`
* `a <= b`: true if `a` is less than or equal to `b`
* `a = b`: true if `a` is equal to `b`
* `a != b`: true if `a` is not equal to `b`
* `a > b`: true if `a` is greater than `b`
* `a >= b`: true if `a` is greater than or equal to `b`

### Addition/Subtraction

Addition and subtraction are evaluated with the same operator precedence,
mimicking the traditional PEMDAS order-of-operations.

#### Addition expression

The addition expression generates a new value by adding two expressions
together. Traditionally, this is used for math, but Bud allows types to
customize this operator's behavior. For example, adding two strings concatenates
the strings instead of attempting to do math on the contents.

This code produces 42:

```bud
40 + 2
```

This code produces `"Hello, World!"`:

```bud
name := "World"
"Hello, " + name + "!"
```

#### Subtraction expression

The subtraction expression generates a new value by subtracting one expression
from another expression. Traditionally, this is used for math, but Bud allows
types to customize this operator's behavior.

This code produces 42:

```bud
44 - 2
```

### Multiplication/Division

Multiplication and division are evaluated with the same operator precedence,
mimicking the traditional PEMDAS order-of-operations.

#### Multiplication expression

The multiplication expression generates a new value by multiplying two
expressions. Traditionally, this is used for math, but Bud allows types to
customize this operator's behavior.

This code produces 42:

```bud
14 * 3
```

#### Division expression

The division expression generates a new value by dividing one expression by
another expression. Traditionally, this is used for math, but Bud allows types
to customize this operator's behavior.

This code produces 42:

```bud
84 / 2
```

### Logical Not expression

The `not` operator is a prefix operator that performs either a logical not on
the operand. The operand's truthyness is determined and the opposite value is
returned.

```bud
not true // produces false
not false // produces true
not 0 // produces true
not 1 // produces false
not 0.0 // produces true
```

### Bitwise Not expression

The `~` operator is a prefix operator that performs either a bitwise not on the
operand. The operand is coerced to an integer, and the result will be the
bitwise not (flipping all bits). If the operand is not able to be coerced to an
integer, a fault will be returned by the virtual machine.

```bud
~0 // produces -1
```

### Terms

A term is the highest precedent path when parsing expressions. Most terms are
literal values, but function calls, variable references, and sub-expressions are
also terms.

#### Identifiers

An identifier is a sequence of characters that represents the name of something.
Identifiers must start with an alphabetic character (Unicode alphabetic
characters are allowed). After the initial alphabetic character, the remaining
characters can be alphabetic, numeric, or underscores (`_`).

When compiling code, the compiler will resolve an identifier to either a
function name or a variable reference. The following example defines a function
`calculate` and two variables `interest` and `principal`. The code calls
`calculate` passing the contents of `interest` and `principal` as the arguments.

```bud
function calculate(a, b)
    a * b
end

interest := 1.05
principal := 500
calculate(interest, principal)
```

#### Booleans

A boolean is a value that is either `true` or `false`.

#### Integers

An integer is a 64-bit signed value capable of representing whole numbers from
-9,223,372,036,854,775,808 (-2^63) to +9,223,372,036,854,775,808 (2^63 - 1).

```bud
one_hundred := 100
balance := -5_000
```

For longer literal values, underscores (`_`) may be used as delimiters. Bud does
not check for consistent usage of delimiters.

#### Real Numbers (Floating Point)

A real number is a 64-bit floating point value.

```bud
pi := 3.141_593
```

For longer literal values, underscores (`_`) may be used as delimiters. Bud does
not check for consistent usage of delimiters.

#### Strings (Text)

A string is a UTF-8 encoded sequence of bytes. A string literal is a sequence of
characters enclosed by double-quotes (`"`).

```bud
"Hello, World!"
```

Some string literals will need to contain special characters or the double-quote
character. To encode these characters, use the backslash (`\`) escape sequence:

* `\t`: Tab character (ascii 9)
* `\n`: New line character (ascii 10)
* `\r`: Carriage return character (ascii 13)
* `\u{xxxx}`: Unicode character with hexadecimal code point `xxxx`

#### Lists (Arrays)

A list is a collection of values. Lists can contain more than one type of data.

```bud
list := [1, 2, 3]
list.get(0)
```

#### Maps (Dictionaries)

A map is a collection of key-value pairs that enables efficient retrieval of
values by their key.

```bud
map := {"a": 1, "b": 2}
map.get("a")
```

#### Sub-expression (Parentheses)

A sub-expression is an expression that is wrapped by parentheses (`()`). Any
expression can be used as a sub-expression. Sub-expressions can be used to make
complex expressions more readable by grouping related operations, but they can
also be used to ensure a specific order of operations.

```bud
14 * 2 + 1 // Results in 29
14 * (2 + 1) // Results in 42
```

### Truthy

Bud allows values to be used as truth statements without explicitly converting
to a boolean value. Conceptually, a value should be truthy if it is non-zero or
non-empty. If the concept does not make sense for a type, it should always be
truthy.

Here are the built-in type's truthy conditions:

| Type     | Truthy Condition                          |
|----------|-------------------------------------------|
| Integer  | Not zero                                  |
| Real     | Not within the epsilon of 0.0 and not NaN |
| List     | Not empty                                 |
| Map      | Not empty                                 |
| String   | Not empty                                 |
| Boolean  | `true`                                    |
| Void     | Never truthy                              |
