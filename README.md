# interpreter

The interpreter of C-like simple language.
Written in Haskell, used BNFC for parsing.

Apart from casual logic, types and arithmetic operations, the interpreter supports static type checking, tuples, arrays, and nested function defintions.

Example programs are placed in correct_examples and incorrect_examples directories.

Compile: just 'make', it'll create TestGrammar.

Run: 'TestGrammar <path to example>'.
