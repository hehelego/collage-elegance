# verified merge sort in dafny

- evaluation: `readability-bad`, `trustworth-bad`
- development environment: `dafny`. `vscode dafny plugin`, `dafny v3.7.0`
- files: `msort.dfy`

## readability issue

The code is bearly readable.

It is good to leave the contracts and key invariants in the code, as they provide guidance to understand the expected behavior and the correctness of the implementation.
However proof steps should definitely be put somewhere else instead of mingled with the code.

The question is how to display/visualize code with annotated proof in a user-friendly way. We need to (1) reducing distraction (2) enable quick lookup/navigation jumping back and forth between implementation and proofs.
One possible solution is to have a dedicated editor that splits the text area vertically, showing the contract on LHS and the proofs on RHS.

## reliability of dafny

Dafny is not reliable at all. I tried to verify the program using dafny v4.4 and v3.11 but failed.

## automation v.s. cost of verification

The cost of one verification run is high.
I have to wait for nearly one minute on my laptop after a fresh reload (without caching).

I think it is desirable to ship proofs/certificates generate by the dafny pipeline (dafny - boggie - z3) and whoever want to use the code only need to run a efficient proof check.

## ghost states

I find ghost states really neat. They help to write clean and understandable code.

- They help to express invariants that are hard to encode only using the program states.
- They can aid the programmer as well as the verifer to understand the invariant reestablishment.

