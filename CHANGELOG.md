# Changelog

## Unreleased

## 0.2.0

- Reworked the template variable syntax inside `\operator` definitions:

  ```
  \operator "\x + \y" => add x y
    \associativity: \left
  ```

## 0.1.0

- Inductive types generate the corresponding eliminator, including both its type and its computation rules.
- Redesigned the namespace handling for constructors: constructors live under their type's namespace by default and can be brought into scope on demand or through surface syntax. For example, by default we use `Nat/zero` and `Nat/suc` to access constructors of `Nat`.
- Added `\operator` so developers can define their own expression syntax, e.g.

  ```
  \operator "~x + ~y" => add x y
    \associativity: \left
  ```

- Modules are now private by default; introduced the `\export` form to expose definitions.
- Introduced the project concept: dependencies are managed through `info.vt`. See https://github.com/violet-prover/std for an example.
- Added built-in records to the kernel.
