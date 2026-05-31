# Changelog

## Unreleased

## 0.6.0

- allow mixfix operator has associativity (to support reasoning style `x =⟨ p ⟩ y =⟨ q ⟩ z ∎`)
- fix: projection now can be used in application (kernel vapp bug and parser bug)
- fix parser: record field value position now allows user-defined operator (e.g. `{ v = x + y }`), including projection syntax mixin it
- better elaborator errors for unsolvable implicits
- elaborator implicit-lambda insertion
- fix elaborator: when build projection result type, make an error that Kernel reject it

## 0.5.1

- fix deps

## 0.5.0

- fix: handle VIdAbsurd in unifier
- improve error report messages about `<= split` and `<= elim`
- `violet lsp --stdio` runs a language server
- fix file path resolution
- update name of recursive call in context, now one will see `f m'` instead of `ih-m` for definition `f`
- interaction module

## 0.4.0

- universe polymorphic properly
- remove builtin `U` as universe
- fix parser: imports/exports/universe decls are interleaving now

## 0.3.1

- identifier now can use some letter unicode

## 0.3.0

- nested `<= \elim` discharges unreachable cases at every depth
- nested pattern (e.g. `cons a (cons b c)`)
- `\operator` templates accept Unicode characters (e.g. `\x ◁ \y`)
- `\elim` auto-discharges unreachable constructor cases, so the user no longer has to write a clause asserting impossibility
- pretty-printer for kernel terms, used to render diagnostic messages

## 0.2.1

- install script
- project lock file now will record HEAD commit SHA correctly

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
- Working REPL (run `violet load <file>`)
