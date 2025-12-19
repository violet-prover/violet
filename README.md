# violet

This project develop violet using nameful context (library Yuujinchou).

- core unification and meta solving: elaboration-zoo
- top level
  - let definition
  - import statement
  - inductive types (view `nat`, `list`, `vec`, `equality` in `example/`)
    - generated eliminator (e.g. `Nat-elim`)
    - (TODO) pattern matching (rely on eliminator)
    - (TODO) strictly positive check
    - (?) sized type for termination checker
  - (TODO) export keyword for top let
- term
  - variable
  - application
  - typed lambda
  - lambda
  - universe
  - hole
  - (?) first class sigma v.s. record based sigma
- (TODO) universe polymorphism: library mugen
