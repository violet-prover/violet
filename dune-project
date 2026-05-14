(lang dune 3.17)

(name violet)

(generate_opam_files true)

(source
 (sourcehut dannypsnl/violet))

(authors "Lîm Tsú-thuàn")

(maintainers "Lîm Tsú-thuàn")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name violet)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends
  ocaml
  dune
  cmdliner
  eio
  eio_main
  violet_kernel
  violet_elab)
 (tags
  (topics "to describe" your project)))

(package
 (name violet_kernel)
 (synopsis "Violet kernel (trusted core)")
 (depends ocaml dune ppx_deriving bwd))

(package
 (name violet_elab)
 (synopsis "Violet elaborator")
 (depends ocaml dune ppx_deriving asai algaeff yuujinchou bwd eio))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
