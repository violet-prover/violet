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
  ocamlformat
  ppxlib
  ppx_deriving
  ppx_inline_test
  ppx_expect
  cmdliner
  tsort
  eio
  eio_main
  asai
  algaeff
  yuujinchou
  bwd)
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
