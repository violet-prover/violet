(lang dune 3.15)

(name gamma)

(generate_opam_files true)

(source
 (github dannypsnl/gamma))

(authors "Lin")

(maintainers "Lin")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name gamma)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends
    ocaml
    dune
    ocamlformat
    ppxlib
    ppx_deriving
    cmdliner
    eio
    eio_main
    asai
    algaeff
    yuujinchou
    bwd)
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
