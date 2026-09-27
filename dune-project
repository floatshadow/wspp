(lang dune 3.0)

(name wspp)

(generate_opam_files true)

(package
 (name wspp)
 (synopsis "Weighted symbolic packet programs (wSPPs) over arbitrary star semirings")
 (depends
  (ocaml (>= 5.0))
  core
  (core_unix :with-test)
  ppx_jane
  pprint
  zarith))
