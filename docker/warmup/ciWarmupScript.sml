(*
  Not part of the project: built once while creating the CI toolchain image
  so that every CakeML theory and library the project depends on is already
  compiled in the image.  Keep the Ancestors/Libs in sync with the ones used
  in hol/ and hol/pancake/.
*)
Theory ciWarmup
Ancestors
  basisProg basis_ffi ml_monad_translator cfMonad CommandLineProof TextIOProof
  sorting integer
  panLang panSem panProps panPtreeConversion byte alignment misc words
Libs
  preamble basis ml_monad_translator_interfaceLib cfMonadLib astToSexprLib
  blastLib intLib
