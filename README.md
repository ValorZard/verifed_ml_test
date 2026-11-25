# Verified quicksort: HOL4 → CakeML → x64

A command-line program that sorts integers, where **all the code is generated
from HOL4 definitions** and its behaviour is **proved** in HOL4.

```
$ ./qsort 5 3 9 -1 0 42 3 -17 100
-17
-1
0
3
3
5
9
42
100
```

Nothing is written in CakeML (or C) by hand. The pipeline is:

1. **HOL4 functions** (`hol/qsortScript.sml`): `qsort` on integer lists, plus
   proofs that its result is sorted, a permutation of its input, and unique
   (so it equals HOL's library `QSORT`).
2. **Proof-producing translation** (`hol/qsortProgScript.sml`):
   - CakeML's translator turns the pure HOL functions into CakeML code, with
     theorems that the code computes exactly those functions. These functions
     are `qsort`, argument parsing (`parse_ints`) and output formatting
     (`show_ints`).
   - `main` is a HOL4 function in a state/IO monad (read the command line,
     print the result). The monadic translator turns it into CakeML.
   - `prove_sem_thm` adds the top-level call, defines the whole program
     `qsort_prog`, and derives its semantics.
3. **Compilation**, by one of two routes:
   - **Tier 1:** `qsort_prog` is exported as an S-expression (`hol/qsort.sexp`)
     and compiled by the release's verified, bootstrapped `cake` compiler
     binary (CakeML v3671).
   - **Tier 2:** `hol/compile/` compiles `qsort_prog` *inside HOL4*, writing
     `qsort.S`, and composes the result with CakeML's compiler correctness
     theorem. That gives a theorem about the x64 machine code itself.

## What is proved

`qsort_prog_correct` (in `qsortProgTheory`) is the headline theorem. It is
checked with no `cheat`s or oracles.

```
⊢ hasFreeFD fs ∧ wfcl cl ∧ wfFS fs ∧ STD_streams fs ⇒
  sem_satisfies
    (semantics_dec_list (init_state (basis_ffi ext cl fs)) init_env qsort_prog)
    (λbehaviour.
       ∃io_events fs'.
         behaviour = Terminate Success io_events ∧
         extract_fs ext (cl,fs) io_events = SOME fs' ∧
         case parse_ints (TL cl) of
           NONE => fs' = add_stderr fs usage_msg
         | SOME ns =>
             ∃ys. SORTED $<= ys ∧ PERM ys ns ∧ fs' = add_stdout fs (show_ints ys))
```

In words: for any command line and well-formed initial file system, every
possible behaviour of the CakeML program terminates successfully. If every
argument is an integer, the only effect is that a sorted permutation of the
arguments is written to stdout, one per line. Otherwise a usage message is
written to stderr.

Supporting theorems in `qsortTheory`: `qsort_SORTED`, `qsort_PERM`,
`qsort_unique`, `qsort_eq_QSORT`.

Tier 2 has **not been built yet**. It was stopped partway through building
CakeML's compiler proofs. When built, it adds `qsort_compiled_thm` (in
`qsortProofTheory`). That theorem says the x64 machine code in
`hol/compile/qsort.S`, when installed in a machine state, behaves as above, or
stops early with an out-of-memory exit.

## Trusted base

- **Kernel and models:** the HOL4 logical kernel, the CakeML semantics, and
  the x64 ISA model.
- **I/O glue:** CakeML's standard `basis_ffi.c`, about 300 lines of C
  implementing the system calls as modelled by the basis library's file
  system model.
- **Tier 1 only:** the bootstrapped compiler binary is verified by the CakeML
  project's own bootstrapping theorem. Also trusted: the S-expression export
  (`astToSexprLib`, a printer) and the `cake` binary's correspondence to that
  theorem.
- **Tier 2 only:** neither of the Tier 1 items is needed, because compilation
  happens inside the logic. What remains trusted is the assembler/linker
  turning `qsort.S` bytes into an executable (the `.S` is just a byte array).

Input is passed as command-line arguments. That is what the monadic
translator's I/O interface supports, and it keeps `main` HOL-generated.

## Building

Requires Docker. Everything runs in a container built from `docker/Dockerfile`:

- Poly/ML 5.9.2.
- HOL4 at the commit the CakeML v3671 release was built with.
- CakeML sources and the v3671 compiler binary.

```
./build.sh          # Tier 1 (first run: ~1.5 h, mostly building CakeML's basis library)
./build.sh tier2    # + in-logic compilation and machine-code theorem (several hours; not yet run)
```

The `hol/` directory is mounted inside the container's CakeML tree at
`/opt/cakeml/examples/verified_qsort`, so Holmake resolves CakeML theories
normally. Re-checking only the quicksort theories takes about a minute.

Outputs (in `hol/build/`): `qsort.S` and the `qsort` executable (Linux x64).
Run it with:

```
docker exec vqs-dev /opt/cakeml/examples/verified_qsort/build/qsort 5 3 -1 42 0
```

In Git Bash (MINGW), prefix the command with `MSYS_NO_PATHCONV=1`, or start
the path with `//opt/...`. Otherwise Git Bash rewrites `/opt/...` into a
Windows path.
