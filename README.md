# Verified quicksort: HOL4 → CakeML → x64 (and Pancake)

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

## Pancake version: a pointer-linked list, with contracts

`hol/pancake/qsort.pnk` is the same program in Pancake, CakeML's low-level
language with pointers:

```
$ echo 5 3 9 -1 0 42 3 -17 100 | ./qsort_pan
```

It reads numbers from stdin into a linked list of heap nodes (`[value; next]`),
quicksorts the list in place by relinking nodes, and prints it.

Pancake code cannot be generated from HOL4, so this program is written by
hand. It is specified with contracts, in the style of Ada SPARK, written as
annotation comments. The compiler keeps these as no-op `Annot` nodes:

- `/@ requires: … @/` and `/@ ensures: … @/` on every function;
- `/@ invariant [ghosts]: … @/` and `/@ decreases: … @/` on every loop.

Contract bodies are HOL4 terms. The tooling is:

| File | Role |
|---|---|
| `panLogicScript.sml` | A small program logic, proved sound against Pancake's formal semantics `panSem`: rules for statements, loops (invariant + variant) and calls (`fun_spec`). |
| `panContractLib.sml` | Parses `qsort.pnk` *inside HOL4* with Pancake's own parser, and turns each contract into a proof obligation. |
| `panStepLib.sml` | Symbolic-execution tactics. |
| `panQsortSpecScript.sml` | The contract vocabulary: list segments `lseg`, node disjointness `nodes_ok`, `frame`, and the FFI model `qs_oracle`. |
| `panQsortProgScript.sml` | `qsort_parses`: the parser maps the exact text of `qsort.pnk` to the AST `qsort_decls`. |
| `panQsortProofScript.sml` | The proofs: `read_list_spec`, `qs_spec`, `print_list_spec`, `main_spec`, and the whole-program theorem. |

The headline theorem is `qsort_pan_semantics` (in `panQsortProofTheory`),
checked with no `cheat`s:

```
⊢ s.code = FEMPTY ∧ s.ffi.oracle = qs_oracle ∧ s.ffi.ffi_state = input ∧ ¬s.be ∧
  heap_ok s.base_addr s.top_addr s.memaddrs (LENGTH input) ⇒
  ∃ys. SORTED $<= ys ∧ PERM ys input ∧
       semantics_decls s «main» qsort_decls =
         Terminate Success (s.ffi.io_events ++ MAP (get_ev ∘ SOME) input ++
                            [get_ev NONE] ++ MAP put_ev ys)
```

In words: started at `main`, the program terminates successfully. It reads
every number of the input, then reads end of input, then prints a sorted
permutation of the numbers.

This is the semantics that the Pancake compiler's correctness theorem
(`pan_to_targetProof`) is stated about. The binary is compiled by the `cake`
binary, as in Tier 1.

What this theorem assumes, beyond the trusted base above:

- **The `cake` binary's Pancake compiler** corresponds to the verified one.
  `qsort_parses` ties the AST in the logic to the `.pnk` text, via the same
  parser the compiler uses.
- **FFI glue:** `qsort_ffi.c` implements `qs_oracle` (about 70 lines of C).
- **Heap size:** `heap_ok` says the heap has room for the input (16 bytes per
  number, plus a 16-byte buffer). With the default 512 MB heap that is about
  33 million numbers. With more input the program stops early through its
  out-of-memory check, a case the theorem does not cover.
- **Stack and other resource limits:** as for any CakeML or Pancake program,
  the compiler theorem allows the binary to stop early if it runs out. The
  recursion depth of `qs` is that of quicksort: linear in the worst case,
  for example on already-sorted input.
- **Numbers** are 64-bit words, compared as signed integers (`$<=` on words is
  signed). The CakeML version uses unbounded integers.

## Continuous integration

`.github/workflows/verify.yml` runs on every push and pull request.

1. **Toolchain image.** The `ci` stage of `docker/Dockerfile` holds Poly/ML,
   HOL4, CakeML, the `cake` compiler, and every CakeML theory this project
   depends on, already built (via `docker/warmup/`).
   - It is pushed to `ghcr.io/<owner>/verified-qsort-toolchain`, tagged by a
     hash of `docker/`.
   - It is only rebuilt when `docker/` changes. That first build takes a few
     hours on a GitHub-hosted runner, within the 6-hour job limit.
2. **Verify.** Inside that image, `ci/check.sh`:
   - re-checks every proof in `hol/` and `hol/pancake/`;
   - fails if any theorem depends on a `cheat` or other oracle
     (`ci/no_cheats.sml`);
   - compiles both programs with the verified `cake` compiler and tests the
     binaries against `sort -n`.

   The binaries and `.S` files are uploaded as a build artifact. This step
   takes about 3 minutes.

To run the same checks locally in a container built from the `ci` stage:
`bash ci/check.sh .` from the repository root.

The Tier 2 machine-code theorem (`hol/compile/`) is not part of CI, because
it needs CakeML's full compiler proofs (many hours).

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

Outputs:

- `hol/build/`: `qsort.S` and the `qsort` executable (Linux x64);
- `hol/pancake/build/`: `qsort_pan.S` and the `qsort_pan` executable.

Run them with:

```
docker exec vqs-dev /opt/cakeml/examples/verified_qsort/build/qsort 5 3 -1 42 0
echo 5 3 -1 42 0 | docker exec -i vqs-dev /opt/cakeml/examples/verified_qsort/pancake/build/qsort_pan
```

In Git Bash (MINGW), prefix the command with `MSYS_NO_PATHCONV=1`, or start
the path with `//opt/...`. Otherwise Git Bash rewrites `/opt/...` into a
Windows path.
