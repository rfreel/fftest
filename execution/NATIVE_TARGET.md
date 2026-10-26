# Native executable refinement: OPEN

The requested all-input refinement theorem is **not proved**. The response
certificates in this workstream must not be presented as that theorem.

## Exact target and mismatch with Basis

The captured deployment artifact is a 122,026,752-byte, dynamically linked,
x86-64 ELF. Its exact SHA-256 is in `checked/report.json`. It includes generated
Lean code, the Lean runtime and an external Linux dynamic-library environment.
A hash identifies bytes; it does not give those bytes a semantics or prove them.

The inspected Basis development is pinned to
`BasisResearch/ship-your-interpreter@fb07094cff916318c34b07494a7d739f1e53989b`.
Its theorem concerns its committed bare-metal RV64 WHILE interpreter under its
Sail machine model and `Loaded` predicate. It does not apply to this x86-64 ELF.
Its README also excludes parsing and says the ELF-to-witness and boot-trace
bindings were checked by external scripts. Those scripts are absent upstream.

## Closed prerequisites

`Proofs/Execution.lean` proves:

1. `checkResult_sound`: any candidate passing finite local checks satisfies
   winning/losing certificates, legal strategies, reachability, avoidance and
   semantic completeness. It does not assume the producer is correct.
2. `solver_accepted`: the original proved solver always passes that checker.
3. `respond_eq_solver`: when the source adapter's lexical and parsing checks
   succeed for a decoded game, it returns the encoding of the proved solver.
   This is source-level and conditional on successful decoding.

`Proofs/NativeExamples.lean` contains eight captured native responses. For each,
Lean checks a certificate theorem and exact equality of every output field to
`solve` for that decoded input. Exact comparisons use `decide +kernel`, with no
native-evaluation trust axiom. These are 16 concrete checked claims, not a
universal binary theorem. Kernel-checkable witness generation is reusable on
other finite batches via `certify.py`.

Python currently binds the input bytes, output bytes, executable hash and Lean
literals. That binding remains outside the kernel. Replacing a binary with one
that behaves correctly only on these eight inputs would still pass this batch.

## Remaining obligations for the requested theorem

A complete theorem must establish observable agreement for every admissible
input, against an actual machine transition relation for the pinned artifact.
It must include explicit and satisfiable initial-state/resource preconditions.
Outstanding work:

- Select and pin an x86-64 instruction semantics and define Linux loading,
  relocations, memory/register initialization, ABI and system-call observations.
- Pin/map the executable's loadable bytes and required shared libraries into
  that semantics, rather than treating source names or a hash as semantics.
- Establish a non-vacuous loaded-state relation for the actual JSONL entrypoint.
- Prove simulations for the generated solver code, runtime, allocation,
  reference counting, integer operations, JSON adapter and stream loop.
- Compose those simulations with `Reachability.acceptance` and the source
  adapter theorem. Prove output/error behavior for each admissible request and
  recovery between requests, with environment and resource assumptions explicit.
- Kernel-check the composed all-input theorem with only approved axioms, then
  attach its artifact identity and build evidence.

Using the Basis machine layer instead would require a separately identified
RV64 executable and a proved language/representation connection for the solver.
That would be a new deployment target, not a proof of the existing ELF.

No `axiom`, `sorry`, presumed compiler-correctness hypothesis, or arbitrary
abstract machine relation has been added to make an unclosed obligation pass.
`python3 execution/status.py --require-whole-binary` deliberately exits 1.

## Reproduce the closed work

```sh
lake build
lake build game-solver
python3 execution/certify.py --requests execution/requests.jsonl --output-dir /tmp/fftest-native-responses
python3 execution/review.py
python3 execution/status.py --require-whole-binary  # expected failure: target remains OPEN
```

Rebuilding may change executable bytes, so a fresh capture has its own image
hash. The checked-in capture is a record of one observed artifact; its witness
proofs can be rechecked without trusting a rebuild to reproduce that hash.
