# Setup boundary

- Target repository: rfreel/fftest, public, main.
- Factory source pinned in ff.lock.json. The controller configuration is copied
  outside the target clone and cannot be widened by candidate commits.
- Lean toolchain: 4.34.0; only Std is imported, no Mathlib download needed.
- Provider: signed-in Codex CLI default model. No credentials are committed.
- Application FFI: forbidden. Allowed foundational axioms: propext,
  Classical.choice, Quot.sound.
- Draft approval: manual, required before implementation. Setup does not
  silently approve the specification on the user's behalf.
- One agent at a time; fixed retry/audit limits; no performance-search phase.
- No persistent server or paid compute is provisioned by this repository.
  A controller started in a transient session is only live while that host lives.

The independent oracle enumerates agent strategies and detects reachable
non-goal cycles. The candidate solver may use attractor iteration, so the oracle
uses a different mechanism. The certificate validator checks local moves,
strict rank descent and complement closure, independently of oracle answers.

The preparation host's /proc/<pid>/exe lookup is unavailable even for its own
process, while /proc/self/exe works. Local Lean validation therefore uses an
external compatibility shim that retries only that same-process executable-path
lookup using /proc/self/exe. It changes no Lean code, proof terms or axioms and
is not part of the target, the FFI allowlist, or the normal installation. CI
runs on an ordinary Linux host without this shim. This host-specific condition
must not be confused with a completed independent CI run.
