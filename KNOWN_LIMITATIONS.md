# Verification boundary

- The formal theorem concerns the approved finite game model. It does not prove
  that a real agent or environment has been modeled faithfully.
- The JSON adapter, Lean compiler, standard JSON parser, runtime, I/O and operating
  system are tested parts of the executable boundary, not separately verified
  components. The adapter calls the proved `Reachability.solve` directly.
- The construction makes one promotion per recursive step and is intended as a
  small, inspectable implementation. No performance target or arbitrary-input
  resource guarantee was approved. Memory and time remain finite host resources.
- The automatic agent runner stalled without a session or code changes on the
  preparation host. The implementation and manual audit were performed directly;
  no autonomous factory audit convergence is claimed.
- Automatic shell Git pushes from the preparation host lack credentials. The
  connected GitHub integration publishes the checked source tree instead.
- The original protected README and setup notes describe the initial draft.
  `APPROVAL.json` records its approval; `EVIDENCE.md` records the implemented result.
