# riscv-lean (copied from ship-your-interpreter)

Copied unchanged from BasisResearch/ship-your-interpreter @ `46b1eb8e`
(`riscv-lean/`):

* `Lean_RV64D/`, `Lean_RV64D_executable/`: the Sail RISC-V model
  (riscv/sail-riscv) generated to Lean. BSD-2-Clause:
  `LICENCE-sail-riscv` is the upstream `LICENCE` these files' headers
  refer to.
* `lean_emulator/`: the Lean emulator from sail-riscv (same licence), with
  ship-your-interpreter's `--trace-all`/`--trace-pcs` traced loop.
* `lean-sail/`: rems-project/lean-sail at `0794631`, patched by
  ship-your-interpreter so unmapped addresses read as zero.

Build once with `lake build` from the repository root (the path
dependency builds here); the emulator binary is
`lean_emulator/.lake/build/bin/lean_riscv_emulator`.
