/-
The library specs the network package's proofs take as **hypotheses** (notes/dsv-vr.md,
"Hypotheses"): `log/slog` has no model here (translated names only), so `slog.Debug`'s spec is a
theorem argument, stated over `Spec/sloglib.lean`'s package (the lab's `Harness/Proof/log/slog.lean`
model and its `wp_Debug_gen`, `VsrProof/Proof/network/Log.lean`, lab master 915f964, proved it of
the lab's model; here it is the hypothesis `log.slog.Debug.spec`, never an axiom or an instance).

* `log.slog.Debug.spec`: `slog.Debug(msg, args...)` (package-level; only `pkg/network` calls it),
  every argument `argOk` (`Proof/replica/LibHyps.lean`'s, what the replica's logger methods take):
  returns, the arguments' slice back.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.LibHyps

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace log.slog

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : log.slog.Assumptions]

/-- **Hypothesis** (the file header): `slog.Debug(msg, args...)`, its arguments `argOk`. -/
abbrev Debug.spec : Prop :=
  ∀ (msg : GoString) (arg : GoSlice) (xs : List GoInterface) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.log.slog ∗ arg ↦*{dq} xs ∗
      [∗list] x ∈ xs, argOk (GF := GF) x }}
    (App (App (Val (@! log.slog.Debug)) (Val #msg)) (Val #arg))
  {{ RET #(); arg ↦*{dq} xs }}

end spec

end log.slog

end Perennial
