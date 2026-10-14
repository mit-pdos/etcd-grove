/- Lean-first (no Rocq counterpart).

`CheckOperations(model, history)` (porcupine.go): `true` on a linearizable history.
-/
module

public import Proof.github_com.anishathalye.porcupine.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

/-- See the file header. -/
abbrev CheckOperations.spec : Prop :=
  ∀ (σ : Type) (S : ModelSpec GF σ) (m : Model) (sl : GoSlice) (ops : List Operation)
    (dq : DFrac),
  HistOk ops →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ isModel S m ∗ sl ↦*{dq} ops ∗ opsIoOk S ops }}
    (App (App (Val (@! github_com.anishathalye.porcupine.CheckOperations))
      (Val #m)) (Val #sl))
  {{ (b : Bool), RET #b; ⌜Linearizable S.M (histOf ops) → b = true⌝ }}

end spec

end porcupine
end EtcdGrove
end Perennial
