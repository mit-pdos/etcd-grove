/- Lean-first (no Rocq counterpart).

`CheckOperationsTimeout(model, history, timeout)` (porcupine.go): as
`CheckOperationsVerbose`, without the linearization info.

`context.isClosedchanInit` (`context`'s package-init ghost fact: `closedchan` is closed) is what
`checkParallel`'s `context.WithCancel(context.Background())` needs.
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
abbrev CheckOperationsTimeout.spec : Prop :=
  ∀ (σ : Type) (S : ModelSpec GF σ) (m : Model) (sl : GoSlice) (ops : List Operation)
    (dq : DFrac) (dur : w64),
  HistOk ops →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ context.isClosedchanInit ∗
      isModel S m ∗ sl ↦*{dq} ops ∗ opsIoOk S ops }}
    (App (App (App (Val (@! github_com.anishathalye.porcupine.CheckOperationsTimeout))
      (Val #m)) (Val #sl)) (Val #dur))
  {{ (r : GoString), RET #r;
      ⌜Linearizable S.M (histOf ops) →
        r ≠ go!"Illegal" ∧ (sint.Z dur ≤ 0 → r = go!"Ok")⌝ }}

end spec

end porcupine
end EtcdGrove
end Perennial
