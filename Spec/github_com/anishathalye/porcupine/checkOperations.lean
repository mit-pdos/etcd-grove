/- Lean-first (no Rocq counterpart).

`checkOperations(model, history, verbose, timeout)` (checker.go): `fillDefault`, the model's
`Partition` (`noPartition`: the one partition `[history]`), `makeEntries` per partition,
`checkParallel`. On a linearizable history it never answers `Illegal`, and with no timeout
(`timeout <= 0`) it answers `Ok`. `context.isClosedchanInit` is what `checkParallel`'s
`context.WithCancel(context.Background())` needs.
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
abbrev checkOperations.spec : Prop :=
  ∀ (σ : Type) (S : ModelSpec GF σ) (m : Model) (sl : GoSlice) (ops : List Operation)
    (dq : DFrac) (verbose : Bool) (dur : w64),
  HistOk ops →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗
      context.isClosedchanInit ∗ isModel S m ∗ sl ↦*{dq} ops ∗ opsIoOk S ops }}
    (App (App (App (App (Val (@! github_com.anishathalye.porcupine.checkOperations))
      (Val #m)) (Val #sl)) (Val #verbose)) (Val #dur))
  {{ (r : GoString) (info : LinearizationInfo), RET (PairV #r #info);
      ⌜Linearizable S.M (histOf ops) →
        r ≠ go!"Illegal" ∧ (sint.Z dur ≤ 0 → r = go!"Ok")⌝ }}

end spec

end porcupine
end EtcdGrove
end Perennial
