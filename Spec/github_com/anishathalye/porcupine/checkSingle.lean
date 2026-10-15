/- Lean-first (no Rocq counterpart).

`checkSingle(ctx, model, history, computePartial)` (checker.go): the search of one
partition. Given the entries `es` of a history `h` (`EntriesFor`, what `makeEntries` returns)
and a filled model, it returns `true`, or the history is not linearizable, or the context is
done (its Done proposition holds: `isContext`'s `Err()`). Completeness: it never answers
`false` on a linearizable history unless cancelled.
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
abbrev checkSingle.spec : Prop :=
  ∀ (σ : Type) (S : ModelSpec GF σ) (m : Model) (c : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)) (hsl : GoSlice) (es : List entry) (dq : DFrac)
    (h : List (Theory.Op OpV)) (cp : Bool),
  EntriesFor h es → (h.length : Int) < 2 ^ 60 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ context.isContext c cs ∗ isModelFilled S m ∗
      hsl ↦*{dq} es ∗ histIoOk S h }}
    (App (App (App (App (Val (@! github_com.anishathalye.porcupine.checkSingle))
      (Val #(GoInterface.ok c))) (Val #m)) (Val #hsl)) (Val #cp))
  {{ (b : Bool) (longest : GoSlice), RET (PairV #b #longest);
      (⌜b = true⌝ ∨ ⌜¬ Linearizable S.M h⌝ ∨ □ cs.PDone) ∗ longestOwn longest h.length }}

end spec

end porcupine
end EtcdGrove
end Perennial
