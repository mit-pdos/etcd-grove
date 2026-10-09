/-
Lemmas about `opFullAt`'s sort option (`opSortAt`, `InvOp.lean`), for the proofs of the options
and of `OpPut`/`OpDelete`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvOp

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The sort option is the same for two models that agree on it. -/
theorem opSortAt_of (p : Loc) (o o' : OpFull) (h1 : o'.base.sortSet = o.base.sortSet)
    (h2 : o'.sortTarget = o.sortTarget) (h3 : o'.sortOrder = o.sortOrder) :
    opSortAt (GF := GF) p o ⊢ opSortAt p o' := by
  unfold opSortAt
  rw [h1, h2, h3]

/-- No sort option. -/
theorem opSortAt_unset (p : Loc) (o : OpFull) (h : o.base.sortSet = false) :
    ⊢ opSortAt (GF := GF) p o := by
  unfold opSortAt
  rw [h]
  simp only [Bool.false_eq_true, ↓reduceIte]
  iintro; itrivial

end lemmas

end EtcdGrove
end Perennial
