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

/-- A closure needing no resource needs any: `optSpec` frames `R`. -/
theorem optSpec_res (f : GoFunc) (g : OpFull → OpFull) (R : IProp GF) :
    optSpec (GF := GF) f g ⊢ optSpecRes f g R := by
  unfold optSpec optSpecRes
  iintro #Hf
  imodintro
  iintro %opp %op %o
  imodintro
  iintro %Φ ⟨HR, Hop, #Hat⟩ HΦ
  ihave Hf' := Hf $$ %opp %op %o
  iapply Hf' $$ [$Hop $Hat]
  inext
  iintro %op' ⟨Hop, #Hat'⟩
  iapply HΦ
  iframe
  iexact Hat'

/-- An `OpOption` slice of closures needing no resource is one needing any (`optSpec_res`). -/
theorem optsAt_res (sl : GoSlice) (gs : List (OpFull → OpFull)) (R : IProp GF) :
    optsAt (GF := GF) sl gs ⊢ optsAtRes sl gs R := by
  unfold optsAt optsAtRes
  iintro ⟨%fs, #Hsl, %Hlen, #Hfs⟩
  iexists fs
  iframe Hsl
  isplitr
  · ipureintro; exact Hlen
  imodintro
  iintro %i %f %g %Hf %Hg
  ihave #H := Hfs $$ %i %f %g %Hf %Hg
  iapply optSpec_res $$ H

end lemmas

end EtcdGrove
end Perennial
