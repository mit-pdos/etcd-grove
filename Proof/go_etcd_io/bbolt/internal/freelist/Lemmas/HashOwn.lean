/-
The `hashMap` implementation's own part (`hashImpl`, `Lemmas/Own.lean`) as its raw fields
(`hmRaw`, the old proof's `HashModel.lean`) and the consistency of its maps (`hashOK`).
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Own

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section preds
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- The fields of the `hashMap` at `h` but its `shared`, and its maps' contents. -/
def hmRaw (h : Loc) (cnt : w64) (sp bwm : GMap w64 w64) (sets : GMap w64 (GMap w64 Unit)) :
    IProp GF :=
  iprop(∃ (fm fw bw : Loc) (FM : GMap w64 Loc),
    "Hcnt" ∷ structFieldRef hashMap go!"freePagesCount" h ↦ cnt ∗
    "Hfmf" ∷ structFieldRef hashMap go!"freemaps" h ↦ fm ∗
    "Hfwf" ∷ structFieldRef hashMap go!"forwardMap" h ↦ fw ∗
    "Hbwf" ∷ structFieldRef hashMap go!"backwardMap" h ↦ bw ∗
    "Hfm" ∷ fm ↦$ FM ∗ "Hsets" ∷ ([∗map] _sz ↦ l;st ∈ FM;sets, l ↦$ st) ∗
    "Hfw" ∷ fw ↦$ sp ∗ "Hbw" ∷ bw ↦$ bwm)

theorem hashImpl_own_open (h : Loc) (free : List w64) :
    (hashImpl (GF := GF) h).own free ⊢ ∃ (cnt : w64) (sp bwm : GMap w64 w64)
      (sets : GMap w64 (GMap w64 Unit)), hmRaw h cnt sp bwm sets ∗ ⌜hashOK cnt sp bwm sets free⌝ := by
  dsimp only [hashImpl]
  iintro ⟨%cnt, %sp, %bwm, %sets, %fm, %fw, %bw, %FM, Hcnt, Hfmf, Hfwf, Hbwf, Hfm, Hsets, Hfw, Hbw,
    %Hok⟩
  iexists cnt, sp, bwm, sets
  isplitl
  · iunfold hmRaw
    iexists fm, fw, bw, FM
    iframe
  · ipureintro; exact Hok

theorem hashImpl_own_close (h : Loc) (free : List w64) (cnt : w64) (sp bwm : GMap w64 w64)
    (sets : GMap w64 (GMap w64 Unit)) (hok : hashOK cnt sp bwm sets free) :
    hmRaw (GF := GF) h cnt sp bwm sets ⊢ (hashImpl (GF := GF) h).own free := by
  dsimp only [hashImpl]
  iintro H
  iunfold hmRaw at H
  icases H with ⟨%fm, %fw, %bw, %FM, Hcnt, Hfmf, Hfwf, Hbwf, Hfm, Hsets, Hfw, Hbw⟩
  iexists cnt, sp, bwm, sets, fm, fw, bw, FM
  iframe
  ipureintro; exact hok

/-- The `hashMap` at `h` holds the free ids `free` (the old proof's form; `_s` its `shared`,
unused). -/
def ownHashPart (h : Loc) (_s : Loc) (free : List w64) : IProp GF :=
  iprop(∃ (cnt : w64) (sp bwm : GMap w64 w64) (sets : GMap w64 (GMap w64 Unit)),
    "Hraw" ∷ hmRaw h cnt sp bwm sets ∗ "%Hok" ∷ ⌜hashOK cnt sp bwm sets free⌝)

theorem ownHashPart_iff (h s : Loc) (free : List w64) :
    ownHashPart (GF := GF) h s free ⊣⊢ (hashImpl (GF := GF) h).own free := by
  constructor
  · iintro H
    iunfold ownHashPart at H
    icases H with ⟨%cnt, %sp, %bwm, %sets, Hraw, %Hok⟩
    iapply hashImpl_own_close h free cnt sp bwm sets Hok $$ Hraw
  · iintro H
    icases hashImpl_own_open h free $$ H with ⟨%cnt, %sp, %bwm, %sets, Hraw, %Hok⟩
    iunfold ownHashPart
    iexists cnt, sp, bwm, sets
    iframe
    ipureintro; exact Hok

end preds

end bbolt
end EtcdGrove
end Perennial
