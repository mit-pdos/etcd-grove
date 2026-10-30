/-
Closing (or remapping) the database with `mmaplock` write-locked: its whole token leaves no
reader's (`mmapTok_full_none`); with no reader and no writer the database holds all of the
mapping's cells (`close_gather`, which `munmap` takes) and all of the shared fields
(`frem_whole`).
-/
module

public import Proof.go_etcd_io.bbolt.DBRemap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section close
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

/-- The whole `mmapTok` (`mmaplock` write-locked) leaves no reader's token. -/
theorem mmapTok_full_none (γ : GName) (M : GMap Nat Reader) :
    mmapTok (GF := GF) γ 1 ∗ ([∗map] _k ↦ _r ∈ M, mmapTok (GF := GF) γ sync.rfrac) ⊢
      ⌜M = ∅⌝ ∗ mmapTok (GF := GF) γ 1 := by
  iintro ⟨H1, Hm⟩
  by_cases h : M = ∅
  · iframe; ipureintro; exact h
  obtain ⟨k, r, hk⟩ : ∃ k r, M !! k = some r := by
    refine Classical.byContradiction fun hc => h ((GMap.lookup_empty_iff M).1 fun k => ?_)
    cases e : M !! k with
    | none => rfl
    | some r => exact absurd ⟨k, r, e⟩ hc
  icases (BigSepM.bigSepM_lookup_acc (M := GMap Nat)
    (Φ := fun (_ : Nat) (_ : Reader) => mmapTok (GF := GF) γ sync.rfrac)
    (show Std.get? M k = some r from hk)).1 $$ Hm with ⟨Ht, -⟩
  simp only [mmapTok]
  ihave %Hv := ghostVar_valid_2 _ _ _ _ _ $$ H1 Ht
  exfalso
  have hp := (sync.rfrac).2
  have h1 := Hv.1
  generalize sync.rfrac = q at h1 hp
  have h2 : (1 + q).val ≤ (1 : Qp).val := h1
  rw [Qp.val_add, Qp.val_one] at h2
  grind

/-- No reader and no writer: the database's part of every slot is the caller's half. -/
theorem slot_half_alone (σ : DBState) (v0 v1 : internal.common.Meta) (h : dbOK σ v0 v1)
    (hr : σ.readers = ∅) (hw : σ.wr = none) (s : Nat) (hs : s < σ.nslots) :
    σ.rem s = halfQ := by
  have H := h.2.2.2.2.2.2.2.2.2.2.2.1 s hs
  have hn : readersQ σ.readers (fun r => r.sees s) = none :=
    readersQ_none _ _ (fun k r hk => by rw [hr] at hk; simp at hk)
  rw [hn, hw] at H
  exact H

/-- No reader and no writer: the shared fields are the database's alone. -/
theorem frem_whole (σ : DBState) (v0 v1 : internal.common.Meta) (h : dbOK σ v0 v1)
    (hr : σ.readers = ∅) (hw : σ.wr = none) : σ.frem = 1 := by
  have H := h.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold fieldsOK at H
  have hn : readersQ σ.readers (fun _ => true) = none :=
    readersQ_none _ _ (fun k r hk => by rw [hr] at hk; simp at hk)
  rw [hn, hw] at H
  exact H

/-- No reader and no writer: the database's cells of the mapping are all of it. -/
theorem close_gather (σ : DBState) (v0 v1 : internal.common.Meta) (h : dbOK σ v0 v1)
    (hr : σ.readers = ∅) (hw : σ.wr = none) :
    slotsView (GF := GF) σ.data σ.bs σ.ps σ.rem (List.range σ.nslots) ∗
      mapTail σ.data σ.bs σ.sz σ.ps ⊢
    mapRange (some (σ.data, σ.sz)) σ.bs 0 σ.sz := by
  have Hc : slotsView (GF := GF) σ.data σ.bs σ.ps σ.rem (List.range σ.nslots) ⊣⊢
      slotsView σ.data σ.bs σ.ps (fun _ => halfQ) (List.range σ.nslots) := by
    unfold slotsView
    refine bigSepL_congr_mem (fun k s hs => ?_)
    rw [slot_half_alone σ v0 v1 h hr hw s (List.mem_range.1 hs)]
    exact .rfl
  iintro ⟨Hs, Ht⟩
  ihave Hs := Hc.1 $$ Hs
  ihave Hs := (slots_const (GF := GF) σ.data σ.bs σ.ps halfQ σ.nslots (nslots_mul_le σ)).1 $$ Hs
  iapply (mapRange_slots (GF := GF) σ.data σ.bs σ.sz σ.ps).2
  unfold DBState.nslots
  iframe

end close

end bbolt
end EtcdGrove
end Perennial
