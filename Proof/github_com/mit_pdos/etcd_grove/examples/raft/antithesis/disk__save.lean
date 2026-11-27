/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/disk__save.lean`: the hard state is
a fresh copy (`copyHardState`); the log is rebuilt by two appends to a `nil` slice, of the kept
prefix `d.ents[:at]` and of the new entries, all read-only (`wp_slice_append_persistent`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.disk__save
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.disk__base
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.copyHardState
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

theorem saveW_split (w : AntSim.DurW) (oh : Option HardStateM) (es : List EntryM) :
    saveW w oh es = saveW (saveW w oh []) none es := by
  cases oh <;> cases es <;> rfl

theorem saveOk_saveW (w : AntSim.DurW) (oh : Option HardStateM) (es : List EntryM) (h : SaveOk w es) :
    SaveOk (saveW w oh []) es := by
  cases oh <;> exact h

theorem save_at (len idx : w64) (h0 : 0 ≤ sint.Z len) (h1 : 1 ≤ uint.nat idx)
    (h2 : uint.nat idx - 1 ≤ sint.nat len) :
    uint.Z (idx - W64 0 - W64 1) ≤ uint.Z len ∧ 0 ≤ sint.Z (idx - W64 0 - W64 1) ∧
      sint.Z (idx - W64 0 - W64 1) ≤ sint.Z len ∧ sint.nat (idx - W64 0 - W64 1) = uint.nat idx - 1 := by
  word

theorem entRO_take_app (dls ls : List Loc) (log es : List EntryM) (k : Nat)
    (hl : dls.length = log.length) :
    (([∗list] p;e ∈ dls;log, entRO (GF := GF) p e) ∗ [∗list] p;e ∈ ls;es, entRO p e) ⊢
      [∗list] p;e ∈ dls.take k ++ ls;log.take k ++ es, entRO p e := by
  iintro ⟨#H1, #H2⟩
  have Ht : (dls.take k).length = (log.take k).length := by simp [hl]
  have Hd := (BigSepL2.bigSepL2_app_same_length (PROP := IProp GF)
    (Φ := fun _ p e => entRO (GF := GF) p e) (l1a := dls.take k) (l1b := dls.drop k)
    (l2a := log.take k) (l2b := log.drop k) (.inl Ht)).1
  rw [List.take_append_drop, List.take_append_drop] at Hd
  ihave H' := Hd $$ H1
  icases H' with ⟨#H3, -⟩
  iapply (BigSepL2.bigSepL2_app_same_length (PROP := IProp GF)
    (Φ := fun _ p e => entRO (GF := GF) p e) (.inl Ht)).2
  iframe H3 H2

theorem disk.save.wp_proof (wp_copyHardState : copyHardState.spec (GF := GF) (hG := hG))
    (wp_base : disk.base.spec (GF := GF) (hG := hG))
    (wp_GetIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG)) :
    disk.save.spec (GF := GF) (hG := hG) := by
  intro d w hp oh sl els es hok
  wp_start as ⟨Hd, Hh, #Hsl, #Hents⟩
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  wp_auto
  wp_join iprop(diskOwn d (saveW w oh []) ∗ d_ptr ↦ d) with [Hd Hh hs d] as ⟨Hd, d⟩
  · iunfold hsOptRO at Hh
    icases Hh with (⟨%Hn, %Ho⟩ | ⟨%h, ⟨%Hn, %Ho⟩, #Hh⟩)
    · subst Ho
      rw [show saveW w none [] = w from rfl]
      iframe
    · exact absurd rfl Hn
  · iunfold hsOptRO at Hh
    icases Hh with (⟨%Hn, %Ho⟩ | ⟨%h, ⟨%Hn, %Ho⟩, #Hh⟩)
    · exact absurd Hn Hif
    subst Ho
    wp_apply wp_copyHardState hp (some h) $$ [$Hpkg] as %hp' Hh'
    · iunfold hsOptRO; iright; iexists h; iframe Hh; ipureintro; exact ⟨Hn, rfl⟩
    iunfold hsOptRO at Hh'
    icases Hh' with (⟨%Hn', %Ho'⟩ | ⟨%h', ⟨%Hn', %Ho'⟩, #Hh'⟩)
    · cases Ho'
    cases Ho'
    iunfold diskOwn at Hd
    icases Hd with ⟨%hsl, %esl, Hhs, #Hhsr, Hsnap, Hents', #Hes, Hcap⟩
    wp_auto
    wp_join_done
    iframe
    iunfold diskOwn
    iexists hp', esl
    iframe
    simp only [saveW]
    iframe Hes
    iexact Hh'
  rw [saveW_split]
  have hok' := saveOk_saveW w oh es hok
  generalize saveW w oh [] = w1 at *
  clear hok
  ihave %Hl := BigSepL2.bigSepL2_length $$ Hents
  ihave %Hsl := ownSlice_len $$ Hsl
  cases es with
  | nil =>
    have H0 : decide (sint.Z (W64 0) < sint.Z sl.len) = false := by
      have h1 := Hsl.1; simp only [List.length_nil] at Hl; rw [Hl] at h1
      simp only [decide_eq_false_iff_not]; word
    rw [H0]
    wp_auto
    iapply HΦ
    rw [show saveW w1 none [] = w1 from rfl]
    iexact Hd
  | cons e r =>
    obtain ⟨l, ls, rfl⟩ : ∃ l ls, els = l :: ls := by
      cases els with
      | nil => simp at Hl
      | cons l ls => exact ⟨l, ls, rfl⟩
    icases BigSepL2.bigSepL2_cons $$ Hents with ⟨#He, #Hr⟩
    have H0 : decide (sint.Z (W64 0) < sint.Z sl.len) = true := by
      have h1 := Hsl.1; simp only [List.length_cons] at Hl h1; rw [Hl] at h1
      simp only [decide_eq_true_iff]; word
    rw [H0]
    wp_auto
    have Hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len := ⟨by decide, of_decide_eq_true H0⟩
    simp only [Hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z (W64 0)) (l :: ls) DFrac.discard l (by decide) $$ [Hsl] as -
    · iframe Hsl; ipureintro; rfl
    wp_apply wp_GetIndex.1 l DFrac.discard e $$ [$Hpb $He] as -
    wp_apply wp_base d w1 $$ [$Hpkg $Hd] as Hd
    simp only [Hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z (W64 0)) (l :: ls) DFrac.discard l (by decide) $$ [Hsl] as -
    · iframe Hsl; ipureintro; rfl
    wp_apply wp_GetIndex.1 l DFrac.discard e $$ [$Hpb $He] as -
    wp_apply wp_base d w1 $$ [$Hpkg $Hd] as Hd
    obtain ⟨hi1, hi2⟩ := hok' e rfl
    have Hle : decide (uint.Z e.Index' ≤ uint.Z (W64 0)) = false := by
      simp only [decide_eq_false_iff_not]; word
    iunfold diskOwn at Hd
    icases Hd with ⟨%hsl, %esl, Hhs, #Hhsr, Hsnap, Hents', #Hes, Hcap⟩
    iunfold entsPts at Hes
    icases Hes with ⟨%dls, #Hdl, #Hdb⟩
    ihave %Hdlen := ownSlice_len $$ Hdl
    ihave %Hdbl := BigSepL2.bigSepL2_length $$ Hdb
    rw [Hle]
    wp_auto
    obtain ⟨Ha1, Ha2, Ha3, Ha4⟩ := save_at esl.len e.Index' Hdlen.2 hi1 (by rw [← Hdlen.1, Hdbl]; exact hi2)
    rw [show decide (uint.Z esl.len < uint.Z (e.Index' - W64 0 - W64 1)) = false by
      simp only [decide_eq_false_iff_not, Int.not_lt]; exact Ha1]
    wp_auto
    ihave %Hcw := ownSliceCap_wf $$ Hcap
    have Hs : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (e.Index' - W64 0 - W64 1) ∧
        sint.Z (e.Index' - W64 0 - W64 1) ≤ sint.Z esl.cap := ⟨by decide, Ha2, by omega⟩
    simp only [Hs, _root_.and_self, ↓reduceIte]
    icases (ownSlice_slice (e.Index' - W64 0 - W64 1) esl.len esl DFrac.discard dls
      ⟨Ha2, Ha3, Int.le_refl _⟩).1 $$ Hdl with ⟨#Hpre, -, -⟩
    ihave #Hnil := ownSlice_nil (V := Loc) (GF := GF) DFrac.discard
    ihave Hcap0 := ownSliceCap_nil (V := Loc) (GF := GF)
    wp_apply wp_slice_append_persistent (V := Loc) slice.nil []
      (slice.slice esl Loc (W64 0) (e.Index' - W64 0 - W64 1))
      (dls.take (sint.nat (e.Index' - W64 0 - W64 1))) DFrac.discard
      $$ [$Hnil $Hcap0 Hpre] as %s1 ⟨#Hs1, Hcap1, -⟩
    · iexact Hpre
    wp_apply wp_slice_append_persistent (V := Loc) s1 _ sl (l :: ls) DFrac.discard
      $$ [$Hs1 $Hcap1 $Hsl] as %s2 ⟨#Hs2, Hcap2, -⟩
    iapply HΦ
    iunfold diskOwn
    iexists hsl, s2
    simp only [saveW]
    iframe Hhs Hhsr Hsnap Hents' Hcap2
    iunfold entsPts
    iexists _
    rw [Ha4, List.nil_append]
    iframe Hs2
    iapply entRO_take_app dls (l :: ls) w1.log (e :: r) _ Hdbl
    iframe Hdb Hents

end proof

end AntHarness
end EtcdGrove
end Perennial
