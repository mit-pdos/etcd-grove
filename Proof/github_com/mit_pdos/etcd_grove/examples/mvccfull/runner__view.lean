/- Lean-first (no Rocq counterpart). The proof of `runner.view`: proved.

The outline: `history.snapshot` (it extends `Hs`); the three-index slice `st[:p.rev:p.rev]`
(`ownSlice_same_ptr_len'`), the pending map appended when it has a change.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__view
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.history__snapshot

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

private theorem zip_disc (ms : List GoMap) (Hs : List HRev) :
    ms.zip ((Hs.map Prod.fst).zip (List.replicate Hs.length DFrac.discard)) =
      (ms.zip Hs).map (fun x => (x.1, (x.2.1, DFrac.discard))) := by
  induction ms generalizing Hs with
  | nil => simp
  | cons m ms ih =>
    cases Hs with
    | nil => simp
    | cons e Hs => simp [List.replicate_succ, ih]

/-- The history's maps, persistent, are the states at `DFrac.discard`. -/
private theorem statesAt_hist (ms : List GoMap) (Hs : List HRev) :
    statesP (GF := GF) ms Hs ⊢ statesAt ms (Hs.map Prod.fst) (List.replicate Hs.length DFrac.discard) := by
  unfold statesP statesAt
  iintro ⟨%h, H⟩
  rw [zip_disc, BigSepL.bigSepL_map]
  isplitr
  · ipureintro; simp [h]
  iexact H

/-- A prefix of the history's maps. -/
private theorem statesP_take (ms : List GoMap) (Hs Hs' : List HRev) (hp : Hs <+: Hs') :
    statesP (GF := GF) ms Hs' ⊢ statesP (ms.take Hs.length) Hs := by
  unfold statesP
  iintro ⟨%h, H⟩
  obtain ⟨t, rfl⟩ := hp
  have hz : ms.zip (Hs ++ t) = (ms.take Hs.length).zip Hs ++ (ms.drop Hs.length).zip t := by
    conv => lhs; rw [← List.take_append_drop Hs.length ms]
    rw [List.zip_append]; simp [List.length_take]; simp at h; omega
  rw [hz]
  icases BigSepL.bigSepL_append.1 $$ H with ⟨H, -⟩
  isplitr
  · ipureintro; simp at h ⊢; omega
  iexact H

private theorem zip_snoc {α β δ : Type} (ms : List α) (Ms : List β) (dqs : List δ) (m : α) (M : β)
    (dq : δ) (h1 : ms.length = Ms.length) (h2 : Ms.length = dqs.length) :
    (ms ++ [m]).zip ((Ms ++ [M]).zip (dqs ++ [dq])) = ms.zip (Ms.zip dqs) ++ [(m, (M, dq))] := by
  rw [List.zip_append h2, List.zip_append (by simp [List.length_zip, h1, h2])]
  rfl

private theorem statesAt_snoc_intro (ms : List GoMap) (Ms : List (GMap GoString kvRec))
    (dqs : List DFrac) (m : GoMap) (M : GMap GoString kvRec) (dq : DFrac)
    (h1 : ms.length = Ms.length) (h2 : Ms.length = dqs.length) :
    statesAt (GF := GF) ms Ms dqs ∗ m ↦${dq} M ⊢ statesAt (ms ++ [m]) (Ms ++ [M]) (dqs ++ [dq]) := by
  unfold statesAt
  iintro ⟨⟨%h, H⟩, Hm⟩
  rw [zip_snoc _ _ _ _ _ _ h1 h2]
  isplitr
  · ipureintro; simp [h1, h2]
  iapply BigSepL.bigSepL_snoc.2
  iframe

private theorem statesAt_snoc_last (ms : List GoMap) (Ms : List (GMap GoString kvRec))
    (dqs : List DFrac) (m : GoMap) (M : GMap GoString kvRec) (dq : DFrac)
    (h1 : ms.length = Ms.length) (h2 : Ms.length = dqs.length) :
    statesAt (GF := GF) (ms ++ [m]) (Ms ++ [M]) (dqs ++ [dq]) ⊢ m ↦${dq} M := by
  unfold statesAt
  iintro ⟨-, H⟩
  rw [zip_snoc _ _ _ _ _ _ h1 h2]
  icases BigSepL.bigSepL_snoc.1 $$ H with ⟨-, H⟩
  iexact H

theorem runner.view.wp_proof
    (wp_snapshot : history.snapshot.spec (GF := GF) (hG := hG)) :
    runner.view.spec (GF := GF) (hG := hG) := by
  intro x h γh Hs p P hPrev h2 h63
  wp_start as ⟨Hh, Hrd, #Hlb, Hpend⟩
  iunfold ownPending at Hpend
  icases Hpend with ⟨%pv, Hp, %Hrev, Hst, Hchs, Hcap⟩
  ihave %Hcl := ownSlice_len $$ Hchs
  iunfold runnerH at Hh
  icases Hh with #Hh
  wp_auto
  wp_apply wp_snapshot h γh Hs $$ [$Hrd $Hlb] as %s ⟨Hrd, %ms, %Hs', ⟨%Hpre, %H2⟩, %Hscap, #Hlb', #Hms, #Hst'⟩
  ihave %Hmlen : ⌜ms.length = Hs'.length⌝ $$ [Hst']
  · iunfold statesP at Hst'; icases Hst' with ⟨%H, -⟩; ipureintro; exact H
  ihave %Hsl := ownSlice_len $$ Hms
  have hle : Hs.length ≤ Hs'.length := Hpre.length_le
  have hrevZ : sint.Z pv.rev' = Hs.length := by rw [Hrev, hPrev]; word
  have hsl : sint.Z s.len = ms.length := by
    have : sint.nat s.len = (sint.Z s.len).toNat := rfl
    omega
  -- the three-index slice: the first `Hs.length` maps
  have hfs : (slice.fullSlice s GoMap (W64 0) pv.rev' pv.rev') =
      ⟨sliceIndexRef GoMap 0 s, pv.rev', pv.rev'⟩ := by
    simp only [slice.fullSlice]; congr 1 <;> word
  ihave #Hms2 : (slice.fullSlice s GoMap (W64 0) pv.rev' pv.rev') ↦*□ ms.take Hs.length $$ [Hms]
  · icases (ownSlice_slice (W64 0) pv.rev' s DFrac.discard ms ⟨by word, by word, by omega⟩).1 $$ Hms
      with ⟨-, Hm, -⟩
    have hsub : subslice (sint.nat (W64 0)) (sint.nat pv.rev') ms = ms.take Hs.length := by
      have h0 : sint.nat (W64 0) = 0 := rfl
      have h1 : sint.nat pv.rev' = Hs.length := by
        have : sint.nat pv.rev' = (sint.Z pv.rev').toNat := rfl
        omega
      simp only [subslice, h0, h1, List.drop_zero]
    rw [hsub]
    iapply ownSlice_same_ptr_len' (slice.slice s GoMap (W64 0) pv.rev')
      (slice.fullSlice s GoMap (W64 0) pv.rev' pv.rev') DFrac.discard (ms.take Hs.length)
      (by intro hn; have := congrArg List.length hn; rw [List.length_take, List.length_nil] at this; omega)
      (by simp only [slice.slice, slice.fullSlice]) (by simp only [slice.slice, slice.fullSlice])
      (by simp only [slice.fullSlice]; word)
    iexact Hm
  ihave #Hst2 := statesP_take ms Hs Hs' Hpre $$ Hst'
  have hcond : (0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z pv.rev' ∧ sint.Z pv.rev' ≤ sint.Z pv.rev' ∧
      sint.Z pv.rev' ≤ sint.Z s.cap) := ⟨by word, by word, by omega, by rw [Hscap]; omega⟩
  (try wp_auto)
  by_cases hc : P.chs = []
  · have h0 : pv.changes'.len = W64 0 := by
      have : sint.nat pv.changes'.len = (sint.Z pv.changes'.len).toNat := rfl
      rw [hc] at Hcl; simp only [List.length_nil] at Hcl; word
    simp only [h0, _root_.decide_true, ↓reduceIte]
    (try wp_auto)
    simp only [if_pos hcond]
    (try wp_auto)
    iapply HΦ
    iframe
    isplitr
    · ipureintro; unfold viewRev; simp only [hc, ↓reduceIte, Hrev]
    iexists DFrac.discard, ms.take Hs.length
    iframe Hms2
    unfold viewSt viewDq
    simp only [hc, ↓reduceIte, List.append_nil]
    isplitr [Hp Hst Hchs Hcap]
    · iapply statesAt_hist $$ Hst2
    iintro -
    iunfold ownPending
    rw [hc]
    iexists pv
    iframe
    ipureintro; exact Hrev
  · have h0 : pv.changes'.len ≠ W64 0 := by
      have : sint.nat pv.changes'.len = (sint.Z pv.changes'.len).toNat := rfl
      intro h; apply hc; apply List.length_eq_zero_iff.1; rw [Hcl.1, h]; word
    simp only [h0, _root_.decide_false, ↓reduceIte]
    (try wp_auto)
    simp only [if_pos hcond]
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %osl ⟨Hosl, -⟩
    (try wp_auto)
    ihave %Hsl2 := ownSlice_len $$ Hms2
    ihave Hscap := ownSliceCap_empty (GF := GF) (V := GoMap) (slice.fullSlice s GoMap (W64 0) pv.rev' pv.rev')
      (by simp only [slice.fullSlice]) Hsl2.2
    wp_apply wp_slice_append_dfrac _ (ms.take Hs.length) DFrac.discard _ [pv.st'] (DFrac.own 1)
      $$ [$Hms2 $Hscap $Hosl] as %s2 ⟨Hs2, -, -⟩
    · ipureintro; exact DFrac.valid_discard
    (try wp_auto)
    iapply HΦ
    iframe
    isplitr
    · ipureintro; unfold viewRev; simp only [hc, ↓reduceIte, Hrev]
    unfold viewSt viewDq
    simp only [hc, ↓reduceIte]
    have hml : (ms.take Hs.length).length = (Hs.map Prod.fst).length := by simp; omega
    isplitr [Hp Hchs Hcap]
    · iapply statesAt_snoc_intro _ _ _ _ _ _ hml (by simp)
      iframe Hst
      iapply statesAt_hist $$ Hst2
    iintro H
    ihave Hst := statesAt_snoc_last _ _ _ _ _ _ hml (by simp) $$ H
    iunfold ownPending
    iexists pv
    iframe
    ipureintro; exact Hrev

end proof

end mvccfull
end EtcdGrove
end Perennial
