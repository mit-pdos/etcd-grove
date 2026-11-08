/- Lean-first (no Rocq counterpart). The proof of `writer.view`: the snapshot is the writer's
revisions exactly (its lower bound and its half of the list, as in `writer.begin`); with no change
pending it is returned as is, else the pending map is appended (`append(st, p.st)` on the
three-index slice `h.states[:n:n]`, so a copy), lent from `ownPending`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__view
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.history__snapshot

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccrand mvcc.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

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

private theorem zip_snoc {α β δ : Type} (ms : List α) (Ms : List β) (dqs : List δ) (m : α) (M : β)
    (dq : δ) (h1 : ms.length = Ms.length) (h2 : Ms.length = dqs.length) :
    (ms ++ [m]).zip ((Ms ++ [M]).zip (dqs ++ [dq])) = ms.zip (Ms.zip dqs) ++ [(m, (M, dq))] := by
  rw [List.zip_append h2, List.zip_append (by simp [List.length_zip, h1, h2])]
  rfl

/-- A state appended to the states. -/
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

/-- The last state of the states. -/
private theorem statesAt_snoc_last (ms : List GoMap) (Ms : List (GMap GoString kvRec))
    (dqs : List DFrac) (m : GoMap) (M : GMap GoString kvRec) (dq : DFrac)
    (h1 : ms.length = Ms.length) (h2 : Ms.length = dqs.length) :
    statesAt (GF := GF) (ms ++ [m]) (Ms ++ [M]) (dqs ++ [dq]) ⊢ m ↦${dq} M := by
  unfold statesAt
  iintro ⟨-, H⟩
  rw [zip_snoc _ _ _ _ _ _ h1 h2]
  icases BigSepL.bigSepL_snoc.1 $$ H with ⟨-, H⟩
  iexact H

theorem writer.view.wp_proof (wp_snapshot : history.snapshot.spec (GF := GF) (hG := hG)) :
    writer.view.spec (GF := GF) (hG := hG) := by
  intro w wv γ σ Hs p P hPrev
  wp_start as ⟨#Hw, Hrd, Hidle, Hpend⟩
  iunfold writerIdle at Hidle
  icases Hidle with ⟨Hgσ, HW, Hpv, %Hid⟩
  icases histW_lb γ.h Hs $$ HW with ⟨HW, #Hlb⟩
  ihave #Hw2 := Hw
  iunfold writerRO at Hw2
  icases Hw2 with ⟨#kvW, #leW, #hW, #rW, #leasesW, #applyingW, #savedW, #ticksW⟩
  iunfold ownPending at Hpend
  icases Hpend with ⟨%pv, Hp, %Hrev, Hst, Hchs, Hcap⟩
  ihave %Hcl := ownSlice_len $$ Hchs
  wp_auto
  wp_apply wp_snapshot wv.h' γ.h Hs $$ [$Hrd $Hlb] as %s ⟨Hrd, %ms, %Hs', %Hpre, %Hcap, #Hlb', #Hms, #Hst'⟩
  -- the snapshot is the writer's revisions
  ihave %Hle : ⌜Hs' <+: Hs⌝ $$ [HW]
  · iunfold histW at HW
    icases HW with ⟨%x, %Hx, -, Hl, -, -⟩
    ihave %H := mono_list_auth_lb_valid γ.h.l _ _ _ $$ Hl Hlb'
    ipureintro; exact H.2
  have hHs : Hs' = Hs := List.IsPrefix.eq_of_length Hle (Nat.le_antisymm Hle.length_le Hpre.1.length_le)
  subst hHs
  ihave %Hmlen : ⌜ms.length = Hs'.length⌝ $$ [Hst']
  · iunfold statesP at Hst'; icases Hst' with ⟨%H, -⟩; ipureintro; exact H
  ihave %Hsl := ownSlice_len $$ Hms
  (try wp_auto)
  by_cases hc : P.chs = []
  · -- nothing pending: the snapshot
    have h0 : pv.changes'.len = W64 0 := by
      have : sint.nat pv.changes'.len = (sint.Z pv.changes'.len).toNat := rfl
      rw [hc] at Hcl; simp only [List.length_nil] at Hcl; word
    simp only [h0, _root_.decide_true]
    (try wp_auto)
    iapply HΦ
    iframe
    isplitr [Hp Hst Hchs Hcap]
    · iunfold writerIdle; iframe; ipureintro; exact Hid
    isplitr
    · ipureintro; unfold viewRev; simp only [hc, ↓reduceIte, Hrev]
    iexists DFrac.discard, ms
    iframe Hms
    unfold viewSt viewDq
    simp only [hc, ↓reduceIte, List.append_nil]
    isplitr [Hp Hst Hchs Hcap]
    · iapply statesAt_hist $$ Hst'
    iintro -
    iunfold ownPending
    rw [hc]
    iexists pv
    iframe
    ipureintro; exact Hrev
  · -- the pending map appended (a copy: the snapshot's capacity is its length)
    have h0 : pv.changes'.len ≠ W64 0 := by
      have : sint.nat pv.changes'.len = (sint.Z pv.changes'.len).toNat := rfl
      intro h; apply hc; apply List.length_eq_zero_iff.1; rw [Hcl.1, h]; word
    simp only [h0, _root_.decide_false]
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %osl ⟨Hosl, -⟩
    (try wp_auto)
    have hcap : s.len = s.cap := Hcap.symm
    ihave Hscap := ownSliceCap_empty (GF := GF) (V := GoMap) s hcap Hsl.2
    wp_apply wp_slice_append_dfrac s ms DFrac.discard _ [pv.st'] (DFrac.own 1)
      $$ [$Hms $Hscap $Hosl] as %s2 ⟨Hs2, -, -⟩
    · ipureintro; exact DFrac.valid_discard
    (try wp_auto)
    iapply HΦ
    iframe
    isplitr [Hp Hst Hchs Hcap]
    · iunfold writerIdle; iframe; ipureintro; exact Hid
    isplitr
    · ipureintro; unfold viewRev; simp only [hc, ↓reduceIte, Hrev]
    unfold viewSt viewDq
    simp only [hc, ↓reduceIte]
    isplitr [Hp Hchs Hcap]
    · iapply statesAt_snoc_intro _ _ _ _ _ _ (by simp [Hmlen]) (by simp)
      iframe Hst
      iapply statesAt_hist $$ Hst'
    iintro H
    ihave Hst := statesAt_snoc_last _ _ _ _ _ _ (by simp [Hmlen]) (by simp) $$ H
    iunfold ownPending
    iexists pv
    iframe
    ipureintro; exact Hrev

end proof

end mvccrand
end EtcdGrove
end Perennial
