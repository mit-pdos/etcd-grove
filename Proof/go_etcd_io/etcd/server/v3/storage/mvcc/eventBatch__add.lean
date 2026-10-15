/-
Proof of `Spec/.../mvcc/eventBatch__add.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.eventBatch__add

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.eventBatch.add.wp_proof : mvcc.eventBatch.add.spec (GF := GF) (hG := hG) := by
  intro eb B e ev
  wp_start as ⟨HB, #He⟩
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hmax, -⟩
  iunfold mvcc.ownEventBatch at HB
  icases HB with ⟨%s, %ps, Heb, Hs, Hcap, %Hlen, Hevs⟩
  ihave %Hsl := ownSlice_len $$ Hs
  wp_auto
  have Hpack : ∀ (B' : mvcc.EventBatch) (s' : GoSlice) (ps' : List Loc),
      ps'.length = B'.evs.length →
      (eb ↦ ({ evs' := s', revs' := B'.revs, moreRev' := B'.moreRev } : eventBatch) ∗
        s' ↦* ps' ∗ ownSliceCap Loc s' (DFrac.own 1) ∗
        ([∗list] x ∈ ps'.zip B'.evs, mvcc.evIs x.1 x.2) : IProp GF) ⊢ mvcc.ownEventBatch eb B' := by
    intro B' s' ps' hl
    iintro ⟨H1, H2, H3, H4⟩
    iunfold mvcc.ownEventBatch
    iexists s', ps'
    iframe H1 H2 H3 H4
    ipureintro; exact hl
  by_cases hcap : sint.Z (W64 1000) < sint.Z B.revs
  · rw [_root_.decide_eq_true hcap]
    wp_auto
    have hB : mvcc.ebAdd B ev = B := by
      unfold mvcc.ebAdd mvcc.watchBatchMaxRevsV; rw [ite_eq_left hcap]
    rw [hB]
    iapply HΦ
    iapply Hpack B s ps Hlen
    iframe
  rw [_root_.decide_eq_false hcap]
  wp_auto
  by_cases h0 : B.evs = []
  · have hps : ps = [] := List.eq_nil_of_length_eq_zero (by rw [Hlen, h0]; rfl)
    subst hps
    have hl0 : s.len = W64 0 := by
      have := Hsl.1; simp only [List.length_nil] at this; word
    rw [hl0, _root_.decide_eq_true rfl]
    wp_auto
    wp_apply wp_slice_literal (l := [e])
    isplitr
    · ipureintro; rfl
    iintro %lit ⟨Hlit, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [$Hs $Hcap $Hlit] as %s' ⟨Hs, Hcap, -⟩
    (try wp_auto)
    have hB : mvcc.ebAdd B ev = { evs := [ev], revs := W64 1, moreRev := B.moreRev } := by
      unfold mvcc.ebAdd mvcc.watchBatchMaxRevsV; rw [ite_eq_right hcap, h0]; rfl
    rw [hB]
    iapply HΦ
    iapply Hpack _ s' [e] rfl
    simp only [List.nil_append, List.zip_cons_cons, List.zip_nil_left]
    iframe Heb Hs Hcap
    iapply BigSepL.bigSepL_singleton.2
    iexact He
  have hne : s.len ≠ W64 0 := by
    intro h; apply h0; apply List.eq_nil_of_length_eq_zero
    rw [← Hlen, Hsl.1, h]; rfl
  rw [_root_.decide_eq_false hne]
  obtain ⟨init, last, hBe⟩ : ∃ init last, B.evs = init ++ [last] := by
    rcases List.eq_nil_or_concat B.evs with h | ⟨L, b, h⟩
    · exact absurd h h0
    · exact ⟨L, b, by rw [h, List.concat_eq_append]⟩
  obtain ⟨pinit, pl, hps⟩ : ∃ pinit pl, ps = pinit ++ [pl] := by
    rcases List.eq_nil_or_concat ps with h | ⟨L, b, h⟩
    · subst h; rw [hBe] at Hlen; simp at Hlen
    · exact ⟨L, b, by rw [h, List.concat_eq_append]⟩
  have hil : pinit.length = init.length := by
    rw [hps, hBe] at Hlen; simpa using Hlen
  wp_auto
  have hsl1 : sint.Z (s.len - W64 1) = (pinit.length : Int) := by
    have := Hsl.1; rw [hps] at this; simp at this; word
  rw [ite_eq_left (show 0 ≤ sint.Z (s.len - W64 1) ∧ sint.Z (s.len - W64 1) < sint.Z s.len by
    have := Hsl.1; rw [hps] at this; simp at this; constructor <;> word)]
  subst hps
  icases ownSlice_elem_acc (sint.Z (s.len - W64 1)) pl s _ (pinit ++ [pl])
    (by rw [hsl1]; omega) (by rw [hsl1]; simp) $$ Hs with ⟨Hp, Hs⟩
  rw [hBe, List.zip_append hil]
  simp only [List.zip_cons_cons, List.zip_nil_left]
  icases BigSepL.bigSepL_snoc.1 $$ Hevs with ⟨Hevs, #Hl⟩
  simp only
  ihave #Hl' := Hl
  ihave #He' := He
  iunfold mvcc.evIs at Hl' He'
  icases Hl' with ⟨%p1, %q1, %st1, %uf1, %sc1, %Hn1, #Hpl, #Hkv1, -⟩
  icases He' with ⟨%p2, %q2, %st2, %uf2, %sc2, %Hn2, #Hev, #Hkv2, #Hprev2⟩
  iunfold mvcc.kvPtrFixed at Hkv1 Hkv2
  icases Hkv1 with ⟨%ks1, %vs1, %kst1, %kuf1, %ksc1, -, -, #Hk1⟩
  icases Hkv2 with ⟨%ks2, %vs2, %kst2, %kuf2, %ksc2, -, -, #Hk2⟩
  icases mvcc.event_fields _ _ _ $$ Hpl with ⟨-, #Hpl, -⟩
  icases mvcc.event_fields _ _ _ $$ Hev with ⟨-, #Hev, -⟩
  icases mvcc.kv_fields _ _ _ $$ Hk1 with ⟨-, #Hk1⟩
  icases mvcc.kv_fields _ _ _ $$ Hk2 with ⟨-, #Hk2⟩
  wp_auto
  ihave Hs := Hs $$ Hp
  rw [show (pinit ++ [pl]).set (sint.Z (s.len - W64 1)).toNat pl = pinit ++ [pl] by
    rw [hsl1]; simp]
  have hgl : B.evs.getLast? = some last := by rw [hBe]; simp
  by_cases hrev : sint.Z last.kv.modRev < sint.Z ev.kv.modRev
  · rw [_root_.decide_eq_true hrev]
    wp_auto
    by_cases hcap2 : sint.Z (W64 1000) < sint.Z (B.revs + W64 1)
    · rw [_root_.decide_eq_true hcap2]
      wp_auto
      have hB : mvcc.ebAdd B ev = { B with revs := B.revs + W64 1, moreRev := ev.kv.modRev } := by
        unfold mvcc.ebAdd mvcc.watchBatchMaxRevsV
        rw [ite_eq_right hcap, hgl]; simp only [ite_eq_left hrev, ite_eq_left hcap2]
      rw [hB]
      iapply HΦ
      iapply Hpack _ s (pinit ++ [pl]) (by simp [hBe, hil])
      simp only
      iframe Heb Hs Hcap
      rw [hBe, List.zip_append hil]
      simp only [List.zip_cons_cons, List.zip_nil_left]
      iapply BigSepL.bigSepL_snoc.2
      iframe Hevs Hl
    · rw [_root_.decide_eq_false hcap2]
      wp_auto
      wp_apply wp_slice_literal (l := [e])
      isplitr
      · ipureintro; rfl
      iintro %lit ⟨Hlit, -⟩
      wp_auto
      wp_apply wp_slice_append $$ [$Hs $Hcap $Hlit] as %s' ⟨Hs, Hcap, -⟩
      (try wp_auto)
      have hB : mvcc.ebAdd B ev =
          { evs := B.evs ++ [ev], revs := B.revs + W64 1, moreRev := B.moreRev } := by
        unfold mvcc.ebAdd mvcc.watchBatchMaxRevsV
        rw [ite_eq_right hcap, hgl]; simp only [ite_eq_left hrev, ite_eq_right hcap2]
      rw [hB]
      iapply HΦ
      iapply Hpack _ s' (pinit ++ [pl] ++ [e]) (by simp [hBe, hil])
      simp only
      iframe Heb Hs Hcap
      rw [hBe, List.zip_append (by simp [hil]), List.zip_append hil]
      simp only [List.zip_cons_cons, List.zip_nil_left]
      iapply BigSepL.bigSepL_snoc.2
      iframe He
      iapply BigSepL.bigSepL_snoc.2
      iframe Hevs Hl
  · rw [_root_.decide_eq_false hrev]
    wp_auto
    wp_apply wp_slice_literal (l := [e])
    isplitr
    · ipureintro; rfl
    iintro %lit ⟨Hlit, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [$Hs $Hcap $Hlit] as %s' ⟨Hs, Hcap, -⟩
    (try wp_auto)
    have hB : mvcc.ebAdd B ev = { B with evs := B.evs ++ [ev] } := by
      unfold mvcc.ebAdd mvcc.watchBatchMaxRevsV
      rw [ite_eq_right hcap, hgl]; simp only [ite_eq_right hrev]
    rw [hB]
    iapply HΦ
    iapply Hpack _ s' (pinit ++ [pl] ++ [e]) (by simp [hBe, hil])
    simp only
    iframe Heb Hs Hcap
    rw [hBe, List.zip_append (by simp [hil]), List.zip_append hil]
    simp only [List.zip_cons_cons, List.zip_nil_left]
    iapply BigSepL.bigSepL_snoc.2
    iframe He
    iapply BigSepL.bigSepL_snoc.2
    iframe Hevs Hl


end proof

end EtcdGrove
end Perennial
