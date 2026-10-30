module
public import Spec.go_etcd_io.bbolt.internal.freelist.hashMap__mergeWithExistingSpan
public import Spec.go_etcd_io.bbolt.internal.freelist.hashMap__delSpan
public import Spec.go_etcd_io.bbolt.internal.freelist.hashMap__addSpan
public import Proof.go_etcd_io.bbolt.internal.freelist.HashMergeLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

theorem hashMap.mergeWithExistingSpan.wp_proof (hDel : hashMap.delSpan.spec (GF := GF) (hG := hG))
    (hAdd : hashMap.addSpan.spec (GF := GF) (hG := hG)) :
    hashMap.mergeWithExistingSpan.spec (GF := GF) (hG := hG) := by
  intro h s free start e Hle H1 Hge1 Hdis Hlen
  wp_start as Hown
  unfold ownHashPart hmRaw
  icases Hown with ⟨%cnt, %sp, %bwm, %sets, ⟨%fm, %fw, %bw, %FM, Hraw⟩, %Hok⟩
  obtain ⟨Hinv0, Hend0⟩ := mInv_init Hle H1 Hdis
  iNamed Hraw
  wp_auto
  wp_apply wp_map_lookup2 $$ [Hbw] as Hbw
  · iexact Hbw
  try wp_auto
  wp_apply wp_map_lookup2 $$ [Hfw] as Hfw
  · iexact Hfw
  try wp_auto
  have Hfnd : free.Nodup := Hok.2.1.1.nodup
  -- the span after the merged ids does not start at `0`: `e+1` does not wrap around
  have Hnext : ∀ q, sp !! (e + W64 1) = some q → uint.Z (e + W64 1) = uint.Z e + 1 := by
    intro q hq
    have := Hge1 _ (span_mem Hok.2.1 hq (hm_inRun_self (by have := (Hok.1.1 _ q hq).1; word)))
    word
  wp_join iprop(∃ (cnt1 : w64) (sp1 bwm1 : GMap w64 w64) (sets1 : GMap w64 (GMap w64 Unit))
      (f1 : List w64) (ns nsz : w64),
      hmRaw h cnt1 sp1 bwm1 sets1 ∗ newStart_ptr ↦ ns ∗ newSize_ptr ↦ nsz ∗ f_ptr ↦ h ∗
      ⌜hashOK cnt1 sp1 bwm1 sets1 f1 ∧ mInv free start (uint.nat (e - start) + 1) f1 ns nsz ∧
        uint.Z ns + uint.Z nsz = uint.Z e + 1 ∧ 1 ≤ uint.Z ns ∧
        (∀ q, sp !! (e + W64 1) = some q → sp1 !! (e + W64 1) = some q)⌝)
    with [Hcnt Hfmf Hfwf Hbwf Hfm Hsets Hbw Hfw newStart newSize f prev preSize]
    as ⟨%cnt1, %sp1, %bwm1, %sets1, %f1, %ns, %nsz, Hraw, newStart, newSize, f, %H1ok⟩
  · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 Hif
    rw [hp, Option.getD_some]
    obtain ⟨Hsp, Hlt, Hinv1, Hend1⟩ := merge_prev Hok Hinv0 hp H1 Hge1
    try wp_auto
    wp_apply (hDel h cnt sp bwm sets free _ p Hok Hsp) $$ [Hcnt Hfmf Hfwf Hbwf Hfm Hsets Hbw Hfw]
      as Hraw
    · unfold hmRaw; iexists fm, fw, bw, FM; simp only [named]; iframe
    try wp_auto
    wp_join_done
    have hps : start - W64 1 + W64 1 - p = start - p := by word
    rw [hps] at Hsp Hlt ⊢
    have hns1 : 1 ≤ uint.Z (start - p) :=
      Hge1 _ (span_mem Hok.2.1 Hsp (hm_inRun_self (by have := (Hok.1.1 _ p Hsp).1; word)))
    rw [hps] at Hinv1
    iexists _, _, _, _, _, (start - p), (e - start + W64 1 + p)
    iframe
    ipureintro
    refine ⟨hashOK_del Hok Hsp _ (Hok.2.1.1.filter _) (fun x => mem_filter_not x), Hinv1,
      by omega, hns1, fun q hq => ?_⟩
    have := Hnext q hq
    rw [GMap.lookup_delete_ne _ (by intro h'; rw [← h'] at this; omega)]
    exact hq
  · iexists _, _, _, _, free, start, (e - start + W64 1)
    unfold hmRaw
    iframe
    ipureintro
    exact ⟨Hok, Hinv0, Hend0, H1, fun q hq => hq⟩
  wp_join iprop(∃ (cnt2 : w64) (sp2 bwm2 : GMap w64 w64) (sets2 : GMap w64 (GMap w64 Unit))
      (f2 : List w64) (nsz2 : w64),
      hmRaw h cnt2 sp2 bwm2 sets2 ∗ newSize_ptr ↦ nsz2 ∗ f_ptr ↦ h ∗
      ⌜hashOK cnt2 sp2 bwm2 sets2 f2 ∧ mInv free start (uint.nat (e - start) + 1) f2 ns nsz2⌝)
    with [Hraw newSize f next nextSize]
    as ⟨%cnt2, %sp2, %bwm2, %sets2, %f2, %nsz2, Hraw, newSize, f, %H2ok⟩
  · obtain ⟨Hok1, Hinv1, Hend1, Hns1, Hsp1⟩ := H1ok
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 Hif
    rw [hq, Option.getD_some]
    have hq1 := Hsp1 q hq
    try wp_auto
    wp_apply (hDel h cnt1 sp1 bwm1 sets1 f1 _ q Hok1 hq1) $$ [Hraw] as Hraw
    · iframe
    try wp_auto
    wp_join_done
    iexists _, _, _, _, _, (nsz + q)
    iframe
    ipureintro
    exact ⟨hashOK_del Hok1 hq1 _ (Hok1.2.1.1.filter _) (fun x => mem_filter_not x),
      merge_next Hok1 Hinv1 Hend1 Hns1 hq1 Hge1⟩
  · obtain ⟨Hok1, Hinv1, -⟩ := H1ok
    iexists _, _, _, _, f1, nsz
    iframe
    ipureintro
    exact ⟨Hok1, Hinv1⟩
  obtain ⟨Hok2, Hinv2⟩ := H2ok
  wp_apply (hAdd h cnt2 sp2 bwm2 sets2 ns nsz2) $$ [Hraw] as Hraw
  · iframe
  try wp_auto
  have Hnw : uint.Z start + ↑(uint.nat (e - start) + 1) ≤ 2 ^ 64 := by word
  have Hfin := merge_final Hok2 Hinv2 Hfnd Hlen Hnw Hdis
  iapply HΦ
  isplitr
  · ipureintro; exact sortIds_perm _
  iexists _, _, _, _
  isplitl [Hraw]
  · iunfold hmRaw at Hraw; iexact Hraw
  ipureintro; exact Hfin

end proof

end bbolt
end EtcdGrove
end Perennial
