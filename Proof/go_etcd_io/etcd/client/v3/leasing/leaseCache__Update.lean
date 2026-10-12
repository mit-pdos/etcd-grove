/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leaseCache__Update.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__Update
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeaseCacheLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem leaseCache.Update.wp_proof : leaseCache.Update.spec (GF := GF) (hG := hG) := by
  intro lc st keySl key valSl val h hm
  wp_start as ⟨Hown, %Hwf, #Hkey, #Hval, #Hh⟩
  rw [lcOwn_def]
  icases Hown with ⟨Hentries, Hemap, Hrv, Hrmap, Hhdr, #HhdrOk, Hents, #Hfrozen⟩
  wp_auto
  wp_apply wp_bytes_to_string $$ [$Hkey] as -
  wp_apply wp_entries_lookup st _ key Hwf $$ [$Hemap] as Hemap
  cases hk : st.entries !! key with
  | none =>
    simp only [Option.map_none, Option.getD_none]
    wp_auto
    iapply HΦ
    iexists null, slice.nil
    rw [modify_none key _ st hk, lcOwn_def]
    iframe
    iframe #
  | some e =>
    have hli : e.li ≠ null := Hwf.li_ne key e hk
    simp only [Option.map_some, Option.getD_some]
    icases (BigSepM.bigSepM_insert_acc hk) $$ Hents with ⟨He, Hback⟩
    rw [entryOwn_def, respOwn_def]
    icases He with ⟨%-, Hr, Hrev, Hwc, ⟨%Hrnn, Hhd, #Hehd, Hkvs, Hsl, Hcap, Hkv, Hmore, Hcount⟩, #Hw⟩
    rw [decide_eq_false hli]
    rw [hdrFull_def h]
    icases Hh with ⟨%Hhnn, #Hh1, #Hh2, #Hh3, #Hh4, #Hh5⟩
    wp_auto
    ihave %Hlen := ownSlice_len $$ Hsl
    -- the first key-value exists afterwards: the cached one, or a fresh one appended
    wp_join iprop(∃ (p : Loc) (sl' : GoSlice),
        structFieldRef etcdserverpb.RangeResponse go!"Kvs" e.resp ↦
          (e.upd1 (freshKv p keySl key hm.revision) sl').kvsSl ∗
        (e.upd1 (freshKv p keySl key hm.revision) sl').kvsSl ↦*
          ((e.upd1 (freshKv p keySl key hm.revision) sl').kvs.map CachedKv.p) ∗
        ownSliceCap Loc (e.upd1 (freshKv p keySl key hm.revision) sl').kvsSl (DFrac.own 1) ∗
        ([∗list] c ∈ (e.upd1 (freshKv p keySl key hm.revision) sl').kvs,
          cachedKvOwn c (DFrac.own 1)) ∗
        structFieldRef etcdserverpb.RangeResponse go!"Count" e.resp ↦
          (e.upd1 (freshKv p keySl key hm.revision) sl').count ∗
        cacheResp_ptr ↦ e.resp ∗ respHeader_ptr ↦ h ∗ key_ptr ↦ keySl)
      with [Hkvs Hsl Hcap Hkv Hcount respHeader key cacheResp] as ⟨%p, %sl', Hkvs, Hsl, Hcap, Hkv, Hcount, cacheResp, respHeader, key⟩
    · have hkvs : e.kvs = [] := by
        have h0 := Hlen.1; rw [Hif] at h0
        rw [List.length_map] at h0
        exact List.length_eq_zero_iff.mp (by rw [h0]; rfl)
      wp_apply wp_slice_literal (l := [«$r0_ptr»])
      isplitr
      · ipureintro; rfl
      iintro %slp ⟨Hlit, -⟩
      wp_auto
      rw [hkvs]
      wp_apply wp_slice_append $$ [$Hsl $Hcap $Hlit] as %sl' ⟨Hsl', Hcap', -⟩
      isplitr
      · ipureintro; rfl
      iexists «$r0_ptr», sl'
      simp only [LeaseEntry.upd1, hkvs, ↓reduceIte, List.map_cons, List.map_nil, List.nil_append]
      iframe
      ihave %Hpnn := typedPointsto_not_null $$ «$r0»
      iStructNamed «$r0»
      rw [cachedKvOwn_def]
      simp only [freshKv, BigSepL.bigSepL_cons, BigSepL.bigSepL_nil]
      iframe
      iframe #
      isplitr
      · ipureintro; exact Hpnn
      iapply ownSlice_nil
    · have hne : e.kvs ≠ [] := by
        intro h0; rw [h0] at Hlen; apply Hif
        have := Hlen.1; simp at this; word
      iexists null, slice.nil
      simp only [LeaseEntry.upd1, hne, ↓reduceIte]
      iframe
    have hne1 : (e.upd1 (freshKv p keySl key hm.revision) sl').kvs ≠ [] := by
      unfold LeaseEntry.upd1; split <;> simp_all
    have hsame : ∀ x : LeaseEntry, x = e.upd1 (freshKv p keySl key hm.revision) sl' →
        x.li = e.li ∧ x.resp = e.resp ∧ x.rev = e.rev ∧ x.waitc = e.waitc ∧ x.hdr = e.hdr ∧
        x.hm = e.hm ∧ x.more = e.more ∧ x.lease = e.lease ∧ x.acq = e.acq := by
      intro x hx; subst hx; unfold LeaseEntry.upd1; split <;> simp
    generalize he1 : e.upd1 (freshKv p keySl key hm.revision) sl' = e1 at hne1 ⊢
    obtain ⟨c0, cs, hc⟩ : ∃ c0 cs, e1.kvs = c0 :: cs := by
      cases h1 : e1.kvs with
      | nil => exact absurd h1 hne1
      | cons c0 cs => exact ⟨c0, cs, rfl⟩
    rw [hc]
    icases Hkv with ⟨Hc0, Hcs⟩
    rw [cachedKvOwn_def c0]
    icases Hc0 with ⟨%Hc0nn, HcK, #HcKb, HcC, HcM, HcV, HcVal, #HcValb, HcL⟩
    ihave %Hlen1 := ownSlice_len $$ Hsl
    have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z e1.kvsSl.len := by
      have := Hlen1.1; simp only [List.map_cons, List.length_cons] at this; word
    wp_pures
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ _ c0.p (by word) $$ [Hsl] as Hsl
    · iframe; ipureintro; rfl
    wp_pures
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ _ c0.p (by word) $$ [Hsl] as Hsl
    · iframe; ipureintro; rfl
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ _ c0.p (by word) $$ [Hsl] as Hsl
    · iframe; ipureintro; rfl
    obtain ⟨hs_li, hs_resp, hs_rev, hs_wc, hs_hdr, hs_hm, hs_more, hs_lease, hs_acq⟩ :=
      hsame e1 he1.symm
    have hli' : ∀ x : LeaseEntry,
        (x.update (freshKv p keySl key hm.revision) sl' h hm valSl val).li = x.li :=
      fun x => (update_fields x _ sl' h hm valSl val).1
    wp_if_destruct
    · simp only [hb, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ _ c0.p (by word) $$ [Hsl] as Hsl
      · iframe; ipureintro; rfl
      wp_auto
      simp only [hb, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ _ c0.p (by word) $$ [Hsl] as Hsl
      · iframe; ipureintro; rfl
      iapply HΦ
      iexists p, sl'
      iapply lcOwn_modify_intro lc st key _ e _ hk hli'
      iframe
      iframe #
      iapply Hback
      rw [update_upd1, he1, hc]
      simp only [Hif, ↓reduceIte]
      rw [entryOwn_def, respOwn_def]
      simp only [hs_li, hs_resp, hs_rev, hs_wc, hs_more, hs_hdr, hs_hm, List.map_cons]
      unfold CachedKv.bump
      simp only [Hif, ↓reduceIte]
      iframe
      iframe #
      try rw [hdrFull_def h]
      rw [cachedKvOwn_def]
      simp only
      iframe
      iframe #
      ipureintro
      first | exact ⟨hli, Hrnn, Hhnn, Hc0nn⟩ | exact ⟨hli, Hrnn, Hc0nn⟩
    · iapply HΦ
      iexists p, sl'
      iapply lcOwn_modify_intro lc st key _ e _ hk hli'
      iframe
      iframe #
      iapply Hback
      rw [update_upd1, he1, hc]
      simp only [Hif, ↓reduceIte]
      rw [entryOwn_def, respOwn_def]
      simp only [hs_li, hs_resp, hs_rev, hs_wc, hs_more, hs_hdr, hs_hm, List.map_cons]
      unfold CachedKv.bump
      simp only [Hif, ↓reduceIte]
      iframe
      iframe #
      try rw [hdrFull_def h]
      rw [cachedKvOwn_def]
      simp only
      iframe
      iframe #
      ipureintro
      first | exact ⟨hli, Hrnn, Hhnn, Hc0nn⟩ | exact ⟨hli, Hrnn, Hc0nn⟩

end proof

end leasing
end EtcdGrove
end Perennial
