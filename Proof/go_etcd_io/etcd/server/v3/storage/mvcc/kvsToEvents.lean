/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.kvsToEvents
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.isTombstone
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.BytesToRev
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherGroup__contains
public import Spec.google_golang_org.protobuf.proto.Unmarshal

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- A bucket key's tombstone mark decodes back. -/
theorem mvcc.isTomb_revBytes_self (r : mvcc.Rev) (t : Bool) : mvcc.isTomb (mvcc.revBytes r t) = t := by
  cases t
  · have h := mvcc.isTomb_revBytes r []
    rw [List.append_nil] at h; rw [h]; decide
  · rw [mvcc.revBytes_true, mvcc.isTomb_revBytes]; simp

set_option maxHeartbeats 4000000 in
theorem mvcc.kvsToEvents.wp_proof
    (hUnm : proto.Unmarshal.spec (GF := GF) (hG := hG))
    (hTomb : mvcc.isTombstone.spec (GF := GF) (hG := hG))
    (hB2R : mvcc.BytesToRev.spec (GF := GF) (hG := hG))
    (hCont : mvcc.watcherGroup.contains.spec (GF := GF) (hG := hG)) :
    mvcc.kvsToEvents.spec (GF := GF) (hG := hG) := by
  intro lg g W revs vals ents
  wp_start as ⟨Hg, #Hpv, %Hbnd⟩
  iunfold mvcc.pairVals at Hpv
  icases Hpv with ⟨%kss, %vss, #Hks, #Hvs, %Hlens, #Hel⟩
  wp_auto
  rename_i igo
  irename : (igo ↦ zero_val w64 : IProp GF) => Higo
  have hlen1 : kss.length = ents.length := by simpa using Hlens.1
  have hlen2 : vss.length = ents.length := by simpa using Hlens.2
  ihave %Hvl := ownSlice_len _ _ _ $$ Hvs
  ihave %Hkl := ownSlice_len _ _ _ $$ Hks
  ihave IH : iprop(∃ (n k : w64) (vv es : GoSlice) (ps : List Loc),
      "i" ∷ i_ptr ↦ n ∗ "Higo" ∷ igo ↦ k ∗ "v" ∷ v_ptr ↦ vv ∗ "evs" ∷ evs_ptr ↦ es ∗
      "Hes" ∷ es ↦* ps ∗ "Hcap" ∷ ownSliceCap Loc es (DFrac.own 1) ∗
      "Hg" ∷ mvcc.ownWatcherGroup g W ∗
      "Hdone" ∷ ([∗list] x ∈ ps.zip (mvcc.entsEvents W (ents.take (sint.nat n))), mvcc.evIs x.1 x.2) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ ents.length ∧
        ps.length = (mvcc.entsEvents W (ents.take (sint.nat n))).length⌝) $$ [i Higo v evs Hg]
  · iexists W64 0, _, _, _, []
    simp only [named]
    iframe i Higo v evs Hg
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    rw [show sint.nat (W64 0) = 0 from rfl]
    simp only [List.take_zero, List.zip_nil_left]
    isplitl []
    · iapply BigSepL.bigSepL_nil_intro; iempintro
    ipureintro; refine ⟨by decide, by simp, by simp [mvcc.entsEvents]⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < ents.length := by rw [← hlen2, Hvl.1]; word
    have Hbnd2 : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z vals.len := ⟨Hn.1, Hif⟩
    simp only [Hbnd2, and_self, ↓reduceIte]
    obtain ⟨e, He⟩ : ∃ e, ents[sint.nat n]? = some e := ⟨_, List.getElem?_eq_getElem Hlt⟩
    icases (BigSepL.bigSepL_lookup_acc (List.getElem?_map ▸ (by rw [He]; rfl :
        (ents[sint.nat n]?).map mvcc.KvEnt.pair = some e.pair))).1 $$ Hel
      with ⟨⟨%ksl, %vsl, %Hkv, #Hksl, #Hvsl⟩, -⟩
    wp_apply wp_load_slice_index vals (sint.Z n) vss DFrac.discard vsl Hn.1 $$ [$Hvs] as -
    · ipureintro; exact Hkv.2
    simp only [mvcc.KvEnt.pair]
    wp_apply (hUnm vsl e.kv «$r0_ptr» _ DFrac.discard) $$ [$Hvsl $«$r0»]
      as ⟨-, %ks', %vs', %st, %uf, %sc, Hp, #Hks', #Hvs'⟩
    ihave %Hpnn := typedPointsto_not_null _ _ _ $$ Hp
    iStructNamedPrefix Hp "K"
    (try wp_auto)
    wp_apply wp_bytes_to_string ks' e.kv.key DFrac.discard $$ [$Hks'] as -
    (try wp_auto)
    wp_apply (hCont g W e.kv.key) $$ [$Hg] as Hg
    have hcv : (open Classical in decide (∃ w r, W !! w = some r ∧ r.covers e.kv.key = true)) =
        mvcc.wgCovers W e.kv.key := rfl
    rw [hcv]
    have hsnoc : mvcc.entsEvents W (ents.take (sint.nat n + 1)) =
        mvcc.entsEvents W (ents.take (sint.nat n)) ++
          (if mvcc.wgCovers W e.kv.key then [e.ev] else []) := by
      rw [List.take_add_one, He]
      have hkey : e.ev.kv.key = e.kv.key := by unfold mvcc.KvEnt.ev; split <;> rfl
      unfold mvcc.entsEvents
      simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil,
        List.filter_append, List.filter_cons, List.filter_nil, hkey]
    have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    cases hc : mvcc.wgCovers W e.kv.key
    · -- no member covers the key: skipped
      simp only [Bool.not_false]
      (try wp_auto)
      wp_for_post
      iframe
      iexists n + W64 1, n, vsl, es, ps
      rw [hn1, hsnoc, hc]
      simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
      iframe
      ipureintro; exact ⟨by word, by omega, Hn.2.2⟩
    · simp only [Bool.not_true]
      (try wp_auto)
      simp only [go_etcd_io.etcd.api.v3.mvccpb.Event_PUT]
      (try wp_auto)
      have Hbr : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z revs.len := by
        refine ⟨Hn.1, ?_⟩; have := Hkl.1; rw [hlen1] at this; word
      simp only [Hbr, and_self, ↓reduceIte]
      wp_apply wp_load_slice_index revs (sint.Z n) kss DFrac.discard ksl Hn.1 $$ [$Hks] as -
      · ipureintro; exact Hkv.1
      wp_apply (hTomb ksl (mvcc.revBytes e.rev e.tomb) DFrac.discard) $$ [$Hksl] as -
      rw [mvcc.isTomb_revBytes_self]
      cases ht : e.tomb
      · (try wp_auto)
        have hev : e.ev = ⟨false, e.kv, none⟩ := by unfold mvcc.KvEnt.ev; rw [ht]; rfl
        ihave Hpk : («$r0_ptr» ↦
            ({ state' := st, Key' := ks', CreateRevision' := e.kv.createRev,
               ModRevision' := e.kv.modRev, Version' := e.kv.version, Value' := vs',
               Lease' := e.kv.lease, unknownFields' := uf, sizeCache' := sc } :
              go_etcd_io.etcd.api.v3.mvccpb.KeyValue) : IProp GF) $$
            [Kstate KKey KCreateRevision KModRevision KVersion KValue KLease KunknownFields KsizeCache]
        · iapply typedPointsto_combine _ _ _ Hpnn
          simp only [TypedPointsto.typedPointstoDef]
          iframe
        ihave %Henn := typedPointsto_not_null _ _ _ $$ «$sl0»
        ipersist Hpk
        ipersist «$sl0»
        ihave #Hev : mvcc.evIs «$sl0_ptr» e.ev $$ []
        · rw [hev]
          iunfold mvcc.evIs
          iexists «$r0_ptr», null, _, slice.nil, _
          simp only [mvcc.evType, Bool.false_eq_true, ↓reduceIte]
          iframe «$sl0»
          isplitr
          · ipureintro; exact ⟨Henn, Hpnn⟩
          isplitr
          · iunfold mvcc.kvPtrFixed
            iexists ks', vs', st, uf, sc
            iframe Hks' Hvs' Hpk
          first | (ipureintro; rfl) | (ipureintro; trivial) | itrivial
        wp_apply wp_slice_literal (V := Loc) [«$sl0_ptr»]
        isplitr
        · ipureintro; rfl
        iintro %asl ⟨Hasl, -⟩
        (try wp_auto)
        wp_apply wp_slice_append es ps _ [«$sl0_ptr»] (DFrac.own 1) $$ [$Hes $Hcap $Hasl]
          as %es' ⟨Hes, Hcap, -⟩
        (try wp_auto)
        wp_for_post
        iframe
        iexists n + W64 1, n, vsl, es', ps ++ [«$sl0_ptr»]
        rw [hn1, hsnoc, hc]
        simp only [↓reduceIte]
        iframe
        isplitl [Hdone]
        · rw [List.zip_append (by rw [Hn.2.2])]
          simp only [List.zip_cons_cons, List.zip_nil_left]
          iapply (BigSepL.bigSepL_snoc (PROP := IProp GF)).2
          iframe Hdone Hev
        ipureintro; exact ⟨by word, by omega, by simp [Hn.2.2]⟩
      · simp only [go_etcd_io.etcd.api.v3.mvccpb.Event_DELETE]
        (try wp_auto)
        simp only [Hbr, and_self, ↓reduceIte]
        wp_apply wp_load_slice_index revs (sint.Z n) kss DFrac.discard ksl Hn.1 $$ [$Hks] as -
        · ipureintro; exact Hkv.1
        rw [mvcc.revBytes_true]
        have hb := Hbnd e (List.mem_of_getElem? He)
        wp_apply (hB2R ksl e.rev [mvcc.markTomb] DFrac.discard (by simp) hb.1 hb.2) $$ [$Hksl] as -
        (try wp_auto)
        have hev : e.ev = ⟨true, { e.kv with modRev := e.rev.main }, none⟩ := by unfold mvcc.KvEnt.ev; rw [ht]; rfl
        ihave Hpk : («$r0_ptr» ↦
            ({ state' := st, Key' := ks', CreateRevision' := e.kv.createRev,
               ModRevision' := e.rev.main, Version' := e.kv.version, Value' := vs',
               Lease' := e.kv.lease, unknownFields' := uf, sizeCache' := sc } :
              go_etcd_io.etcd.api.v3.mvccpb.KeyValue) : IProp GF) $$
            [Kstate KKey KCreateRevision KModRevision KVersion KValue KLease KunknownFields KsizeCache]
        · iapply typedPointsto_combine _ _ _ Hpnn
          simp only [TypedPointsto.typedPointstoDef]
          iframe
        ihave %Henn := typedPointsto_not_null _ _ _ $$ «$sl0»
        ipersist Hpk
        ipersist «$sl0»
        ihave #Hev : mvcc.evIs «$sl0_ptr» e.ev $$ []
        · rw [hev]
          iunfold mvcc.evIs
          iexists «$r0_ptr», null, _, slice.nil, _
          simp only [mvcc.evType, ↓reduceIte]
          iframe «$sl0»
          isplitr
          · ipureintro; exact ⟨Henn, Hpnn⟩
          isplitr
          · iunfold mvcc.kvPtrFixed
            iexists ks', vs', st, uf, sc
            iframe Hks' Hvs' Hpk
          first | (ipureintro; rfl) | (ipureintro; trivial) | itrivial
        wp_apply wp_slice_literal (V := Loc) [«$sl0_ptr»]
        isplitr
        · ipureintro; rfl
        iintro %asl ⟨Hasl, -⟩
        (try wp_auto)
        wp_apply wp_slice_append es ps _ [«$sl0_ptr»] (DFrac.own 1) $$ [$Hes $Hcap $Hasl]
          as %es' ⟨Hes, Hcap, -⟩
        (try wp_auto)
        wp_for_post
        iframe
        iexists n + W64 1, n, vsl, es', ps ++ [«$sl0_ptr»]
        rw [hn1, hsnoc, hc]
        simp only [↓reduceIte]
        iframe
        isplitl [Hdone]
        · rw [List.zip_append (by rw [Hn.2.2])]
          simp only [List.zip_cons_cons, List.zip_nil_left]
          iapply (BigSepL.bigSepL_snoc (PROP := IProp GF)).2
          iframe Hdone Hev
        ipureintro; exact ⟨by word, by omega, by simp [Hn.2.2]⟩
  · have hge : ¬ sint.Z n < sint.Z vals.len := by
      first | exact Hif | exact fun h => Hif (by rw [decide_eq_true h])
    have hnl : sint.nat n = ents.length := by
      have h1 := Hvl.1; rw [hlen2] at h1; have := Hn.2.1; word
    rw [hnl, List.take_length] at Hn
    rw [hnl, List.take_length]
    iapply HΦ
    iframe
    ipureintro; exact Hn.2.2

end proof

end EtcdGrove
end Perennial
