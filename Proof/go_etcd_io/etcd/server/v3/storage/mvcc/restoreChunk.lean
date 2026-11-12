/-
Proof of `Spec/.../mvcc/restoreChunk.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.restoreChunk
public import Spec.google_golang_org.protobuf.proto.Unmarshal
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.isTombstone

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.restoreChunk.wp_proof
    (hUnm : proto.Unmarshal.spec (GF := GF) (hG := hG))
    (hTomb : mvcc.isTombstone.spec (GF := GF) (hG := hG)) :
    mvcc.restoreChunk.spec (GF := GF) (hG := hG) := by
  intro lg kvc mp keys vals ents Rd Tok γ P R sent Q M
  wp_start as ⟨#Hpv, #Hrc, Htok, Hmp, #Hsp, Hprod, HQ, #Hob⟩
  iunfold mvcc.pairVals at Hpv
  icases Hpv with ⟨%kss, %vss, #Hks, #Hvs, %Hlens, #Hel⟩
  wp_auto
  rename_i igo
  irename : (igo ↦ zero_val w64 : IProp GF) => Higo
  have hlen1 : kss.length = ents.length := by simpa using Hlens.1
  have hlen2 : vss.length = ents.length := by simpa using Hlens.2
  ihave %Hvl := ownSlice_len _ _ _ $$ Hvs
  ihave %Hkl := ownSlice_len _ _ _ $$ Hks
  ihave IH : iprop(∃ (n k : w64) (kk : GoSlice) (new : List revKeyValue),
      "i" ∷ i_ptr ↦ n ∗ "Higo" ∷ igo ↦ k ∗ "key" ∷ key_ptr ↦ kk ∗
      "Htok" ∷ Tok ∗ "Hmp" ∷ mp ↦$ mvcc.ktlApply M (ents.take (sint.nat n)) ∗
      "Hprod" ∷ spscProducer γ (sent ++ new) ∗
      "HQ" ∷ ([∗list] j ↦ e ∈ ents.drop (sint.nat n), Q (sint.nat n + j) e) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ ents.length ∧ new.length = sint.nat n⌝)
      $$ [i Higo key Htok Hmp Hprod HQ]
  · iexists W64 0, _, _, []
    simp only [named, List.append_nil]
    rw [show sint.nat (W64 0) = 0 from rfl]
    simp only [List.drop_zero, Nat.zero_add, List.take_zero, mvcc.ktlApply_nil]
    iframe i Higo key Htok Hmp Hprod
    iframe HQ
    ipureintro; refine ⟨by decide, by simp, by simp⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < ents.length := by rw [← hlen1, Hkl.1]; word
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z keys.len := ⟨Hn.1, Hif⟩
    simp only [Hbnd, and_self, ↓reduceIte]
    obtain ⟨e, He⟩ : ∃ e, ents[sint.nat n]? = some e := ⟨_, List.getElem?_eq_getElem Hlt⟩
    icases (BigSepL.bigSepL_lookup_acc (List.getElem?_map ▸ (by rw [He]; rfl :
        (ents[sint.nat n]?).map mvcc.KvEnt.pair = some e.pair))).1 $$ Hel
      with ⟨⟨%ksl, %vsl, %Hkv, #Hksl, #Hvsl⟩, -⟩
    -- the range value: `keys[n]`
    wp_apply wp_load_slice_index keys (sint.Z n) kss DFrac.discard ksl Hn.1 $$ [$Hks] as -
    · ipureintro; exact Hkv.1
    (try wp_auto)
    -- `proto.Unmarshal(vals[i], kv)`
    have Hbv : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z vals.len := by
      refine ⟨Hn.1, ?_⟩; have := Hvl.1; rw [hlen2] at this; word
    simp only [Hbv, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index vals (sint.Z n) vss DFrac.discard vsl Hn.1 $$ [$Hvs] as -
    · ipureintro; exact Hkv.2
    simp only [mvcc.KvEnt.pair]
    iunfold mvcc.rdCap at Hrc
    icases Hrc $$ %vsl %(mvcc.kvEncode e.kv) Hvsl Htok with ⟨%dqv, Hvb, Hvback⟩
    wp_apply (hUnm vsl e.kv «$r0_ptr» _ dqv) $$ [$Hvb $«$r0»]
      as ⟨Hvb, %ks', %vs', %st, %uf, %sc, Hp, #Hks', #Hvs'⟩
    ihave Htok := Hvback $$ Hvb
    ihave %Hpnn := typedPointsto_not_null _ _ _ $$ Hp
    iStructNamedPrefix Hp "K"
    (try wp_auto)
    -- `rkv.kstr = string(rkv.kv.Key)`
    wp_apply wp_bytes_to_string ks' e.kv.key DFrac.discard $$ [$Hks'] as -
    (try wp_auto)
    -- `isTombstone(key)`
    icases Hrc $$ %ksl %(mvcc.revBytes e.rev e.tomb) Hksl Htok with ⟨%dqk, Hkb, Hkback⟩
    wp_apply (hTomb ksl (mvcc.revBytes e.rev e.tomb) dqk) $$ [$Hkb] as Hkb
    ihave Htok := Hkback $$ Hkb
    rw [mvcc.isTomb_revBytes_self]
    have hstep : mvcc.ktlApply M (ents.take (sint.nat n + 1)) =
        mvcc.ktlStep (mvcc.ktlApply M (ents.take (sint.nat n))) e := by
      rw [List.take_succ, He]; exact mvcc.ktlApply_snoc _ _ _
    cases ht : e.tomb
    · -- not a tombstone: the lease, if any, is recorded
      (try wp_auto)
      ihave Hkvp : iprop(«$r0_ptr» ↦ mvcc.kvMsgOf st ks' vs' uf sc e.kv) $$
          [Kstate KKey KCreateRevision KModRevision KVersion KValue KLease KunknownFields KsizeCache]
      · iapply (typedPointsto_combine _ _ _ Hpnn)
        simp only [TypedPointsto.typedPointstoDef, mvcc.kvMsgOf]
        iframe
      by_cases hl : e.kv.lease = W64 0
      · simp only [hl, decide_true, Bool.not_true]
        (try wp_auto)
        wp_apply (wp_mapDelete mp _ e.kv.key go.string
          go_etcd_io.etcd.server.v3.lease.LeaseID.ty) $$ [$Hmp] as Hmp
        ihave Hmp : iprop(mp ↦$ mvcc.ktlApply M (ents.take (sint.nat n + 1))) $$ [Hmp]
        · rw [hstep]; unfold mvcc.ktlStep; simp only [ht, hl, Bool.false_eq_true, ↓reduceIte, if_true, if_false]; iexact Hmp
        (try wp_auto)
        -- the entry's restored form, and the protocol's `P` for it
        have hdrop : ents.drop (sint.nat n) = e :: ents.drop (sint.nat n + 1) := by
          rw [List.drop_eq_getElem_cons Hlt, (List.getElem?_eq_some_iff.1 He).2]
        rw [hdrop]
        icases (BigSepL.bigSepL_cons).1 $$ HQ with ⟨HQe, HQ⟩
        ihave Hrkv : mvcc.rkvIs Rd ⟨ksl, «$r0_ptr», e.kv.key⟩ e $$ [Hkvp]
        · iunfold mvcc.rkvIs
          rw [ht]
          iframe Hksl
          isplitr
          · ipureintro; rfl
          iexists ks', vs', uf, st, sc
          iframe Hkvp Hks' Hvs'
        ihave HP := Hob $$ %(sint.nat n) %e %(revKeyValue.mk ksl «$r0_ptr» e.kv.key) %He HQe Hrkv
        have hlenS : ((sent ++ new).length : Int) = (sent.length : Int) + (sint.nat n : Int) := by
          rw [List.length_append, Hn.2.2]; push_cast; rfl
        try simp only
        ihave HP' : iprop(P (sent ++ new).length ⟨ksl, «$r0_ptr», e.kv.key⟩) $$ [HP]
        · rw [hlenS]; iexact HP
        wp_apply (wp_spsc_send γ kvc P R (sent ++ new) ⟨ksl, «$r0_ptr», e.kv.key⟩)
          $$ [$Hsp $Hprod $HP'] as Hprod
        wp_for_post
        iframe
        iexists n + W64 1, n, ksl, new ++ [⟨ksl, «$r0_ptr», e.kv.key⟩]
        simp only [named, List.append_assoc]
        have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
        rw [hn1]
        iframe
        isplitl [HQ]
        · iapply (BigSepL.bigSepL_mono (fun {j _} _ => by
            rw [show sint.nat n + 1 + j = sint.nat n + (j + 1) by omega])) $$ HQ
        ipureintro
        refine ⟨by word, by omega, ?_⟩
        rw [List.length_append, Hn.2.2]; rfl
      · simp only [hl, decide_false, Bool.not_false]
        (try wp_auto)
        wp_apply (wp_mapInsert go.string mp _ e.kv.key e.kv.lease) $$ [$Hmp] as Hmp
        ihave Hmp : iprop(mp ↦$ mvcc.ktlApply M (ents.take (sint.nat n + 1))) $$ [Hmp]
        · rw [hstep]; unfold mvcc.ktlStep; simp only [ht, hl, Bool.false_eq_true, ↓reduceIte, if_true, if_false]; iexact Hmp
        (try wp_auto)
        -- the entry's restored form, and the protocol's `P` for it
        have hdrop : ents.drop (sint.nat n) = e :: ents.drop (sint.nat n + 1) := by
          rw [List.drop_eq_getElem_cons Hlt, (List.getElem?_eq_some_iff.1 He).2]
        rw [hdrop]
        icases (BigSepL.bigSepL_cons).1 $$ HQ with ⟨HQe, HQ⟩
        ihave Hrkv : mvcc.rkvIs Rd ⟨ksl, «$r0_ptr», e.kv.key⟩ e $$ [Hkvp]
        · iunfold mvcc.rkvIs
          rw [ht]
          iframe Hksl
          isplitr
          · ipureintro; rfl
          iexists ks', vs', uf, st, sc
          iframe Hkvp Hks' Hvs'
        ihave HP := Hob $$ %(sint.nat n) %e %(revKeyValue.mk ksl «$r0_ptr» e.kv.key) %He HQe Hrkv
        have hlenS : ((sent ++ new).length : Int) = (sent.length : Int) + (sint.nat n : Int) := by
          rw [List.length_append, Hn.2.2]; push_cast; rfl
        try simp only
        ihave HP' : iprop(P (sent ++ new).length ⟨ksl, «$r0_ptr», e.kv.key⟩) $$ [HP]
        · rw [hlenS]; iexact HP
        wp_apply (wp_spsc_send γ kvc P R (sent ++ new) ⟨ksl, «$r0_ptr», e.kv.key⟩)
          $$ [$Hsp $Hprod $HP'] as Hprod
        wp_for_post
        iframe
        iexists n + W64 1, n, ksl, new ++ [⟨ksl, «$r0_ptr», e.kv.key⟩]
        simp only [named, List.append_assoc]
        have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
        rw [hn1]
        iframe
        isplitl [HQ]
        · iapply (BigSepL.bigSepL_mono (fun {j _} _ => by
            rw [show sint.nat n + 1 + j = sint.nat n + (j + 1) by omega])) $$ HQ
        ipureintro
        refine ⟨by word, by omega, ?_⟩
        rw [List.length_append, Hn.2.2]; rfl
    · -- a tombstone: `delete`
      ihave Hkvp : iprop(«$r0_ptr» ↦ mvcc.kvMsgOf st ks' vs' uf sc e.kv) $$
          [Kstate KKey KCreateRevision KModRevision KVersion KValue KLease KunknownFields KsizeCache]
      · iapply (typedPointsto_combine _ _ _ Hpnn)
        simp only [TypedPointsto.typedPointstoDef, mvcc.kvMsgOf]
        iframe
      (try wp_auto)
      wp_apply (wp_mapDelete mp _ e.kv.key go.string
        go_etcd_io.etcd.server.v3.lease.LeaseID.ty) $$ [$Hmp] as Hmp
      ihave Hmp : iprop(mp ↦$ mvcc.ktlApply M (ents.take (sint.nat n + 1))) $$ [Hmp]
      · rw [hstep]; unfold mvcc.ktlStep; simp only [ht, ↓reduceIte]; iexact Hmp
      (try wp_auto)
      -- the entry's restored form, and the protocol's `P` for it
      have hdrop : ents.drop (sint.nat n) = e :: ents.drop (sint.nat n + 1) := by
        rw [List.drop_eq_getElem_cons Hlt, (List.getElem?_eq_some_iff.1 He).2]
      rw [hdrop]
      icases (BigSepL.bigSepL_cons).1 $$ HQ with ⟨HQe, HQ⟩
      ihave Hrkv : mvcc.rkvIs Rd ⟨ksl, «$r0_ptr», e.kv.key⟩ e $$ [Hkvp]
      · iunfold mvcc.rkvIs
        rw [ht]
        iframe Hksl
        isplitr
        · ipureintro; rfl
        iexists ks', vs', uf, st, sc
        iframe Hkvp Hks' Hvs'
      ihave HP := Hob $$ %(sint.nat n) %e %(revKeyValue.mk ksl «$r0_ptr» e.kv.key) %He HQe Hrkv
      have hlenS : ((sent ++ new).length : Int) = (sent.length : Int) + (sint.nat n : Int) := by
        rw [List.length_append, Hn.2.2]; push_cast; rfl
      try simp only
      ihave HP' : iprop(P (sent ++ new).length ⟨ksl, «$r0_ptr», e.kv.key⟩) $$ [HP]
      · rw [hlenS]; iexact HP
      wp_apply (wp_spsc_send γ kvc P R (sent ++ new) ⟨ksl, «$r0_ptr», e.kv.key⟩)
        $$ [$Hsp $Hprod $HP'] as Hprod
      wp_for_post
      iframe
      iexists n + W64 1, n, ksl, new ++ [⟨ksl, «$r0_ptr», e.kv.key⟩]
      simp only [named, List.append_assoc]
      have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
      rw [hn1]
      iframe
      isplitl [HQ]
      · iapply (BigSepL.bigSepL_mono (fun {j _} _ => by
          rw [show sint.nat n + 1 + j = sint.nat n + (j + 1) by omega])) $$ HQ
      ipureintro
      refine ⟨by word, by omega, ?_⟩
      rw [List.length_append, Hn.2.2]; rfl
  · -- every key sent
    have Heq : sint.nat n = ents.length := by
      have := Hkl.1; rw [hlen1] at this; word
    (try wp_for_post)
    iapply HΦ
    rw [List.take_of_length_le (by omega : ents.length ≤ sint.nat n)]
    iframe Htok Hmp
    iexists new
    iframe Hprod
    ipureintro; rw [Hn.2.2, Heq]

end proof

end EtcdGrove
end Perennial
