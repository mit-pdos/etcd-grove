/-
Proof of `Spec/Cache__get.lean`. Lean-first (no Rocq counterpart).

The client's prefix get (`isEtcdKV`, linearizable from the revision bound, which etcd has reached:
`cacheBound`), then `store.Restore` with the response's key-values, at or above every revision the
store can be at (the bound, raised to the response's revision first: `cacheBound_le`):
the response lists etcd's state at its revision, sorted by key, so restoring it (inserting the
entries one by one into an empty tree) gives back the same map (`restoreMap_sorted`).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Cache__get
public import Spec.go_etcd_io.etcd.cache.v3.store__Restore
public import Spec.go_etcd_io.etcd.client.v3.WithPrefix

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

/-- Inserting an entry above every entry of a map appends it. -/
theorem btInsert_kvLess_append (e : KvEntry) :
    ∀ (acc : KvMap), (∀ a ∈ acc, kvLess a e) → btInsert kvLess e acc = acc ++ [e]
  | [], _ => rfl
  | a :: acc, h => by
    have ha : kvLess a e := h a List.mem_cons_self
    simp only [btInsert, ha, ↓reduceIte, List.cons_append]
    rw [btInsert_kvLess_append e acc (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem foldl_btInsert_sorted :
    ∀ (rest acc : KvMap), (acc ++ rest).Pairwise kvLess →
      rest.foldl (fun m e => btInsert kvLess e m) acc = acc ++ rest
  | [], acc, _ => by simp
  | e :: rest, acc, h => by
    have hlt : ∀ a ∈ acc, kvLess a e := by
      intro a ha
      exact List.pairwise_append.1 h |>.2.2 a ha e List.mem_cons_self
    simp only [List.foldl_cons]
    rw [btInsert_kvLess_append e acc hlt, foldl_btInsert_sorted rest (acc ++ [e])
      (by simpa using h)]
    simp

/-- Restoring a map sorted by key gives it back. -/
theorem restoreMap_sorted (m : KvMap) (h : m.Pairwise kvLess) : restoreMap m = m := by
  unfold restoreMap
  simpa using foldl_btInsert_sorted m [] (by simpa using h)

/-- The cache's get is a range. -/
theorem opGetModel_withPrefix_t (pfx : GoString) :
    (opGetModel pfx [withPrefixM]).t = W64 1 := by
  simp only [opGetModel, opFold, List.foldl, withPrefixM, OpFull.getInit]
  by_cases h : pfx = [] <;> simp [h]

/-- The cache's prefix get is a prefix get. -/
theorem opGetModel_withPrefix_isPrefixGet (pfx : GoString) :
    (opGetModel pfx [withPrefixM]).isPrefixGet pfx = true := by
  by_cases h : pfx = []
  · subst h
    simp [opGetModel, opFold, withPrefixM, OpFull.getInit, OpFull.newOp, OpModel.zero,
      OpFull.isPrefixGet]
  · simp [opGetModel, opFold, withPrefixM, OpFull.getInit, OpFull.newOp, OpModel.zero,
      OpFull.isPrefixGet, h]

/-- The cache's prefix get is not serializable (so it is linearizable). -/
theorem opGetModel_withPrefix_serializable (pfx : GoString) :
    (opGetModel pfx [withPrefixM]).base.serializable = false := by
  by_cases h : pfx = []
  · subst h
    simp [opGetModel, opFold, withPrefixM, OpFull.getInit, OpFull.newOp, OpModel.zero]
  · simp [opGetModel, opFold, withPrefixM, OpFull.getInit, OpFull.newOp, OpModel.zero, h]

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- A map that is etcd's state has its `*KeyValue`s' keys (`kvsAt`), and is sorted. -/
theorem isEtcdKvs_kvsAt (r : w64) (pfx : GoString) (m : KvMap) :
    isEtcdKvs (GF := GF) r pfx m ⊢ kvsAt m ∗ ⌜m.Pairwise kvLess⌝ := by
  unfold isEtcdKvs
  iintro ⟨%s, -, %Hk, %Hwf, #Hv⟩
  isplitl []
  · unfold kvsAt kvValsAt
    imodintro
    iintro %e %He
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 He
    have hk : (m.map Prod.fst)[i]? = (s.map EtcdKv.key)[i]? := by rw [Hk]
    rw [List.getElem?_map, List.getElem?_map, hi] at hk
    cases hs : s[i]? with
    | none => rw [hs] at hk; cases hk
    | some v =>
      rw [hs] at hk
      simp only [Option.map_some, Option.some.injEq] at hk
      ihave #Hval := Hv $$ %i %e %v %hi %hs
      iunfold kvValAt at Hval
      icases Hval with ⟨%keySl, %valSl, #HK, #HKs, -⟩
      unfold kvAt
      iexists keySl
      iframe HK
      rw [hk]
      iexact HKs
  · ipureintro
    have h1 : (m.map Prod.fst).Pairwise go.GoStringLt := by rw [Hk]; exact Hwf.1
    exact (List.pairwise_map (f := Prod.fst) (R := go.GoStringLt)).1 h1

/-- With the revision bound's authority at `r`, no revision the store can be at is above `r`. -/
theorem cacheBound_dom (cf : CacheFields) (r : w64) (hr : 0 ≤ sint.Z r) :
    ∀ x : w64, (monoNatAuthOwn (GF := GF) cf.γb 1 (sint.nat r) ∗ cacheRev cf x ⊢
      ⌜sint.Z x ≤ sint.Z r⌝) := by
  intro x
  unfold cacheRev cacheBoundLb
  iintro ⟨Ha, -, (%H | #H)⟩
  · ipureintro; omega
  · ihave %Hv := monoNatLbOwn_valid $$ Ha H
    ipureintro
    have h2 := Hv.2
    by_cases h0 : 0 ≤ sint.Z x
    · have e1 : ((sint.nat x : Nat) : Int) = sint.Z x := Int.toNat_of_nonneg h0
      have e2 : ((sint.nat r : Nat) : Int) = sint.Z r := Int.toNat_of_nonneg hr
      omega
    · omega

theorem Cache.get.wp_proof
    (wp_WithPrefix : WithPrefix.spec (GF := GF) (hG := hG))
    (wp_Restore : store.Restore.spec (GF := GF) (hG := hG)) :
    Cache.get.spec (GF := GF) (hG := hG) := by
  intro c cf γr γd cap ctx s B
  wp_start as ⟨#Hc, #Hctx, Hb⟩
  iunfold cacheBound at Hb
  icases Hb with ⟨Ha, #HRB, %HB0⟩
  ihave #Hcl : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  unfold isCacheFields
  iNamed Hc
  wp_auto
  wp_apply wp_WithPrefix as %f1 #Hf1
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  ipersist Hsl
  wp_auto
  generalize hsl : slice.mk sl _ _ = optsSl
  ihave #Hopts : optsAt optsSl ([withPrefixM] : List (OpFull → OpFull)) $$ []
  · iunfold optsAt
    iexists _
    iframe Hsl
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %f %g %Hf %Hg
    rcases i with _ | i
    · cases Hf; cases Hg; iexact Hf1
    · simp at Hf
  iunfold isEtcdKV at HisKV
  ihave #HG := HisKV $$ %ctx %s %cf.pfx %optsSl %([withPrefixM] : List (OpFull → OpFull)) %B
  wp_apply HG $$ [] as %resp %err #Hres
  · iframe Hctx Hopts HRB
    ipureintro
    refine ⟨?_, opGetModel_withPrefix_t cf.pfx⟩
    rintro ⟨-, h⟩
    simp [opFold, withPrefixM, OpFull.newOp] at h
  iunfold kvGetResult at Hres
  icases Hres with (%Herr | ⟨%Herr, %r, %m, #Hrev, #Hm, #Hreach, %Hle0, Hkvs⟩)
  · obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
      cases err with
      | nil => exact absurd rfl Herr
      | ok e => exact ⟨e, rfl⟩
    wp_auto
    iapply HΦ
    ileft
    isplitr
    · ipureintro; exact ⟨rfl, Herr⟩
    iunfold cacheBound
    iframe Ha HRB
    ipureintro; exact HB0
  · subst Herr
    rw [ite_eq_left (opGetModel_withPrefix_isPrefixGet cf.pfx)]
    have Hle : sint.Z B ≤ sint.Z r ∧ sint.Z r < 2 ^ 63 - 1 :=
      ⟨Hle0.1 (opGetModel_withPrefix_serializable cf.pfx), Hle0.2⟩
    have Hr0 : 0 ≤ sint.Z r := by omega
    iunfold getRespRev at Hrev
    icases Hrev with ⟨%hdr, #Hh, %Hnn, #Hr⟩
    iunfold getRespKvs at Hkvs
    icases Hkvs with ⟨%kvsSl, #HKs, #HKsl⟩
    icases isEtcdKvs_kvsAt r cf.pfx m $$ Hm with ⟨#HkvsAt, %Hsorted⟩
    -- raise the revision bound to `r`
    imod mono_nat_own_update (sint.nat r) (Int.toNat_le_toNat Hle.1) $$ Ha with ⟨Ha, #Hlbr⟩
    ihave #HRr : cacheRev cf r $$ []
    · unfold cacheRev cacheBoundLb
      iframe Hreach
      iright; iexact Hlbr
    wp_auto
    wp_apply wp_Restore cf.store cf.γs cf.scap (etcdCert cf.pfx) (cacheRev cf)
      (monoNatAuthOwn cf.γb 1 (sint.nat r)) kvsSl m DFrac.discard r
      $$ [$HisStore $HisStoreW $HKsl $HkvsAt $Ha] as ⟨-, Ha, #Hlb, #Hslb⟩
    · isplitr
      · ipureintro; exact cacheBound_dom cf r Hr0
      isplitr
      · imodintro
        unfold etcdCert
        rw [restoreMap_sorted m Hsorted]
        iexact Hm
      iexact HRr
    iapply HΦ
    iright
    isplitr
    · ipureintro; rfl
    iexists r
    isplitr
    · iunfold getRespRev
      iexists hdr
      iframe Hh Hr
      ipureintro; exact Hnn
    iframe Hlb Hslb
    isplitl [Ha]
    · iunfold cacheBound
      iframe Ha Hreach
      ipureintro; exact Hr0
    ipureintro; exact Hle

end proof

end EtcdGrove
end Perennial
