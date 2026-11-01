/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/Lease__Keys.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.Lease__Keys
public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- The keys of the item set `S`, as `Keys()`'s loop collects them. -/
theorem keys_of_set {ks : List GoString} {S : GMap LeaseItem Unit} {keys : List LeaseItem}
    (Hkset : ∀ it, it ∈ keys ↔ (S.lookup it).isSome = true) (Hknodup : keys.Nodup)
    (Hks : ks = keys.map LeaseItem.Key') :
    (∀ k : GoString, k ∈ ks ↔ S.lookup ⟨k⟩ = some ()) ∧ ks.Nodup := by
  subst Hks
  constructor
  · intro k
    rw [List.mem_map]
    constructor
    · rintro ⟨it, hit, rfl⟩
      have h := (Hkset it).1 hit
      cases it
      revert h; cases S.lookup _ <;> simp
    · intro h
      exact ⟨LeaseItem.mk k, (Hkset _).2 (by rw [h]; rfl), rfl⟩
  · unfold List.Nodup at Hknodup ⊢
    rw [List.pairwise_map]
    refine Hknodup.imp (fun {a b} hab heq => hab ?_)
    cases a; cases b; simp only at heq; rw [heq]

theorem lease.Lease.Keys.wp_proof : lease.Lease.Keys.spec (GF := GF) (hG := hG) := by
  intro γl l id K
  wp_start as ⟨#Hlo, Hpre⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  cases K with
  | owner I =>
  rw [keysPre_owner]
  icases Hpre with ⟨Hio, Hslot⟩
  wp_auto
  wp_apply (sync.RWMutex.wp_RLock (lsF go!"mu" l) (leaseItems γl l)) $$ [$Hslot] as ⟨Hlk, HR⟩
  iunfold leaseItems at HR
  icases HR with ⟨%sm, %S, %γr, #Hpr, Hsm, HS, He⟩
  iunfold leaseItemsOwn at Hio
  icases Hio with ⟨%sm', %S0, Hsm', HS', %HSI⟩
  icombine Hsm Hsm' gives %Hsmeq
  subst Hsmeq
  ihave %HSeq := ownMap_agree sm _ _ S S0 $$ [$HS $HS']
  subst HSeq
  wp_auto
  wp_apply (wp_map_len_lt sm S _) $$ [$HS] as ⟨HS, %Hsz⟩
  wp_apply (wp_slice_make3 (V := GoString) (W64 0) (W64 (GMap.size S : Int)) ⟨by word, by word⟩)
    as %sl0 ⟨Hsl0, Hcap0, -⟩
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_map_for_range (fun (keys : List LeaseItem) (i : Int) => iprop(∃ (x : LeaseItem)
      (sl : GoSlice),
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "k" ∷ k_ptr ↦ x ∗
      "keys" ∷ keys_ptr ↦ sl ∗
      "Hsl" ∷ sl ↦* ((keys.take i.toNat).map LeaseItem.Key') ∗
      "Hcap" ∷ ownSliceCap GoString sl (DFrac.own 1)))) $$ HS
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [k keys Hsl0 Hcap0]
  · iexists _, sl0
    simp only [named]
    iframe
    ipureintro; exact Int.le_refl _
  isplitr
  · imodintro
    iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
    iNamed HP
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %lit ⟨Hlit, -⟩
    wp_apply wp_slice_append $$ [$Hsl $Hcap $Hlit] as %sl' ⟨Hsl, Hcap, -⟩
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists key, sl'
    simp only [named]
    iframe
    have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega]
      rw [List.take_add_one, Hkey]; rfl
    rw [Htake, List.map_append, List.map_singleton]
    iframe
    ipureintro; omega
  iintro HP HS
  iNamed HP
  rw [Int.toNat_natCast, ← Hklen, List.take_length]
  wp_auto
  wp_apply (sync.RWMutex.wp_RUnlock (lsF go!"mu" l) (leaseItems γl l)) $$ [$Hlk Hsm HS He] as Hslot
  · inext; iunfold leaseItems; iexists sm, S, γr; iframe; iframe #
  have Hk := keys_of_set Hkset Hknodup rfl
  iapply HΦ
  iframe Hsl Hslot
  rw [keysPost_owner]
  isplitl [Hsm' HS']
  · iunfold leaseItemsOwn; iexists sm, S; iframe; ipureintro; exact HSI
  ipureintro
  refine ⟨fun k => ?_, Hk.2⟩
  rw [Hk.1 k]
  exact HSI ⟨k⟩
  | reader m =>
  rw [keysPre_reader]
  icases Hpre with ⟨#Hlive, Htt, %Hb⟩
  iunfold isLeaseObj at Hlo
  icases Hlo with ⟨%Hnn, #Hguard, #Hrd, #Hpool⟩
  icases Hpool $$ %Hb with ⟨%γp, #Hpool⟩
  iapply fupd_wp
  imod threadPool.borrow leasePoolN γp (sync.ownRWMutex (lsF go!"mu" l) (leaseItems γl l)) ⊤ (fun _ _ => CoPset.mem_full) $$ [Hpool Htt]
    with ⟨Hslot, Hloan⟩
  · iframe #; iframe
  imodintro
  wp_auto
  wp_apply (sync.RWMutex.wp_RLock (lsF go!"mu" l) (leaseItems γl l)) $$ [$Hslot] as ⟨Hlk, HR⟩
  iunfold leaseItems at HR
  icases HR with ⟨%sm, %S, %γr, #Hpr, Hsm, HS, He⟩
  iapply fupd_wp
  imod itemSet_keysFrom γl γr l _ S m id ⊤ (fun _ _ => CoPset.mem_full) $$ [$Hrd $Hpr $Hlive $He]
    with ⟨He, %i, %σ, %Hσ, #Hat⟩
  imodintro
  wp_auto
  wp_apply (wp_map_len_lt sm S _) $$ [$HS] as ⟨HS, %Hsz⟩
  wp_apply (wp_slice_make3 (V := GoString) (W64 0) (W64 (GMap.size S : Int)) ⟨by word, by word⟩)
    as %sl0 ⟨Hsl0, Hcap0, -⟩
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_map_for_range (fun (keys : List LeaseItem) (i : Int) => iprop(∃ (x : LeaseItem)
      (sl : GoSlice),
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "k" ∷ k_ptr ↦ x ∗
      "keys" ∷ keys_ptr ↦ sl ∗
      "Hsl" ∷ sl ↦* ((keys.take i.toNat).map LeaseItem.Key') ∗
      "Hcap" ∷ ownSliceCap GoString sl (DFrac.own 1)))) $$ HS
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [k keys Hsl0 Hcap0]
  · iexists _, sl0
    simp only [named]
    iframe
    ipureintro; exact Int.le_refl _
  isplitr
  · imodintro
    iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
    iNamed HP
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %lit ⟨Hlit, -⟩
    wp_apply wp_slice_append $$ [$Hsl $Hcap $Hlit] as %sl' ⟨Hsl, Hcap, -⟩
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists key, sl'
    simp only [named]
    iframe
    have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega]
      rw [List.take_add_one, Hkey]; rfl
    rw [Htake, List.map_append, List.map_singleton]
    iframe
    ipureintro; omega
  iintro HP HS
  iNamed HP
  rw [Int.toNat_natCast, ← Hklen, List.take_length]
  wp_auto
  iapply wp_fupd
  wp_apply (sync.RWMutex.wp_RUnlock (lsF go!"mu" l) (leaseItems γl l)) $$ [$Hlk Hsm HS He] as Hslot
  · inext; iunfold leaseItems; iexists sm, S, γr; iframe; iframe #
  imod threadPool.giveBack leasePoolN γp (sync.ownRWMutex (lsF go!"mu" l) (leaseItems γl l)) ⊤ (fun _ _ => CoPset.mem_full) $$ [Hpool Hloan Hslot]
    with Htt
  · iframe #; iframe
  imodintro
  have Hk := keys_of_set Hkset Hknodup rfl
  iapply HΦ
  iframe Hsl Htt
  rw [keysPost_reader]
  isplitr
  · iframe #; ipureintro; exact Hb
  isplitr
  · iunfold leaseKeysFrom
    iexists i, σ
    iframe #
    ipureintro
    refine ⟨Hσ.1, Hσ.2.1, fun k => ?_, Hσ.2.2.2⟩
    rw [Hk.1 k]
    exact Hσ.2.2.1 ⟨k⟩
  ipureintro; exact Hk.2

end proof

end EtcdGrove
end Perennial
