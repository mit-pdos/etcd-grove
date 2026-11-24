/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/RaftCluster__MemberIDs.lean`
(claim #34, stage 2, 2026-11-25). Lean-first.

The cluster's mutex locked and unlocked owned (`OwnedMutex.lean`); the members map's range appends
each member's id, which is its key (`memIdsOk`; the loop's invariant: the ids so far are the first
keys of the range's order); `sort.Sort` over `types.IDSlice` (a `sorterSpec` of the ids, ordered
unsigned) permutes them into ascending order, strictly, as the keys are distinct (`idsSorted`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__MemberIDs
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.IDSlice__Len
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.IDSlice__Less
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.IDSlice__Swap
public import Spec.sort.Sort
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.OwnedMutex

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

/-- The unsigned order of ids is a strict weak order. -/
theorem membership.w64Lt_swo :
    slices.StrictWeakOrder (fun a b : w64 => decide (uint.Z a < uint.Z b) = true) := by
  simp only [decide_eq_true_eq]
  exact {
    strict_weak_order_irrefl := fun _ => Int.lt_irrefl _
    strict_weak_order_trans := fun _ _ _ h1 h2 => Int.lt_trans h1 h2
    strict_weak_order_equiv := {
      refl := fun _ => ⟨Int.lt_irrefl _, Int.lt_irrefl _⟩
      symm := fun h => ⟨h.2, h.1⟩
      trans := fun h1 h2 => ⟨by omega, by omega⟩ } }

/-- **A sorted permutation of the keys is `idsSorted`**: distinct, the keys, strictly ascending. -/
theorem membership.idsSorted_of_sort (mem : GMap w64 apply.MemberM) (keys l' : List w64)
    (hk : ∀ k, k ∈ keys ↔ (mem !! k).isSome) (hnd : keys.Nodup) (hp : keys.Perm l')
    (hs : ∀ (i j : Nat) (a b : w64), l'[i]? = some a → l'[j]? = some b → i < j →
      decide (uint.Z b < uint.Z a) = false) :
    membership.idsSorted mem l' := by
  have hnd' : l'.Nodup := hp.nodup_iff.1 hnd
  refine ⟨hnd', fun k => (hp.mem_iff).symm.trans (hk k), ?_⟩
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have h := hs i j l'[i] l'[j] (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hj) hij
  have hne : l'[i] ≠ l'[j] := by
    intro he
    have := (hnd'.getElem_inj).1 he
    omega
  have hne' : l'[i].toNat ≠ l'[j].toNat := fun he => hne (BitVec.eq_of_toNat_eq he)
  simp only [decide_eq_false_iff_not, uint.Z] at h
  omega

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `IDSlice` over the slice `sl` sorts the ids it holds, unsigned. -/
theorem membership.sorter_ids
    (hLen : types.IDSlice.Len.spec (GF := GF) (hG := hG))
    (hLess : types.IDSlice.Less.spec (GF := GF) (hG := hG))
    (hSwap : types.IDSlice.Swap.spec (GF := GF) (hG := hG)) (sl : GoSlice) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types ⊢
      sorterSpec (interface.mk go_etcd_io.etcd.client.pkg.v3.types.IDSlice.ty #sl)
        (fun l : List w64 => (sl ↦* l : IProp GF)) (fun a b => decide (uint.Z a < uint.Z b)) := by
  iintro #Hpkg
  unfold sorterSpec
  isplitr
  · imodintro
    iintro %l
    iintro !> %Φ Hs HΦ
    wp_apply (hLen sl l (DFrac.own 1)) $$ [$Hs] as Hs
    iapply HΦ
    iexact Hs
  isplitr
  · imodintro
    iintro %l %i %j %a %b %Hij
    iintro !> %Φ Hs HΦ
    obtain ⟨hi, hj, ha, hb⟩ := Hij
    wp_apply (hLess sl l (DFrac.own 1) i j a b hi hj ha hb) $$ [$Hs] as Hs
    iapply HΦ
    iexact Hs
  imodintro
  iintro %l %i %j %a %b %Hij
  iintro !> %Φ Hs HΦ
  obtain ⟨hi, hj, ha, hb⟩ := Hij
  wp_apply (hSwap sl l i j a b hi hj ha hb) $$ [$Hs] as Hs
  iapply HΦ
  iexact Hs

theorem membership.RaftCluster.MemberIDs.wp_proof
    (hSort : sort.«Sort».spec (GF := GF) (hG := hG))
    (hLen : types.IDSlice.Len.spec (GF := GF) (hG := hG))
    (hLess : types.IDSlice.Less.spec (GF := GF) (hG := hG))
    (hSwap : types.IDSlice.Swap.spec (GF := GF) (hG := hG)) :
    membership.RaftCluster.MemberIDs.spec (GF := GF) (hG := hG) := by
  intro c q ms mem hids hsz
  wp_start as ⟨Hmu, Hmem⟩
  iunfold membership.memAt at Hmem
  icases Hmem with ⟨%mp, Hfl, Hmap, %Hdom, Hmems⟩
  (try wp_auto)
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock_owned $$ [$Hmu] as Hmu
  (try wp_auto)
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (K := w64) (V := Loc) (fun (keys : List w64) (i : Int) => iprop(
      ∃ (sl' : GoSlice) (x : Loc),
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "ids" ∷ ids_ptr ↦ sl' ∗
      "Hsl" ∷ sl' ↦* keys.take i.toNat ∗
      "Hcap" ∷ ownSliceCap w64 sl' (DFrac.own 1) ∗
      "Hmems" ∷ ([∗map] k ↦ m ∈ ms, membership.memberAt m q ((mem !! k).getD default)) ∗
      "m" ∷ m_ptr ↦ x)) $$ Hmap
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [ids m Hmems]
  · iexists slice.nil, zero_val Loc
    simp only [named, Int.toNat_zero, List.take_zero]
    iframe ids m Hmems
    isplitl []
    · ipureintro; omega
    isplitl []
    · iapply ownSlice_nil
    iapply ownSliceCap_nil
  isplitr
  · imodintro
    iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
    iNamed HP
    (try wp_auto)
    icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF)
      (Φ := fun (k : w64) (m : Loc) => membership.memberAt (GF := GF) m q
        ((mem !! k).getD default)) Hvv).1 $$ Hmems
      with ⟨Hown, Hmclose⟩
    -- the member's id is its key
    have hkid : ((mem !! key).getD default).id = key := by
      have hs : (mem !! key).isSome := by rw [← Hdom.1 key, Hvv]; rfl
      obtain ⟨mm, hmm⟩ := Option.isSome_iff_exists.1 hs
      rw [hmm]
      exact hids key mm hmm
    iunfold membership.memberAt at Hown
    icases Hown with ⟨%Hnn, %pu, %cu, Hid, Hpu, Hil, Hnm, Hcu, Hpus, Hcus⟩
    rw [hkid]
    (try wp_auto)
    wp_apply wp_slice_literal (V := w64) [key]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    (try wp_auto)
    wp_apply wp_slice_append (V := w64) _ _ _ _ _ $$ [$Hsl $Hcap $Hsl2] as %sl3 ⟨Hsl, Hcap, -⟩
    (try wp_auto)
    ihave Hmems := Hmclose $$ [Hid Hpu Hil Hnm Hcu Hpus Hcus]
    · iunfold membership.memberAt
      rw [hkid]
      isplitr
      · ipureintro; exact Hnn
      iexists pu, cu
      iframe
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists sl3, vv
    simp only [named]
    have htake : keys.take i.toNat ++ [key] = keys.take (i + 1).toNat := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey]
      rfl
    rw [htake]
    iframe ids Hsl Hcap Hmems m
    ipureintro; omega
  iintro HP Hmap
  iNamed HP
  (try wp_auto)
  have hkeys : keys.take (GMap.size ms : Int).toNat = keys := by
    simp [← Hklen]
  rw [hkeys]
  ihave #Htypes : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types $$ []
  · iPkgInit
  ihave #Hpsort : isPkgInit (PROP := IProp GF) pkg_id.sort $$ []
  · iPkgInit
  ihave #Hsorter := membership.sorter_ids hLen hLess hSwap sl' $$ Htypes
  wp_apply (hSort w64 _ (fun l : List w64 => (sl' ↦* l : IProp GF))
      (fun a b => decide (uint.Z a < uint.Z b)) keys membership.w64Lt_swo) $$ [Hsl]
      as %l' ⟨Hsl, %Hl'⟩
  · iframe #
    iframe Hsl
    ipureintro
    rw [Hklen]; exact hsz
  (try wp_auto)
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock_owned $$ [$Hmu] as Hmu
  (try wp_auto)
  iapply HΦ
  iframe Hmu
  isplitl [Hfl Hmap Hmems]
  · iunfold membership.memAt
    iexists mp
    iframe
    ipureintro; exact Hdom
  iexists l'
  iframe Hsl
  ipureintro
  refine ⟨membership.idsSorted_of_sort mem keys l' ?_ Hknodup Hl'.1 Hl'.2, ?_⟩
  · intro k
    rw [Hkset k, Hdom.1 k]
  · rw [← Hl'.1.length_eq, Hklen]

end proof

end EtcdGrove
end Perennial
