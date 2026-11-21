/-
The sort of a lessor's leases by expiry (`sort.Sort(leasesByExpiry(ls))`, in `Leases` and `Promote`):
`leasesByExpiry` over a slice of the lessor's leases is a `sorterAnySpec` that permutes them
(`Less` reads the clock, with the level-0 token, so no order is stated); and the persistent facts
of the lock's lease map, read off a list of its pairs. Moved out of `lessor__Leases.lean`
(prove-ps2-promote, 2026-11-21) so that `Promote`'s proof applies them too.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.leasesByExpiry__Len
public import Spec.go_etcd_io.etcd.server.v3.lease.leasesByExpiry__Less
public import Spec.go_etcd_io.etcd.server.v3.lease.leasesByExpiry__Swap
public import Spec.sort.SortAnyLess
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- What `leasesByExpiry`, a sorter over the slice `sl`, holds: the pointers of `l`, a permutation
of `ls0`, and the level-0 token of the leases' pools (for `Less`'s `Remaining()`). -/
def lease.sorterR (sl : GoSlice) (ls0 : List (Loc × w64)) (l : List (Loc × w64)) : IProp GF :=
  iprop(sl ↦* l.map Prod.fst ∗ levelTok leaseLvl ∗ ⌜l.Perm ls0⌝)

/-- `leasesByExpiry` over the slice `sl` permutes the (pointer, id) list `ls0` of leases. -/
theorem lease.sorter_byExpiry
    (hLen : lease.leasesByExpiry.Len.spec (GF := GF) (hG := hG))
    (hLess : lease.leasesByExpiry.Less.spec (GF := GF) (hG := hG))
    (hSwap : lease.leasesByExpiry.Swap.spec (GF := GF) (hG := hG))
    (γl : GName) (sl : GoSlice) (ls0 : List (Loc × w64)) (hb : threadBound GF ≤ 2 ^ 30 - 1) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
      ([∗list] p ∈ ls0.map Prod.fst, isLeaseObj γl p) ⊢
      sorterAnySpec (interface.mk leasesByExpiry.ty #sl) (lease.sorterR sl ls0) := by
  iintro ⟨#Hpkg, #Hls⟩
  unfold sorterAnySpec lease.sorterR
  isplitr
  · imodintro
    iintro %l
    iintro !> %Φ ⟨Hs, Ht, %Hp⟩ HΦ
    wp_apply (hLen sl (l.map Prod.fst) (DFrac.own 1)) $$ [$Hs] as Hs
    rw [List.length_map]
    iapply HΦ
    iframe
    ipureintro; exact Hp
  isplitr
  · imodintro
    iintro %l %i %j %a %b %Hij
    iintro !> %Φ ⟨Hs, Ht, %Hp⟩ HΦ
    obtain ⟨hi, hj, ha, hb'⟩ := Hij
    ihave #Hl : [∗list] p ∈ l.map Prod.fst, isLeaseObj (GF := GF) γl p $$ [Hls]
    · iapply (BigSepL.bigSepL_perm (PROP := IProp GF) (Φ := fun p => isLeaseObj (GF := GF) γl p)
        (Hp.map Prod.fst)).2
      iexact Hls
    wp_apply (hLess γl sl (l.map Prod.fst) (DFrac.own 1) i j a.1 b.1) $$ [$Hs $Hl $Ht] as %r ⟨Hs, Ht⟩
    · ipureintro
      refine ⟨hb, hi, hj, ?_, ?_⟩
      · rw [List.getElem?_map, ha]; rfl
      · rw [List.getElem?_map, hb']; rfl
    iapply HΦ
    iframe
    ipureintro; exact Hp
  imodintro
  iintro %l %i %j %a %b %Hij
  iintro !> %Φ ⟨Hs, Ht, %Hp⟩ HΦ
  obtain ⟨hi, hj, ha, hb'⟩ := Hij
  have hp : l.Perm ((l.set (sint.nat i) b).set (sint.nat j) a) :=
    slices.swap_perm l (sint.nat j) (sint.nat i) b a hb' ha
  wp_apply (hSwap sl (l.map Prod.fst) i j a.1 b.1) $$ [$Hs] as Hs
  · ipureintro
    refine ⟨hi, hj, ?_, ?_⟩
    · rw [List.getElem?_map, ha]; rfl
    · rw [List.getElem?_map, hb']; rfl
  iapply HΦ
  rw [List.map_set, List.map_set]
  iframe Hs Ht
  ipureintro; exact hp.symm.trans Hp

/-- The `ID` facts of the lock's `leaseMeta`s (persistent). -/
theorem lease.leaseMeta_ids (M : GMap w64 Loc) (q : Qp) :
    ([∗map] id ↦ l ∈ M, leaseMeta (GF := GF) id l q) ⊢
      ([∗map] id ↦ l ∈ M, leaseMeta id l q) ∗ [∗map] id ↦ l ∈ M, lsF go!"ID" l ↦□ id := by
  rw [← BigSepM.bigSepM_sep_eq]
  apply BigSepM.bigSepM_mono
  intro k v _
  iintro H
  iunfold leaseMeta at H
  icases H with ⟨#Hid, Ht, Hc, Hr, He, #Hg⟩
  isplitl [Ht Hc Hr He]
  · iunfold leaseMeta; iframe Hid Hg Ht Hc Hr He
  iexact Hid

/-- A persistent map's facts, for a list of its pairs. -/
theorem lease.bigSepM_pairs {P : w64 → Loc → IProp GF} [∀ k v, Persistent (P k v)]
    (M : GMap w64 Loc) (ls : List (Loc × w64))
    (h : ∀ (id : w64) (l : Loc), (l, id) ∈ ls ↔ M.lookup id = some l) :
    ([∗map] id ↦ l ∈ M, P id l) ⊢ [∗list] x ∈ ls, P x.2 x.1 := by
  iintro #H
  have key : □ ([∗map] id ↦ l ∈ M, P id l) ⊢ [∗list] x ∈ ls, P x.2 x.1 := by
    apply BigSepL.bigSepL_intro
    intro k x hk
    refine intuitionistically_elim.trans ?_
    exact BigSepM.bigSepM_lookup ((h x.2 x.1).1 (List.mem_of_getElem? hk))
  iapply key
  imodintro
  iexact H

end lemmas

end EtcdGrove
end Perennial
