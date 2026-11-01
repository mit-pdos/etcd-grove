/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/lessor__Leases.lean`. Lean-first (no Rocq
counterpart); the lease-read plan (2026-10-31).

Under the read lock, `unsafeLeases` copies the lease map's pairs into a fresh slice; the lock's
`isLeaseObj` and `leaseMeta` give each lease's facts, its history the index of the map, its
persistent receipt `⧖ |M|` the bound on the slice's length (`|M| < receiptBound GF ≤ 2^62`).
`sort.Sort` over `leasesByExpiry` (a `sorterAnySpec` of the (pointer, id) list: `Less` reads the
clock, so no order is stated) permutes the pairs.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Leases
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__unsafeLeases
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

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- What `leasesByExpiry`, a sorter over the slice `sl`, holds: the pointers of `l`, a permutation
of `ls0`, and a thread token (for `Less`'s `Remaining()`). -/
def lease.sorterR (sl : GoSlice) (ls0 : List (Loc × w64)) (l : List (Loc × w64)) : IProp GF :=
  iprop(sl ↦* l.map Prod.fst ∗ threadTok ∗ ⌜l.Perm ls0⌝)

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

theorem lease.lessor.Leases.wp_proof
    (hUL : lease.lessor.unsafeLeases.spec (GF := GF) (hG := hG))
    (hSort : sort.«Sort».anyLessSpec (GF := GF) (hG := hG))
    (hLen : lease.leasesByExpiry.Len.spec (GF := GF) (hG := hG))
    (hLess : lease.leasesByExpiry.Less.spec (GF := GF) (hG := hG))
    (hSwap : lease.leasesByExpiry.Swap.spec (GF := GF) (hG := hG)) :
    lease.lessor.Leases.spec (GF := GF) (hG := hG) := by
  intro lp γl m
  wp_start as ⟨#Hinv, Hrd, #Hlb, Htt, %Hb, %Hrb⟩
  iunfold lessorInv at Hinv
  icases Hinv with ⟨%Hlp, #Hpin, #Hmu, #Hrdi⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold lessorRd at Hrd
  wp_auto
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hlk, HR⟩
  iunfold lessorMu at HR
  icases HR with ⟨%lm, %im, %M, %I', %rd0, %L', Hlm, HM, Him, HI, Hrdf, Ha, Hg, %HL, #Hsz, #Hls, Hx,
    %γr, %hs, #Hpr, Hhl, %Hlast⟩
  -- the reader's view: the history's last snapshot, at an index no earlier than `m`
  icases lockHist_at γl γr _ hs (M, I') m Hlast $$ [$Hlb $Hpr $Hhl] with ⟨Hhl, %Hm, #Hat⟩
  ihave %Hszlt := preceipt_lt _ $$ Hsz
  -- the leases' `ID` facts, from their `leaseMeta`s
  iunfold lessorExtra at Hx
  icases Hx with ⟨%dc, %np, %h, %hx, %cp, %bl, Hdc, Hnp, Hnot, Hh, Hhq, Hcp, Hmeta, Hbl⟩
  icases lease.leaseMeta_ids M _ $$ Hmeta with ⟨Hmeta, #Hids⟩
  wp_apply (hUL lp lm M _) $$ [$Hlm $HM] as %sl %ls ⟨Hlm, HM, Hsl, %Hls0⟩
  obtain ⟨Hnd, Hpairs⟩ := Hls0
  have Hlen : ls.length = GMap.size M := by
    rw [GMap.size_eq_length M (ls.map Prod.snd) Hnd, List.length_map]
    intro k
    constructor
    · intro hk
      obtain ⟨⟨l, k'⟩, hmem, rfl⟩ := List.mem_map.1 hk
      rw [(Hpairs k' l).1 hmem]; rfl
    · intro hk
      obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 hk
      exact List.mem_map.2 ⟨(l, k), (Hpairs k l).2 hl, rfl⟩
  ihave #Hobjs : [∗list] x ∈ ls, isLeaseObj (GF := GF) γl x.1 $$ [Hls]
  · iapply (lease.bigSepM_pairs (P := fun _ l => isLeaseObj (GF := GF) γl l) M ls Hpairs)
    iexact Hls
  ihave #HidsL : [∗list] x ∈ ls, lsF go!"ID" x.1 ↦□ x.2 $$ [Hids]
  · iapply (lease.bigSepM_pairs (P := fun id l => lsF go!"ID" l ↦□ id) M ls Hpairs)
    iexact Hids
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hlk Hlm HM Him HI Hrdf Ha Hg Hdc Hnp Hnot Hh Hhq Hcp Hmeta
      Hbl Hhl] as Hrd
  · inext
    iunfold lessorMu
    iexists lm, im, M, I', rd0, L'
    iframe Hlm HM Him HI Hrdf Ha Hg
    isplitr
    · ipureintro; exact HL
    iframe Hsz Hls
    isplitl [Hdc Hnp Hnot Hh Hhq Hcp Hmeta Hbl]
    · iunfold lessorExtra; iexists dc, np, h, hx, cp, bl; iframe
    iexists γr, hs
    iframe Hpr Hhl
    ipureintro; exact Hlast
  -- the sort: a permutation of the pairs
  (try wp_auto)
  ihave #Hpsort : isPkgInit (PROP := IProp GF) pkg_id.sort $$ []
  · iPkgInit
  ihave #HobjsF : [∗list] p ∈ ls.map Prod.fst, isLeaseObj (GF := GF) γl p $$ [Hobjs]
  · rw [BigSepL.bigSepL_map]; iexact Hobjs
  ihave #Hsorter := lease.sorter_byExpiry hLen hLess hSwap γl sl ls Hb $$ [$Hpkg $HobjsF]
  wp_apply (hSort (Loc × w64) _ (lease.sorterR sl ls) ls) $$ [Hsl Htt] as %ls' HR
  · iframe #
    unfold lease.sorterR
    iframe
    ipureintro
    refine ⟨List.Perm.refl ls, ?_⟩
    omega
  unfold lease.sorterR
  icases HR with ⟨⟨Hsl, Htt, %Hp⟩, %Hp'⟩
  (try wp_auto)
  iapply HΦ
  iunfold lessorRd
  iframe Hrd Htt Hsl
  isplitr
  · iexists hs.length - 1
    isplitr
    · ipureintro; exact Hm
    iapply (leaseMapAt_perm γl _ Hp.symm)
    iunfold leaseMapAt
    iexists (M, I')
    iframe Hat
    ipureintro; exact ⟨Hnd, Hpairs⟩
  iapply (BigSepL.bigSepL_perm (PROP := IProp GF)
    (Φ := fun (x : Loc × w64) => iprop(isLeaseObj (GF := GF) γl x.1 ∗ lsF go!"ID" x.1 ↦□ x.2)) Hp.symm).1
  iapply BigSepL.bigSepL_sep_eqv.2
  iframe Hobjs HidsL

end proof

end EtcdGrove
end Perennial
