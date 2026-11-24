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
public import Proof.go_etcd_io.etcd.server.v3.lease.SortByExpiry

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

theorem lease.lessor.Leases.wp_proof
    (hUL : lease.lessor.unsafeLeases.spec (GF := GF) (hG := hG))
    (hSort : sort.Sort''.anyLessSpec (GF := GF) (hG := hG))
    (hLen : lease.leasesByExpiry.Len.spec (GF := GF) (hG := hG))
    (hLess : lease.leasesByExpiry.Less.spec (GF := GF) (hG := hG))
    (hSwap : lease.leasesByExpiry.Swap.spec (GF := GF) (hG := hG)) :
    lease.lessor.Leases.spec (GF := GF) (hG := hG) := by
  intro lp γl m
  wp_start as ⟨#Hinv, #Hpool, #Hlb, Htt, %Hb, %Hrb⟩
  iunfold lessorInv at Hinv
  icases Hinv with ⟨%Hlp, #Hpin, #Hmu, #Hrdi⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  -- a reader slot borrowed from the pool with the token, for the read lock (the lease-src plan)
  iapply fupd_wp
  imod lease.lessorRdPool_borrow γl ⊤ (fun _ _ => CoPset.mem_full) $$ [Hpool Htt]
    with ⟨Hrdo, Hback⟩
  · iframe #; iframe
  imodintro
  wp_auto
  iunfold lessorRdOf at Hrdo
  icases Hrdo with ⟨%lp', #Hpin', Hrd⟩
  ihave %Heq := lessorPin_agree γl lp lp' $$ [$Hpin $Hpin']
  subst Heq
  iunfold lessorRd at Hrd
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hlk, HR⟩
  iunfold lessorMu at HR
  icases HR with ⟨%lm, %im, %M, %I', %rd0, %L', Hlm, HM, Him, HI, Hrdf, Ha, Hg, %HL, #Hsz, #Hls, Hx,
    %γr, %hs, #Hpr, Hhl, %Hlast⟩
  -- the reader's view: the history's last snapshot, at an index no earlier than `m`
  obtain ⟨Tq, Hlast⟩ := Hlast
  icases lockHist_at γl γr _ hs (M, I', Tq) m Hlast $$ [$Hlb $Hpr $Hhl] with ⟨Hhl, %Hm, #Hat⟩
  ihave %Hszlt := preceipt_lt _ $$ Hsz
  -- the leases' `ID` facts, from their `leaseMeta`s
  iunfold lessorExtra at Hx
  icases Hx with ⟨%dc, %np, %h, %hx, %bl, Hdc, Hnp, Hnot, Hh, Hhq, Hcp, Hmeta, Hbl, Hdt⟩
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
      Hbl Hdt Hhl] as Hrd
  · inext
    iunfold lessorMu
    iexists lm, im, M, I', rd0, L'
    iframe Hlm HM Him HI Hrdf Ha Hg
    isplitr
    · ipureintro; exact HL
    iframe Hsz Hls
    isplitl [Hdc Hnp Hnot Hh Hhq Hcp Hmeta Hbl Hdt]
    · iunfold lessorExtra; iexists dc, np, h, hx, bl; iframe
    iexists γr, hs
    iframe Hpr Hhl
    ipureintro; exact ⟨Tq, Hlast⟩
  -- the slot back, for the token (`Less` reads the clock with it)
  iapply fupd_wp
  imod Hback $$ [Hrd] with Htt
  · iunfold lessorRdOf; iexists lp; iframe Hpin; iunfold lessorRd; iexact Hrd
  imodintro
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
  iframe Htt Hsl
  isplitr
  · iexists hs.length - 1
    isplitr
    · ipureintro; exact Hm
    iapply (leaseMapAt_perm γl _ Hp.symm)
    iunfold leaseMapAt
    iexists (M, I', Tq)
    iframe Hat
    ipureintro; exact ⟨Hnd, Hpairs⟩
  iapply (BigSepL.bigSepL_perm (PROP := IProp GF)
    (Φ := fun (x : Loc × w64) => iprop(isLeaseObj (GF := GF) γl x.1 ∗ lsF go!"ID" x.1 ↦□ x.2)) Hp.symm).1
  iapply BigSepL.bigSepL_sep_eqv.2
  iframe Hobjs HidsL

end proof

end EtcdGrove
end Perennial
