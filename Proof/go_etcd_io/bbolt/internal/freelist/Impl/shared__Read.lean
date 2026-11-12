/-
`shared.Read(p)` (U2 internal): the free ids become the freelist page's ids, sorted (`Init`
through the interface). The page is read through its bytes (`Lemmas/FLPageBytes.lean`).
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Own
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.FLPageBytes
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Sorters
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsFreelistPage
public import Spec.go_etcd_io.bbolt.internal.common.Page__FreelistPageIds

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs
namespace internal
namespace freelist

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- `t.Read(p)` on the freelist page `pg` at `p` (read at any fraction): the free ids become
the page's ids, sorted. The state need only be weakly well-formed after it (`Reload`: the page
may hold pending ids); an empty page needs the old free ids all pending (`hashMap.Init` of no
ids keeps the old cache). -/
abbrev shared.Read.spec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (fl : FLPg) (p : Loc) (pg : List w8) (dq : DFrac),
  pageFlags pg = freelistPageFlag →
  16 + 8 * (flCountIdx pg).2 + 8 * (flCountIdx pg).1 ≤ pg.length →
  (flCountIdx pg).1 < 2 ^ 63 → 0 < p.addr → p.addr + pg.length ≤ maxAddr →
  ({ fl with free := sortPgids (flIds pg) } : FLPg).WFw →
  (flIds pg ≠ [] ∨ ∀ x ∈ fl.free, x ∈ fl.pendingIds) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ I.hdl s ∗
      ownShW s I.iface fl ∗ I.own fl.free ∗ bytesPointsto p dq pg }}
    (App (Val #(methods (go.GoType.PointerType shared.ty) go!"Read" #s)) (Val #p))
  {{ RET #(); ownShW s I.iface { fl with free := sortPgids (flIds pg) } ∗
      I.own (sortPgids (flIds pg)) ∗ bytesPointsto p dq pg }}

theorem shared.Read.wp_proof (I : FLImpl (GF := GF)) (hInit : I.InitSpec)
    (hIs : _root_.Perennial.EtcdGrove.bbolt.internal.common.Page.IsFreelistPage.spec
      (GF := GF) (hG := hG))
    (hIds : _root_.Perennial.EtcdGrove.bbolt.internal.common.Page.FreelistPageIds.spec
      (GF := GF) (hG := hG)) :
    shared.Read.spec I := by
  intro s fl p pg dq Hfl Hsz Hcnt Hp Hmax Hwf Hemp
  wp_start as ⟨#Hhdl, Hsh, Hown, Hpg⟩
  ihave #Hc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  icases flPage_open p pg dq Hp Hsz $$ Hpg with ⟨Hhdr, Hcc, Hids, Hback⟩
  have hflag : (pageHdr pg).flags' = W16 16 := by
    apply BitVec.eq_of_toNat_eq; unfold pageFlags freelistPageFlag at Hfl; rw [Hfl]; rfl
  -- the ids' count and offset, as `FreelistPageIds` computes them
  have hN : (if (pageHdr pg).count' = W16 65535 then (decode (bytesAt pg 16 8) : w64)
      else W64 (uint.Z (pageHdr pg).count')) = W64 ((flCountIdx pg).1 : Int) := by
    rw [flCountIdx_eq]
    split
    · simp
    · simp only [pageCount]; try word
  have hK : (uint.Z (if (pageHdr pg).count' = W16 65535 then W64 1 else W64 0) : Int) =
      ((flCountIdx pg).2 : Int) := by
    rw [flCountIdx_eq]; split <;> word
  have hc0 : (pageHdr pg).count' = W16 65535 → 0 ≤ sint.Z (decode (bytesAt pg 16 8) : w64) := by
    intro h
    have : ((decode (bytesAt pg 16 8) : w64)).toNat = (flCountIdx pg).1 := by
      rw [flCountIdx_eq, if_pos h]
    word
  have hnZ : sint.Z (W64 ((flCountIdx pg).1 : Int)) = (flCountIdx pg).1 := by word
  have hk1 := flCountIdx_snd_le pg
  have hbnd : p.addr + 16 + 8 * (uint.Z (if (pageHdr pg).count' = W16 65535 then W64 1 else W64 0) +
      sint.Z (if (pageHdr pg).count' = W16 65535 then (decode (bytesAt pg 16 8) : w64)
        else W64 (uint.Z (pageHdr pg).count'))) ≤ maxAddr := by
    rw [hN, hK, hnZ]; omega
  iunfold flCountCell at Hcc
  iunfold flCountCell at Hback
  generalize hc : (decode (bytesAt pg 16 8) : w64) = c at hN hc0 hbnd
  generalize hh : pageHdr pg = hdr at hflag hN hK hc0 hbnd
  wp_auto
  wp_apply (hIs p hdr dq) $$ [Hhdr] as Hhdr
  · iframe
  rw [hflag]
  simp only [decide_true]
  wp_auto
  wp_apply (hIds p hdr dq c hflag hc0 Hp hbnd) $$ [Hhdr Hcc] as ⟨Hhdr, Hcc⟩
  · iframe
  rw [hN, hK]
  iunfold ownShW at Hsh
  icases Hsh with ⟨%c0, Hsh, %Hok⟩
  iunfold ownShC at Hsh
  iNamed Hsh
  have hlenids := flIds_length pg
  generalize hn : (flCountIdx pg).1 = n at hlenids hnZ Hcnt Hsz hN ⊢
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · -- an empty page: `Init([]Pgid{})`
    subst h0
    have hnil : flIds pg = [] := List.eq_nil_of_length_eq_zero hlenids
    rw [if_pos (show W64 ((0 : Nat) : Int) = W64 0 from rfl)]
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl0 ⟨Hsl0, Hsl0c⟩
    try wp_auto
    wp_method_call
    wp_call
    try wp_auto
    ihave Hsh : ownShW s I.iface fl $$ [Hif Hal Hallocs Hca Hcache Hpe Hpending Hpds]
    · iunfold ownShW; iexists c0
      isplitl
      · iunfold ownShC; iexists al, ca, pe, pp; iframe
      · ipureintro; exact Hok
    isimp only [go.arrayLiteralSize, Int.toNat_zero, List.replicate_zero] at Hsl0
    have Hwf0 : ({ fl with free := [] } : FLPg).WFw := by
      rw [hnil] at Hwf; simpa [sortPgids] using Hwf
    have Hemp0 : ([] : List w64) ≠ [] ∨ ∀ x ∈ fl.free, x ∈ fl.pendingIds := by
      rw [hnil] at Hemp; exact Hemp
    wp_bind (App (Val #(methods I.ity go!"Init" I.iv)) _)
    iapply (hInit s fl _ [] Hwf0 Hemp0) $$ [Hsh Hown Hsl0 Hsl0c]
    · iframe
      isplitl []
      · iexact Hpkg
      iexact Hhdl
    inext
    iintro ⟨Hsh, Hown⟩
    wp_auto
    iapply HΦ
    rw [hnil]
    simp only [sortPgids, List.mergeSort_nil]
    iframe
    iapply Hback
    iframe
  · have hn0 : W64 (n : Int) ≠ W64 0 := by intro h; have := congrArg BitVec.toNat h; simp at this; omega
    simp only [hn0, ↓reduceIte]
    wp_auto
    wp_apply (wp_slice_make2 (V := w64) (W64 (n : Int))) as %d ⟨Hd, Hdc⟩
    · ipureintro; omega
    -- the page's ids, as a `[]Pgid` over its bytes
    have hloc : (p +ₗ (((16 + 8 * (flCountIdx pg).2 : Nat) : Int))) =
        p +ₗ (16 + 8 * ((flCountIdx pg).2 : Int)) := by
      congr 1 <;> omega
    rw [hloc]
    ihave Hsl := ownSlice_of_bytes' go_etcd_io.bbolt.internal.common.Pgid.ty
      go_etcd_io.bbolt.internal.common.Pgid.layout
      (slice.mk (p +ₗ (16 + 8 * ((flCountIdx pg).2 : Int))) (W64 (n : Int)) (W64 (n : Int)))
      (flIds pg) dq (by simp [Loc.add]; omega) (by simp only; rw [hnZ, hlenids])
      (by simp only; omega) $$ Hids
    wp_apply (wp_slice_copy d _ _ (flIds pg) dq) $$ [Hd Hsl] as %nc ⟨%Hnc, Hd, Hsl⟩
    · iframe
    rw [show (flIds pg).take (List.replicate (sint.nat (W64 (n : Int))) (zero_val w64)).length ++
        (List.replicate (sint.nat (W64 (n : Int))) (zero_val w64)).drop (flIds pg).length =
        flIds pg by
      rw [List.length_replicate, show sint.nat (W64 (n : Int)) = n by word, ← hlenids,
        List.take_length, List.drop_replicate, Nat.sub_self, List.replicate_zero,
        List.append_nil]]
    icases ownSlice_w64_len _ _ _ $$ Hd with ⟨Hd, %Hdl⟩
    ihave #Hsrt := Pgids_isSorter (GF := GF) d
    ihave #Hspkg : isPkgInit (PROP := IProp GF) pkg_id.sort $$ []
    · iPkgInit
    wp_apply (sort.wp_Sort (interface.mk go_etcd_io.bbolt.internal.common.Pgids.ty #d)
      (fun l => d ↦* l) pgLt slices.StrictWeakOrder_unsigned_lt (flIds pg)) $$ [Hd]
      as %xs' ⟨Hd, %Hperm, %Hsorted⟩
    · iframe
      isplitl []
      · iexact Hsrt
      ipureintro; omega
    have hxs' : xs' = sortPgids (flIds pg) := sort_post_eq Hperm Hsorted
    subst hxs'
    try wp_auto
    wp_method_call
    wp_call
    try wp_auto
    ihave Hsh : ownShW s I.iface fl $$ [Hif Hal Hallocs Hca Hcache Hpe Hpending Hpds]
    · iunfold ownShW; iexists c0
      isplitl
      · iunfold ownShC; iexists al, ca, pe, pp; iframe
      · ipureintro; exact Hok
    have Hemp1 : sortPgids (flIds pg) ≠ [] ∨ ∀ x ∈ fl.free, x ∈ fl.pendingIds := by
      left; intro h
      have := (sortPgids_perm (flIds pg)).length_eq
      rw [h] at this; simp at this; omega
    wp_bind (App (Val #(methods I.ity go!"Init" I.iv)) _)
    iapply (hInit s fl d _ Hwf Hemp1) $$ [Hsh Hown Hd Hdc]
    · iframe
      isplitl []
      · iexact Hpkg
      iexact Hhdl
    inext
    iintro ⟨Hsh, Hown⟩
    wp_auto
    iapply HΦ
    iframe
    iapply Hback
    iframe
    iapply ownSlice_to_bytes' go_etcd_io.bbolt.internal.common.Pgid.ty
      go_etcd_io.bbolt.internal.common.Pgid.layout _ _ _ (by simp [Loc.add]; omega) $$ Hsl

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
