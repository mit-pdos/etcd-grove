/-
The proof of `Spec/go_etcd_io/bbolt/Bucket__pageNode_r.lean` (U6, `notes/bbolt-proof-plan.md`):
the header's root (a persistent copy, or the view's bytes), then the inline page or `Tx.page_r`.
-/
module

public import Spec.go_etcd_io.bbolt.Bucket__pageNode_r
public import Spec.go_etcd_io.bbolt.Tx__page_r
public import Spec.go_etcd_io.bbolt.internal.common.InBucket__RootPage
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- A reader bucket's header's `RootPage()`: its value's root. -/
theorem wp_rd_rootPage (hRP : internal.common.InBucket.RootPage.spec (GF := GF) (hG := hG))
    (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) (bv : List w8)
    (ibp : Loc) (hbv : 16 ≤ bv.length) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ rdTxK (GF := GF) K tx src q T v ∗
        ((∃ ib : InBucket, ibp ↦□ ib ∗ ⌜ib.root' = (inBucketOf bv).root'⌝) ∨
          ⌜inViewLoc v ibp (bytesAt bv 0 16)⌝) }}
      (App (Val (ibp @!! go.GoType.PointerType InBucket.ty @!! go!"RootPage")) (Val #()))
    {{ RET #((inBucketOf bv).root'); rdTxK K tx src q T v ∗
        ((∃ ib : InBucket, ibp ↦□ ib ∗ ⌜ib.root' = (inBucketOf bv).root'⌝) ∨
          ⌜inViewLoc v ibp (bytesAt bv 0 16)⌝) }} := by
  iintro %Φ ⟨#Hpkg, Hk, Hh⟩ HΦ
  icases Hh with (⟨%ib, #Hib, %Hr⟩ | %Hv)
  · wp_apply hRP ibp ib DFrac.discard $$ [Hib] as -
    · iexact Hib
    rw [Hr]
    iapply HΦ
    iframe
    ileft; iexists ib; iframe #; ipureintro; exact Hr
  · icases rdTxK_loc_acc K tx src q T v ibp _ Hv $$ Hk with ⟨%dqh, Hb, Hk⟩
    have hlen : (bytesAt bv 0 16).length = 16 := by unfold bytesAt; simp; omega
    icases Read.bytesPointsto_bounds ibp dqh (bytesAt bv 0 16) (by intro h; simp [h] at hlen)
      $$ Hb with ⟨Hb, %Hbd⟩
    icases bytesPointsto_view_read (V := InBucket) ibp dqh (bytesAt bv 0 16) 0 ibp (by simp)
      (by omega) Hbd.1 $$ Hb with ⟨Hib, Hback⟩
    rw [show (decode (List.take 16 (List.drop 0 (bytesAt bv 0 16))) : InBucket) = inBucketOf bv by
      unfold inBucketOf bytesAt; simp only [List.drop_zero, List.take_take, Nat.min_self]]
    wp_apply hRP ibp (inBucketOf bv) dqh $$ [Hib] as Hib
    · iexact Hib
    ihave Hb := Hback $$ Hib
    ihave Hk := Hk $$ Hb
    iapply HΦ
    iframe
    iright; ipureintro; exact Hv

theorem Bucket.pageNode_r.wp_proof (hpr : Tx.page_r.spec (GF := GF) (hG := hG))
    (hRP : internal.common.InBucket.RootPage.spec (GF := GF) (hG := hG)) :
    Bucket.pageNode_r.spec (GF := GF) (hG := hG) := by
  intro K tx src q T v b dq bv ibp pp id l pg hbv hpa
  unfold rBktP
  wp_start as ⟨Hk, HIB, Htx, Hbks, Hpage, Hroot, Hnodes, Hhdr, Hil⟩
  wp_auto
  wp_method_call; wp_call
  wp_auto
  wp_apply wp_rd_rootPage hRP K tx src q T v bv ibp hbv $$ [Hk Hhdr] as ⟨Hk, Hhdr⟩
  · iframe
  rw [show (decode (List.take 8 (bytesAt bv 0 16)) : w64) = (inBucketOf bv).root' from rfl]
  have hroot : inBucketRoot bv = (inBucketOf bv).root'.toNat := rfl
  unfold rPageAt at hpa
  wp_if_destruct
  · -- inline: position 0, the inline page
    have hi : inBucketRoot bv = 0 := by rw [hroot, Hif]; rfl
    rw [if_pos hi] at hpa
    by_cases h0 : id.toNat = 0
    · rw [if_pos h0] at hpa
      simp only [Option.some.injEq, Prod.mk.injEq] at hpa
      obtain ⟨rfl, rfl⟩ := hpa
      have hid : id = W64 0 := by apply BitVec.eq_of_toNat_eq; simpa using h0
      subst hid
      wp_auto
      iapply HΦ
      iframe
    · rw [if_neg h0] at hpa; cases hpa
  · have hi : inBucketRoot bv ≠ 0 := by
      rw [hroot]; intro h; apply Hif; apply BitVec.eq_of_toNat_eq; simpa using h
    rw [if_neg hi] at hpa
    obtain ⟨pg', hpg, he⟩ := Option.map_eq_some_iff.mp hpa
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    wp_apply hpr K tx src q T v id pg' hpg $$ [Hk] as Hk
    · iexact Hk
    iapply HΦ
    iframe

end proof

end bbolt
end EtcdGrove
end Perennial
