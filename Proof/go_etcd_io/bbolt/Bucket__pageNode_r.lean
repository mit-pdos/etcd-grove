/-
The proof of `Spec/go_etcd_io/bbolt/Bucket__pageNode_r.lean` (U6, `notes/bbolt-proof-plan.md`):
the header's root (a persistent copy, or the view's bytes), then the inline page or `Tx.page_r`.
-/
module

public import Spec.go_etcd_io.bbolt.Bucket__pageNode_r
public import Spec.go_etcd_io.bbolt.Tx__page_r
public import Proof.go_etcd_io.bbolt.Read.Root

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
