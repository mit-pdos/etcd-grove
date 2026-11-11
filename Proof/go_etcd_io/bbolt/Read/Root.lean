/-
The read path's (U6, `notes/bbolt-proof-plan.md`) reads of a reader bucket's header: its
`RootPage()` (a persistent copy, or the view's bytes).
-/
module

public import Proof.go_etcd_io.bbolt.Read.RCtx
public import Spec.go_etcd_io.bbolt.internal.common.InBucket__RootPage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section root
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
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

end root

end bbolt
end EtcdGrove
end Perennial
