module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Find
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__find
public import Proof.go_etcd_io.etcd.pkg.v3.adt.NodeLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3.adt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

theorem adt.intervalTree.Find.wp_proof
    (h_find : adt.intervalTree.find.spec (GF := GF) (hG := hG)) :
    adt.intervalTree.Find.spec (GF := GF) (hG := hG) := by
  intro t L b e q
  wp_start as Ht
  icases adt.ownIvt_read _ _ _ $$ Ht with ⟨%tv, %T, Hr, Hc, Hs, Hn, %Hp, Hback⟩
  obtain ⟨hTL, -, hsorted, -⟩ := Hp
  subst hTL
  wp_auto
  wp_apply h_find t tv q T b e $$ [Hr Hs Hn] as %n ⟨Hr, Hs, %p, %Tz, Hz, Hw, %HTz⟩
  · iframe
  cases hf : T.findE (b, e) with
  | none =>
    rw [hf] at HTz
    subst HTz
    icases adt.ownNode_leaf_open _ _ _ _ $$ Hz with %Hn
    subst Hn
    wp_auto
    iapply HΦ
    iright
    isplitl []
    · ipureintro; exact ⟨rfl, adt.findE_none _ T hsorted hf⟩
    iapply Hback
    iframe
    iapply Hw
    iapply adt.ownNode_leaf_close
  | some z =>
    rw [hf] at HTz
    obtain ⟨c, l, r, rfl⟩ := HTz
    obtain ⟨hzm, hz1⟩ := adt.findE_some _ T z hf
    obtain ⟨⟨zb, ze⟩, zv⟩ := z
    simp only [Prod.mk.injEq] at hz1
    obtain ⟨rfl, rfl⟩ := hz1
    icases adt.ownNode_node_open _ _ _ _ c l ((zb, ze), zv) r $$ Hz with
      ⟨%lp, %rp, %Hn, Hiv, Hmx, Hl, Hr', Hp, Hc', Hnl, Hnr⟩
    wp_if_destruct
    · exfalso; first | exact Hn.1 ‹_› | exact Hn.1 rfl
    ihave %Hivn := typedPointsto_not_null _ _ _ $$ Hiv
    iapply HΦ
    ileft
    iexists ((zb, ze), zv)
    isplitl []
    · ipureintro; exact ⟨hzm, rfl⟩
    isplitl []
    · ipureintro; exact Hivn
    iframe Hiv
    iintro Hiv
    iapply Hback
    iframe
    iapply Hw
    iapply adt.ownNode_node_close
    iexists lp, rp
    iframe
    ipureintro; exact Hn

end proof

end EtcdGrove
end Perennial
