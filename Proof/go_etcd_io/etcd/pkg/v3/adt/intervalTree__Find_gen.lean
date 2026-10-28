/-
`intervalTree.Find` (`interval_tree.go`) over a comparator: the proof of
`Spec/.../adt/intervalTree__Find_gen.lean` (unit 4, generalized in the auth plan's S2b). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Find_gen
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__find

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3.adt

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

theorem adt.intervalTree.Find_gen.wp_proof
    (h_find : adt.intervalTree.find.spec (GF := GF) (hG := hG)) :
    adt.intervalTree.Find_gen.spec (GF := GF) (hG := hG) := by
  intro K hK t L vb ve db de b e q
  wp_start as ⟨Ht, Hkb, Hke⟩
  icases adt.ownIvtK_read K _ _ _ $$ Ht with ⟨%tv, %T, Hr, Hc, Hs, Hn, %Hp, Hback⟩
  obtain ⟨hTL, -, hsorted, -⟩ := Hp
  subst hTL
  wp_auto
  wp_apply (h_find K hK) t tv q T vb ve db de b e $$ [Hr Hs Hn Hkb Hke]
    as %n ⟨Hr, Hs, Hkb, Hke, %p, %C, %ls, %Tz, Hw, Hz, %HTz⟩
  · iframe
  obtain ⟨Htop, Hplug, HTz⟩ := HTz
  cases hf : T.findE (b, e) with
  | none =>
    rw [hf] at HTz
    subst HTz
    icases adt.ownNode_leaf_open K _ _ _ _ $$ Hz with %Hn
    subst Hn
    wp_auto
    iapply HΦ
    iframe Hkb Hke
    iright
    isplitl []
    · ipureintro; exact ⟨rfl, adt.findE_none _ T hsorted hf⟩
    iapply Hback
    iframe
    rw [← Hplug]
    iapply adt.ownPathAt_plug' K _ _ _ _ _ _ _ _ _ Htop
    iframe
  | some z =>
    rw [hf] at HTz
    obtain ⟨c, l, r, rfl⟩ := HTz
    obtain ⟨hzm, hz1⟩ := adt.findE_some _ T z hf
    obtain ⟨⟨zb, ze⟩, zv⟩ := z
    simp only [Prod.mk.injEq] at hz1
    obtain ⟨rfl, rfl⟩ := hz1
    icases adt.ownNode_node_open K _ _ _ _ c l ((zb, ze), zv) r $$ Hz with
      ⟨%lp, %rp, %Hn, Hiv, Hmx, Hl, Hr', Hp, Hc', Hnl, Hnr⟩
    wp_if_destruct
    · exfalso; first | exact Hn.1 ‹_› | exact Hn.1 rfl
    ihave %Hivn := K.ivAt_not_null _ _ _ $$ Hiv
    iapply HΦ
    iframe Hkb Hke
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
    rw [← Hplug]
    iapply adt.ownPathAt_plug' K _ _ _ _ _ _ _ _ _ Htop
    iframe
    iapply adt.ownNode_node_close
    iexists lp, rp
    iframe
    ipureintro; exact Hn


end proof

end EtcdGrove
end Perennial
