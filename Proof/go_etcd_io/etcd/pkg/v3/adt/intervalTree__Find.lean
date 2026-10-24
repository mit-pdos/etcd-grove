/-
`intervalTree.Find` (`interval_tree.go`) over string-affine keys: the generic proof
(`intervalTree__Find_gen.lean`) instantiated for `strKey` (the auth plan's S2b). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Find
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Find_gen
public import Proof.go_etcd_io.etcd.pkg.v3.adt.StrKey

@[expose] public section

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
    (h_Find_gen : adt.intervalTree.Find_gen.spec (GF := GF) (hG := hG))
    (h_StringAffineComparable_Compare :
      adt.StringAffineComparable.Compare.spec (GF := GF) (hG := hG)) :
    adt.intervalTree.Find.spec (GF := GF) (hG := hG) := by
  intro t L b e q
  unfold adt.ownIvt
  rw [adt.affIvl_eq (GF := GF)]
  wp_start_folded as Ht
  wp_apply (h_Find_gen adt.strKey (adt.strKey_ok h_StringAffineComparable_Compare) t L
    #b #e .discard .discard b e (DFrac.own q)) $$ [Ht] as %p ⟨-, -, Hpost⟩
  · simp only [adt.strKey_keyAt]
    iframe Ht
    all_goals (try (isplitl []; · ipureintro; trivial))
    all_goals (try (isplitl []; · ipureintro; trivial))
    all_goals (try (ipureintro; trivial))
  iapply HΦ
  icases Hpost with (⟨%z, %hz, %hpn, Hiv, Hw⟩ | H)
  · ileft
    have hb : z.1.1 = b := by rw [hz.2]
    have he : z.1.2 = e := by rw [hz.2]
    iexists z
    icases (adt.strKey_ivAt _ _ _).1 $$ Hiv with Hiv
    rw [hb, he, adt.affIvl_eq (GF := GF)]
    iframe Hiv
    isplitl []
    · ipureintro; exact ⟨hz.1, hz.2⟩
    isplitl []
    · ipureintro; exact hpn
    iintro Hiv
    iapply Hw
    iapply (adt.strKey_ivAt _ _ _).2
    rw [hb, he, adt.affIvl_eq (GF := GF)]
    iexact Hiv
  · iright
    iexact H

end proof

end EtcdGrove
end Perennial
