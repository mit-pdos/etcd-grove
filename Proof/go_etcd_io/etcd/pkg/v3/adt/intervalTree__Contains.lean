/-
`intervalTree.Contains` (`interval_tree.go`) over string-affine keys: the generic proof
(`intervalTree__Contains_gen.lean`) instantiated for `strKey` (the auth plan's S2b). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Contains
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Contains_gen
public import Proof.go_etcd_io.etcd.pkg.v3.adt.StrKey

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

theorem adt.intervalTree.Contains.wp_proof
    (h_Contains_gen : adt.intervalTree.Contains_gen.spec (GF := GF) (hG := hG))
    (h_StringAffineComparable_Compare :
      adt.StringAffineComparable.Compare.spec (GF := GF) (hG := hG)) :
    adt.intervalTree.Contains.spec (GF := GF) (hG := hG) := by
  intro t L b e q
  unfold adt.ownIvt
  rw [adt.affIvl_eq (GF := GF)]
  wp_start_folded as Ht
  wp_apply (h_Contains_gen adt.strKey (adt.strKey_ok h_StringAffineComparable_Compare) t L
    #b #e .discard .discard b e (DFrac.own q)) $$ [Ht] as %r ⟨Ht, -, -, %Hres⟩
  · simp only [adt.strKey_keyAt]
    iframe Ht
    all_goals (try (isplitl []; · ipureintro; trivial))
    all_goals (try (ipureintro; trivial))
  iapply HΦ
  iframe Ht
  ipureintro; exact Hres

end proof

end EtcdGrove
end Perennial
