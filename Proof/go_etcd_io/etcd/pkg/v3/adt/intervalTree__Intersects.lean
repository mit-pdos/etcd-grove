/-
`intervalTree.Intersects` (`interval_tree.go`) over string-affine keys: the generic proof
(`intervalTree__Intersects_gen.lean`) instantiated for `strKey` (the auth plan's S2b). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Intersects
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Intersects_gen
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

theorem adt.intervalTree.Intersects.wp_proof
    (h_Intersects_gen : adt.intervalTree.Intersects_gen.spec (GF := GF) (hG := hG))
    (h_StringAffineComparable_Compare :
      adt.StringAffineComparable.Compare.spec (GF := GF) (hG := hG)) :
    adt.intervalTree.Intersects.spec (GF := GF) (hG := hG) := by
  intro t L b e q
  unfold adt.ownIvt
  rw [adt.affIvl_eq (GF := GF)]
  wp_start_folded as Ht
  wp_apply (h_Intersects_gen adt.strKey (adt.strKey_ok h_StringAffineComparable_Compare) t L
    #b #e .discard .discard b e (DFrac.own q)) $$ [Ht] as ⟨Ht, -, -⟩
  · simp only [adt.strKey_keyAt]
    iframe Ht
    all_goals (try (isplitl []; · ipureintro; trivial))
    all_goals (try (isplitl []; · ipureintro; trivial))
    all_goals (try (ipureintro; trivial))
  iapply HΦ
  iexact Ht

end proof

end EtcdGrove
end Perennial
