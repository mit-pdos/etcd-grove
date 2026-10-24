/-
`intervalTree.Union` (`interval_tree.go`) over string-affine keys: the generic proof
(`intervalTree__Union_gen.lean`) instantiated for `strKey` (the auth plan's S2b). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Union
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Union_gen
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

theorem adt.intervalTree.Union.wp_proof
    (h_Union_gen : adt.intervalTree.Union_gen.spec (GF := GF) (hG := hG))
    (h_StringAffineComparable_Compare :
      adt.StringAffineComparable.Compare.spec (GF := GF) (hG := hG)) :
    adt.intervalTree.Union.spec (GF := GF) (hG := hG) := by
  intro t t' L L' q' b e
  unfold adt.ownIvt
  rw [adt.affIvl_eq (GF := GF)]
  wp_start_folded as ⟨Ht, Ht', %hlen, %hq⟩
  wp_apply (h_Union_gen adt.strKey (adt.strKey_ok h_StringAffineComparable_Compare) t t' L L'
    (DFrac.own q') #b #e .discard .discard b e) $$ [Ht Ht'] as ⟨-, -, Hpost⟩
  · simp only [adt.strKey_keyAt]
    iframe Ht Ht'
    all_goals (try (isplitl []; · ipureintro; trivial))
    all_goals (try (isplitl []; · ipureintro; trivial))
    all_goals (try (isplitl []; · ipureintro; exact hlen))
    all_goals (try (ipureintro; exact hq))
  iapply HΦ
  iexact Hpost

end proof

end EtcdGrove
end Perennial
