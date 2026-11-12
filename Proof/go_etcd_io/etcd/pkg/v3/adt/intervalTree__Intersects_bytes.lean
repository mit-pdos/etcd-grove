/-
`intervalTree.Intersects` (`interval_tree.go`) over bytes-affine keys: the generic proof
(`intervalTree__Intersects_gen.lean`) instantiated for `bytesKey` (the auth plan's S2b; until then
an axiom of `BytesIvl.lean`). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Intersects_bytes
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Intersects_gen

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

theorem adt.intervalTree.Intersects_bytes.wp_proof
    (h_Intersects_gen : adt.intervalTree.Intersects_gen.spec (GF := GF) (hG := hG))
    (h_BytesAffineComparable_Compare :
      adt.BytesAffineComparable.Compare.spec (GF := GF) (hG := hG)) :
    adt.intervalTree.Intersects_bytes.spec (GF := GF) (hG := hG) := by
  intro t L b e bs es db de dq
  unfold adt.ownIvtB
  rw [adt.bytesIvl_eq (GF := GF)]
  wp_start_folded as ⟨Ht, Hb, He⟩
  wp_apply (h_Intersects_gen adt.bytesKey (adt.bytesKey_ok h_BytesAffineComparable_Compare)
    t L #b #e db de bs es dq) $$ [Ht Hb He] as ⟨Ht, Hb, He⟩
  · simp only [adt.bytesKey_keyAt]
    iframe Ht
    isplitl [Hb]
    · iapply adt.bytesKeyAt_intro $$ Hb
    iapply adt.bytesKeyAt_intro $$ He
  iapply HΦ
  iframe Ht
  (try simp only [adt.bytesKey_keyAt])
  isplitl [Hb]
  · iapply adt.bytesKeyAt_elim $$ Hb
  iapply adt.bytesKeyAt_elim $$ He

end proof

end EtcdGrove
end Perennial
