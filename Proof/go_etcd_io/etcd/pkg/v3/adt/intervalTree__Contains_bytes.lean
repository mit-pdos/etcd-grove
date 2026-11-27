/-
`intervalTree.Contains` (`interval_tree.go`) over bytes-affine keys: the generic proof
(`intervalTree__Contains_gen.lean`) instantiated for `bytesKey` (the auth plan's S2b; until then an
axiom of `BytesIvl.lean`). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Contains_bytes
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Contains_gen
public import Proof.go_etcd_io.etcd.pkg.v3.adt.NodeLemmas

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

theorem adt.intervalTree.Contains_bytes.wp_proof
    (h_Contains_gen : adt.intervalTree.Contains_gen.spec (GF := GF) (hG := hG))
    (h_BytesAffineComparable_Compare :
      adt.BytesAffineComparable.Compare.spec (GF := GF) (hG := hG)) :
    adt.intervalTree.Contains_bytes.spec (GF := GF) (hG := hG) := by
  intro t L b e bs es db de dq
  unfold adt.ownIvtB
  rw [adt.bytesIvl_eq (GF := GF)]
  wp_start_folded as ⟨Ht, Hb, He⟩
  ihave %hs := adt.ownIvtK_sorted adt.bytesKey _ _ _ $$ Ht
  icases adt.ownIvtK_T adt.bytesKey t L _ $$ Ht with ⟨%T, Ht, %hTL⟩
  subst hTL
  wp_apply (h_Contains_gen adt.bytesKey (adt.bytesKey_ok h_BytesAffineComparable_Compare)
    t T #b #e db de bs es dq) $$ [Ht Hb He] as %r ⟨Ht, Hb, He, %Hres⟩
  · simp only [adt.bytesKey_keyAt]
    iframe Ht
    isplitl [Hb]
    · iapply adt.bytesKeyAt_intro $$ Hb
    iapply adt.bytesKeyAt_intro $$ He
  iapply HΦ
  ihave Ht := adt.ownIvtT_K _ _ _ _ $$ Ht
  iframe Ht
  (try simp only [adt.bytesKey_keyAt])
  isplitl [Hb]
  · iapply adt.bytesKeyAt_elim $$ Hb
  isplitl [He]
  · iapply adt.bytesKeyAt_elim $$ He
  ipureintro; intro hq; rw [Hres]; exact adt.containsT_eq _ T hs hq

end proof

end EtcdGrove
end Perennial
