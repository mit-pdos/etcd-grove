/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/lib/cluster3/below.lean`: `RandomUint64` (Perennial's
result, used directly) modulo `n`, which is not zero. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.below
public import Perennial.Proof.github_com.goose_lang.primitive.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cluster3

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Assumptions]

theorem below.wp_proof : below.spec (GF := GF) (hG := hG) := by
  intro n hn
  wp_start as #Hpkg
  (try wp_auto)
  wp_apply github_com.goose_lang.primitive.wp_RandomUint64 as %r -
  (try wp_auto)
  rw [ite_eq_right_of_eq_false _ _ (eq_false hn)]
  (try wp_auto)
  iapply HΦ
  ipureintro
  have hpos : 0 < n.toNat := by
    have : 0 < uint.Z n := by word
    exact_mod_cast this
  have h := Nat.mod_lt r.toNat hpos
  rw [← BitVec.toNat_umod] at h
  exact_mod_cast h

end proof

end cluster3
end EtcdGrove
end Perennial
