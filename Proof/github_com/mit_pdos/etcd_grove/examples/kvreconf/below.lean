/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/below.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.below
public import Perennial.Proof.github_com.goose_lang.primitive.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]

theorem below.wp_proof : below.spec (GF := GF) (hG := hG) := by
  intro n
  wp_start
  wp_auto
  wp_if_destruct
  · iapply HΦ
    ipureintro; exact ⟨fun _ => rfl, fun h => absurd rfl h⟩
  wp_apply github_com.goose_lang.primitive.wp_RandomUint64 as %r _
  rw [if_neg (show ¬ uint.Z n = 0 by intro h; apply Hif; word)]
  wp_auto
  iapply HΦ
  ipureintro
  refine ⟨fun h => absurd h Hif, fun _ => ?_⟩
  have h0 : 0 < n.toNat := by
    rcases Nat.eq_zero_or_pos n.toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) Hif
    · exact h
  have : (r % n).toNat < n.toNat := by rw [BitVec.toNat_umod]; exact Nat.mod_lt _ h0
  show ((r % n).toNat : Int) < (n.toNat : Int)
  omega

end proof

end kvreconf
end EtcdGrove
end Perennial
