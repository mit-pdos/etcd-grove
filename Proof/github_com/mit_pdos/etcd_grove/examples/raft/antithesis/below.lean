/-
Lean-first (no Rocq counterpart). #33 S4: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/below.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.below
public import Perennial.Proof.github_com.goose_lang.primitive.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

theorem below.wp_proof : below.spec (GF := GF) (hG := hG) := by
  intro n hn
  wp_start
  wp_auto
  wp_apply github_com.goose_lang.primitive.wp_RandomUint64 as %r _
  rw [if_neg (show ¬ uint.Z n = 0 by omega)]
  wp_auto
  iapply HΦ
  ipureintro
  have h0 : 0 < n.toNat := by
    have : (uint.Z n) = (n.toNat : Int) := rfl
    omega
  have : (r % n).toNat < n.toNat := by rw [BitVec.toNat_umod]; exact Nat.mod_lt _ h0
  show ((r % n).toNat : Int) < (n.toNat : Int)
  omega

end proof

end AntHarness
end EtcdGrove
end Perennial
