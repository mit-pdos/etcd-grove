/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/tracecheck/below.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.below
public import Perennial.Proof.github_com.goose_lang.primitive.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace TraceCheck

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]

theorem below.wp_proof : below.spec (GF := GF) (hG := hG) := by
  intro n Hn
  wp_start
  wp_auto
  wp_apply github_com.goose_lang.primitive.wp_RandomUint64 as %r _
  have Hn0 : ¬ uint.Z n = 0 := by intro h; word
  rw [if_neg Hn0]
  wp_auto
  iapply HΦ
  ipureintro
  have h0 : 0 < n.toNat := by
    rcases Nat.eq_zero_or_pos n.toNat with h | h
    · exact absurd (by simpa using h) Hn0
    · exact h
  have hlt : (r % n).toNat < n.toNat := by rw [BitVec.toNat_umod]; exact Nat.mod_lt _ h0
  have hlt' : uint.Z (r % n) < uint.Z n := by
    show ((r % n).toNat : Int) < (n.toNat : Int)
    omega
  constructor <;> word

end proof

end TraceCheck
end EtcdGrove
end Perennial
