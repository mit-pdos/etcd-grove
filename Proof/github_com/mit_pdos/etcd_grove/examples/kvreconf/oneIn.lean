/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/oneIn.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.oneIn
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

theorem oneIn.wp_proof : oneIn.spec (GF := GF) (hG := hG) := by
  intro n Hn
  wp_start
  wp_auto
  wp_apply github_com.goose_lang.primitive.wp_RandomUint64 as %r _
  rw [if_neg (show ¬ uint.Z n = 0 by intro h; apply Hn; word)]
  wp_auto
  iapply HΦ
  ipureintro; trivial

end proof

end kvreconf
end EtcdGrove
end Perennial
