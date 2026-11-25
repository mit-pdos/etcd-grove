/-
Proof of `oneIn` (kvdurable's, the same Go text): `primitive.RandomUint64() % n == 0`.
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.oneIn
public import Perennial.Proof.github_com.goose_lang.primitive.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvcheck

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.Assumptions]

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

end raft_kvcheck
end EtcdGrove
end Perennial
