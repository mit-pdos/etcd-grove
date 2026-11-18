-- The copy for the part `RaftNoAx/` of `Proof/github_com/mit_pdos/etcd_grove/examples/raft/kvdurable/RandomOptionsN.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvdurablenoax/RandomOptionsN.lean`. Lean-first
(no Rocq counterpart; 2026-11-16, kvraftN): `RandomOptions()`'s options (`OptsOk`), their voters set
to `k` and their replicas to `k + 4`.
-/
module

public import RaftNoAx.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.RandomOptionsN
public import RaftNoAx.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.RandomOptions

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.Assumptions]

theorem RandomOptionsN.wp_proof (wp_RandomOptions : RandomOptions.spec (GF := GF) (hG := hG)) :
    RandomOptionsN.spec (GF := GF) (hG := hG) := by
  intro k Hk1 Hk
  wp_start as #Hpkg
  try wp_auto
  wp_apply wp_RandomOptions as %o %Ho
  try wp_auto
  iapply HΦ
  ipureintro
  obtain ⟨⟨_, _, Hm1, Hm2, Hsz⟩, _⟩ := Ho
  refine ⟨⟨by word, ⟨by word, by word⟩, Hm1, Hm2, Hsz⟩, rfl, rfl⟩

end proof

end raft_kvdurable
end EtcdGrove
end Perennial
