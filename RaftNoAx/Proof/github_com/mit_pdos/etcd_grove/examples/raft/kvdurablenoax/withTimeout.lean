/- Lean-first (no Rocq counterpart); the part's own (raft without hand-written axioms,
`notes/raft-noax-part.md`). Proof of `withTimeout`'s spec.
-/
module

public import RaftNoAx.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.withTimeout

@[expose] public section

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

-- raft-noax: TODO prove `withTimeout` (Perennial's `wp_WithCancel_Background` and
-- `time.wp_AfterFunc`, theorems).
theorem withTimeout.wp_proof : withTimeout.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end raft_kvdurable
end EtcdGrove
end Perennial
