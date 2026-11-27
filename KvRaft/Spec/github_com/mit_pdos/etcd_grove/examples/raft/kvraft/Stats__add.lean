/-
`s.add(i)` (`examples/raft/kvraft/stats.go`): one more of the counter `i` (one of the `numStats`), under the
counters' mutex (`isStats`, `TransportDefs.lean`). The counters are for the tests' coverage report;
no proof reads them, so the post says nothing of them.
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.TransportDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Net go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev Stats.add.spec : Prop :=
  ∀ (s : Loc) (i : w64), 0 ≤ sint.Z i → sint.Z i < numStats →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗
      isStats s }}
    (App (Val (s @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Stats.ty
      @!! go!"add")) (Val #i))
  {{ RET #(); True }}

end spec

end kvraft
end EtcdGrove
end Perennial
