/- Lean-first (no Rocq counterpart).

`r.maybeCompact(snapIndex)` (kv.go): after an `Advance`, the applier at the committed prefix `ap`
(`repOwn`, read only; `r.index = len ap`) compacts its storage to some index from its first one to
the least of `len ap` and the stored snapshot's index `snapIndex` (`memSnapExact`), if there is one.
`Compact` needs the entry there frozen (`frozenTo` of `ap` above the known compaction point `c`, the
first index being past `c`) and justified (`J.B`: the node applied `ap`, `nodeAppliedLb`, which
`Advance` gives). Nothing changes that the applier sees: compaction points are lower bounds.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.DefsCluster

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KvrStor GF]

attribute [local instance] kvrStorageModel

/-- See the file header. -/
abbrev Replica.maybeCompact.spec : Prop :=
  ∀ (γr : RNames) (vs : List w64) (id : w64) (r n st sts : Loc) (ρ : RepNames)
    (ap : List LogEntry) (csp : Loc) (m : Membership) (mA : Loc) (A : GMap (List w8) (List w8))
    (c : Nat) (sv0 : SnapshotM) (snapIndex : w64),
  sv0.Metadata'.Index' = snapIndex →
  {{ isReplicaR γr vs id r n st sts ρ ∗ repOwn γr r ap (W64 ap.length) csp m mA A ∗
      memSnapExact ρ.γs sv0 ∗ memCompacted ρ.γs c ∗ frozenTo ρ.γs c ap ∗
      nodeAppliedLb γr.cluster id ap.length }}
    (App (Val (r @!! go.GoType.PointerType rReplicaTy @!! go!"maybeCompact")) (Val #snapIndex))
  {{ RET #(); repOwn γr r ap (W64 ap.length) csp m mA A ∗ memSnapExact ρ.γs sv0 }}

end spec

end kvreconf
end EtcdGrove
end Perennial
