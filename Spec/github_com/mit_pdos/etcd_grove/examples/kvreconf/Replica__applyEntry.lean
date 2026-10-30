/- Lean-first (no Rocq counterpart).

`r.applyEntry(e)` (kv.go): the committed entry `e` (read-only at `ep`, at index `len ap + 1`) applied
after the committed prefix `ap` of the committed log delivered `l`: by its type, an operation
(`applyOp`), a conf change decoded and decided (`applyConf`; a committed conf entry decodes, the
store's invariant, so the `panic` is unreachable), or nothing; then the index field moves to it. The
applier's replicated state and its view of the node move to `ap ++ [e]`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Defs

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
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [StorageModel GF] [AllG GF]

/-- See the file header. -/
abbrev Replica.applyEntry.spec : Prop :=
  ∀ (γr : RNames) (vs : List w64) (id : w64) (r n st sts : Loc) (q : Qp)
    (ap : List LogEntry) (idx : w64) (csp : Loc) (m : Membership) (mA : Loc)
    (A : GMap (List w8) (List w8)) (l : List LogEntry) (e : LogEntry) (ep : Loc),
  ap ++ [e] <+: l → ((ap.length : Int) + 1 < 2 ^ 61) →
  {{ isReplica γr vs id r n st sts ∗ repOwn γr r ap idx csp m mA A ∗
      appNode γr n l ap.length m ∗ entRO ep (e.toEntryM (W64 (ap.length + 1))) ∗
      isCommittedLogLb γr.cluster l ∗ nodeRunning n γr.cluster kvrRaftN q }}
    (App (Val (r @!! go.GoType.PointerType rReplicaTy @!! go!"applyEntry")) (Val #ep))
  {{ RET #(); ∃ (csp' : Loc) (m' : Membership) (A' : GMap (List w8) (List w8)),
      repOwn γr r (ap ++ [e]) (W64 (ap.length + 1)) csp' m' mA A' ∗
      appNode γr n l (ap.length + 1) m' ∗ nodeRunning n γr.cluster kvrRaftN q }}

end spec

end kvreconf
end EtcdGrove
end Perennial
