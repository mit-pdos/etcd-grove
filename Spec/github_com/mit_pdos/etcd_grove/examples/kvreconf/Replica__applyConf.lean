/- Lean-first (no Rocq counterpart).

`r.applyConf(cc)` (kv.go): the committed conf entry `e` (the change `o` it decodes to, `cc`
read-only, its transition defined, `ccTransOk`) applied after the committed prefix `ap`, at the
membership `m` of the applier's configuration: the store's decision on it (`kvrRule`: the change if
`validConf` accepts it at `m`, else a rejection) moves the applier's replicated state to `ap ++ [e]`
at the membership after it (its index field unchanged: `applyEntry` moves it), and its view of the
node past it (`appNode`: the node applied the change, or the entry was skipped). The applier holds a
fraction of `nodeRunning` (the node does not stop under it), which refutes the node's `nil` answer.
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
abbrev Replica.applyConf.spec : Prop :=
  ∀ (γr : RNames) (vs : List w64) (id : w64) (r n st sts : Loc) (q : Qp)
    (ap : List LogEntry) (idx : w64) (csp : Loc) (m : Membership) (mA : Loc)
    (A : GMap (List w8) (List w8)) (l : List LogEntry) (e : LogEntry) (c : GoInterface)
    (o : ConfChangeIM),
  ap ++ [e] <+: l → ccDecode e = some o → ccTransOk o → ((ap.length : Int) + 1 < 2 ^ 61) →
  {{ isReplica γr vs id r n st sts ∗ repOwn γr r ap idx csp m mA A ∗
      appNode γr n l ap.length m ∗ ownConfChangeI c DFrac.discard (some o) ∗
      isCommittedLogLb γr.cluster l ∗ nodeRunning n γr.cluster kvrRaftN q }}
    (App (Val (r @!! go.GoType.PointerType rReplicaTy @!! go!"applyConf")) (Val #c))
  {{ RET #(); ∃ (csp' : Loc) (m' : Membership), repOwn γr r (ap ++ [e]) idx csp' m' mA A ∗
      appNode γr n l (ap.length + 1) m' ∗ nodeRunning n γr.cluster kvrRaftN q }}

end spec

end kvreconf
end EtcdGrove
end Perennial
