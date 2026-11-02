/- Lean-first (no Rocq counterpart). kvreconf's (the same Go text), ported.

`r.applyConf(cc)` (kv.go): the committed conf entry `e` (the change `o` it decodes to, `cc`
read-only, its transition defined, `ccTransOk`) applied after the committed prefix `ap`, at the
membership `m` of the applier's configuration: the store's decision on it (`kvrRule`: the change if
`validConf` accepts it at `m`, else a rejection) moves the applier's replicated state to `ap ++ [e]`
at the membership after it (its index field unchanged: `applyEntry` moves it), and its view of the
node past it (`appNode`: the node applied the change, or the entry was skipped). The applier holds a
fraction of `nodeRunning` (the node does not stop under it), which refutes the node's `nil` answer.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open kvreconf (kvFold logHist AppliedOk ccTransOk)
open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

/-- See the file header. -/
abbrev Replica.applyConf.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (id : w64) (r n st sts sq ms : Loc)
    (γs : MemStorNames) (ph : KdDmuNames) (q : Qp)
    (ap : List LogEntry) (idx : w64) (csp : Loc) (m : Membership) (mA : Loc)
    (A : GMap (List w8) (List w8)) (l : List LogEntry) (e : LogEntry) (c : GoInterface)
    (o : ConfChangeIM),
  ap ++ [e] <+: l → ccDecode e = some o → ccTransOk o → ((ap.length : Int) + 1 < 2 ^ 61) →
  {{ isReplica γ vs dir id r n st sts sq ms γs ph ∗ repOwn γ r ap idx csp m mA A ∗
      appNode γ n l ap.length m ∗ ownConfChangeI c DFrac.discard (some o) ∗
      isCommittedLogLb γ.r.cluster l ∗ nodeRunning n γ.r.cluster kdRaftN q }}
    (App (Val (r @!! go.GoType.PointerType kReplicaTy @!! go!"applyConf")) (Val #c))
  {{ RET #(); ∃ (csp' : Loc) (m' : Membership), repOwn γ r (ap ++ [e]) idx csp' m' mA A ∗
      appNode γ n l (ap.length + 1) m' ∗ nodeRunning n γ.r.cluster kdRaftN q }}

end spec

end kvdurable
end EtcdGrove
end Perennial
