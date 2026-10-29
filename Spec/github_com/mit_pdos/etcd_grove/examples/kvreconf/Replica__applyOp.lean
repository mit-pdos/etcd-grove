/- Lean-first (no Rocq counterpart).

`r.applyOp(data)` (kv.go): one committed normal entry `e` (its data `data`) applied after the
committed prefix `ap`: the applier's replicated state moves to `ap ++ [e]` (its index field
unchanged: `applyEntry` moves it), and the operation's waiter here, if any, is answered.
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
abbrev Replica.applyOp.spec : Prop :=
  ∀ (RA : RaftAssume (GF := GF)) (γr : RNames) (id : w64) (n r : Loc) (ap : List LogEntry)
    (idx : w64) (csp : Loc) (m : Membership) (mA : Loc) (A : GMap (List w8) (List w8))
    (e : LogEntry) (dsl : GoSlice),
  e.type = W32 0 → ((ap.length : Int) + 1 < 2 ^ 61) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvreconf ∗
      sync.isMutex (r.[RReplica, go!"mu"]) (lockInv γr id r) ∗
      repOwn RA γr n r ap idx csp m mA A ∗ dsl ↦*□ e.data ∗
      isCommittedLogLb γr.cluster (ap ++ [e]) }}
    (App (Val (r @!! go.GoType.PointerType rReplicaTy @!! go!"applyOp")) (Val #dsl))
  {{ RET #(); ∃ A', repOwn RA γr n r (ap ++ [e]) idx csp m mA A' }}

end spec

end kvreconf
end EtcdGrove
end Perennial
