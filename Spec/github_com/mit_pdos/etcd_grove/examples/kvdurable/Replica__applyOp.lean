/- Lean-first (no Rocq counterpart). kvreconf's (the same Go text), ported.

`r.applyOp(data)` (kv.go): one committed normal entry `e` (its data `data`) applied after the
committed prefix `ap`: the applier's replicated state moves to `ap ++ [e]` (its index field
unchanged: `applyEntry` moves it), and the operation's waiter here, if any, is answered.
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
abbrev Replica.applyOp.spec : Prop :=
  ∀ (γ : KdNames) (id : w64) (r : Loc) (ap : List LogEntry)
    (idx : w64) (csp : Loc) (m : Membership) (mA : Loc) (A : GMap (List w8) (List w8))
    (e : LogEntry) (dsl : GoSlice),
  e.type = W32 0 → ((ap.length : Int) + 1 < 2 ^ 61) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvdurable ∗
      sync.isMutex (r.[KReplica, go!"mu"]) (lockInv γ id r) ∗
      repOwn γ r ap idx csp m mA A ∗ dsl ↦*□ e.data ∗
      isCommittedLogLb γ.r.cluster (ap ++ [e]) }}
    (App (Val (r @!! go.GoType.PointerType kReplicaTy @!! go!"applyOp")) (Val #dsl))
  {{ RET #(); ∃ A', repOwn γ r (ap ++ [e]) idx csp m mA A' }}

end spec

end kvdurable
end EtcdGrove
end Perennial
