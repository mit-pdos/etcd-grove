/- Lean-first (no Rocq counterpart).

`deliver(peers, tr, ms)` (cluster.go): the transport. For the messages of a `Ready` as `Ready`
hands them out (raft v3.7, 2026-10-16, stage R6b, D8: the pointers' slice, owned; each message
owned at `readyDq` -- whole, but a response at half --, legitimately sent, `isRaftMsg`, of a term
within the budget, `termLB`) and a read-only peer table whose node at each id is that id's
(`peerOk`), it steps each deliverable message into its target, which takes it for good
(`Node.Step`'s `stepP`: the message at `1`, Q3; its entries slice a fresh copy with its
capacity, which a `MsgApp`'s receiver may adopt). (2026-10-13) It takes each message's read
credit (`Ready`'s) and passes a delivered message's on to `Step`, dropping the others' with
their messages. And (2026-10-13) a `MsgTimeoutNow` is stepped only with a tick credit taken
from the transfer budget `tr` (`isTransfers`, `transfers.take`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Cluster

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [StorageModel GF]

/-- See the file header. -/
abbrev deliver.spec : Prop :=
  ∀ (γ : RaftNames) (bud : BudgetNames) (peers tr : Loc) (P : GMap w64 GoInterface)
    (msl : GoSlice) (ms : List QMsg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv ∗
      peers ↦${DFrac.discard} P ∗ ([∗map] id ↦ nd ∈ P, peerOk γ bud id nd) ∗
      isTransfers bud tr ∗
      msl ↦* ms.map QMsg.loc ∗
      ([∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st ∗ isRaftMsg γ q.st ∗
        termLB bud q.st.msg.Term') ∗
      [∗list] q ∈ ms, rdCred γ (if q.st.msg.Type' = MsgReadIndex then 1 else 0) }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kv.deliver))
      (Val #peers)) (Val #tr)) (Val #msl))
  {{ RET #(); True }}

end spec

end kv
end EtcdGrove
end Perennial
