/-
**What a write's or a transaction's reply says of the state it linearized at** (linkv-txn stage
B3, 2026-10-20; `notes/linkv-txn-plan.md`): for each successful reply (`putReplied`,
`deleteReplied`, `txnReplied`), the state `σ` its client's update fired at (`Q σ`, or `□ Q σ` for
a read-only transaction's read update) and the reply's fields as functions of `σ`: a put's
revision (`σ`'s next) and previous key-value; a delete's count, revision (the state's after the
delete, `kvOpStep`'s) and previous key-values; a transaction's verdict, its branch's responses
and its revision (the state's after its writes, `KVState.commit`'s). As `client_get_value` and
`rangeReply_state` (`Results.lean`) for the reads. A writing transaction's ranges are run
(`skip = false`, linkv-txn stage B1: the reply reached a registered proposer). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.Results

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver
open mvcc

section values
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

end values

end client
end EtcdGrove
end Perennial
