/-
The results of etcd's gRPC KV service (`server/v3/etcdserver/api/v3rpc`: the handlers of
`key.go`, the request checks, the response header, `togRPCError`), restated at top level, with
the trust base of each printed in the build log (`#print axioms`). Lean-first (no Rocq
counterpart); plan: `notes/decisions.md`, "The request path".

Unit 1 (2026-10-12): every function of `key.go` but `kvServer.RangeStream` and
`kvServer.Compact`, of `header.go` and `util.go`'s `togRPCError` specified and proved
(`Link.lean`). The results:
* **`check_gives_nodup`** (`CheckNodup.lean`; `intervalsOkCheckStmt_holds`): a branch passing
  `checkRequestOp` (non-empty keys) and `checkIntervals` with no from-key delete and no nested put a later sibling deletes, run by the server, writes each key at most
  once; with the txn package's `keys_nodup_iff_check`, `checkIntervals_nodup` below: the changes'
  keys are distinct (`NoDupKeysPerRev`'s per-transaction part). The two exclusions are the
  code's findings (`issues/etcd-txn-delete-then-ignore-put.md`,
  `issues/etcd-txn-check-intervals-sibling.md`).
* **`checkRequestOp_nonempty`**: a transaction passing `checkTxnRequest` has no empty
  operation at any depth (the txn package's `etcd-txn-empty-requestop` precondition discharged at
  the API).
* **`checkTxnRequest_ok`**: `checkTxnRequest` purely.
* **`put_handler`**: `kvServer.Put`'s answer is the server's `Put` answer (`A.ok`, units 2/3's)
  with the header filled, or the check's error, or the server's error through `togRPCError`; the
  same for `Range`, `DeleteRange` and `Txn` (`range_handler`, `deleteRange_handler`,
  `txn_handler`, the last over the interval tree's pending contract).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Link
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.CheckPure
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.CheckNodup

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

open Iris Iris.BI

/-- **`checkIntervals` gives distinct keys** (see `check_gives_nodup`): a branch `ops` passing
`checkRequestOp` and `checkIntervals`, with no from-key delete and no nested put a later sibling deletes, run by the
server whose deletes are of present keys (`DelsPresent`, which a run gives), changes each key at
most once. -/
theorem checkIntervals_nodup (n : Int) (ops : List ReqOp) (tops : List TxnOp) (s0 s : List EtcdKv)
    (r : w64) (hops : ReqOp.toTxnOps ops = some tops) (hck : opsCheck n ops = none)
    (hfk : ReqOp.noFromKeyDelL ops)
    (hsib : ReqOp.siblingSafeL ops) (hiv : intervalsOk ops)
    (hdel : txn.DelsPresent r s (txn.srvOps s0 r s tops).1) :
    ((txn.srvOps s0 r s tops).1.map mvcc.Change.key).Nodup :=
  (txn.keys_nodup_iff_check _ s hdel).2 (check_gives_nodup n ops tops s0 s r hops hck hfk hsib hiv)

/-- **An empty operation is rejected** at any depth: a transaction passing `checkTxnRequest`
has the txn package's model (no empty `RequestOp`, the `etcd-txn-empty-requestop` precondition). -/
theorem checkRequestOp_nonempty {n : Int} {cs : List CmpModel} {ts es : List ReqOp}
    (h : txnReqOk n cs ts es) :
    ∃ ts' es', ReqOp.toTxnOps ts = some ts' ∧ ReqOp.toTxnOps es = some es' :=
  txnCheck_toTxnOps h

/-- **`checkTxnRequest`, purely**: passes iff the widest of the comparisons and branches is
within the budget, every comparison has a key, and every operation passes at the budget less
that width. -/
theorem checkTxnRequest_ok (n : Int) (cs : List CmpModel) (ts es : List ReqOp) :
    txnReqOk n cs ts es ↔
      (txnWidth cs ts es : Int) ≤ n ∧ (∀ c ∈ cs, c.key ≠ []) ∧
        (∀ u ∈ ts, requestOpOk (n - txnWidth cs ts es) u) ∧
        (∀ u ∈ es, requestOpOk (n - txnWidth cs ts es) u) :=
  txnCheck_ok_iff n cs ts es

section handlers
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`kvServer.Put`**: the server's `Put` answer with the header filled (`kvOut`), or the
check's error. -/
theorem put_handler : EtcdGrove.v3rpc.kvServer.Put.spec (GF := GF) (hG := hG) :=
  kvServer.wp_Put

theorem range_handler : EtcdGrove.v3rpc.kvServer.Range.spec (GF := GF) (hG := hG) :=
  kvServer.wp_Range

theorem deleteRange_handler : EtcdGrove.v3rpc.kvServer.DeleteRange.spec (GF := GF) (hG := hG) :=
  kvServer.wp_DeleteRange

end handlers

end v3rpc

#print axioms Perennial.EtcdGrove.v3rpc.checkIntervals_nodup
#print axioms Perennial.EtcdGrove.v3rpc.check_gives_nodup
#print axioms Perennial.EtcdGrove.v3rpc.intervalsOkCheckStmt_holds
#print axioms Perennial.EtcdGrove.v3rpc.intervalsOkNoKeysStmt_false
#print axioms Perennial.EtcdGrove.v3rpc.checkRequestOp_nonempty
#print axioms Perennial.EtcdGrove.v3rpc.checkTxnRequest_ok
#print axioms Perennial.EtcdGrove.v3rpc.put_handler
#print axioms Perennial.EtcdGrove.v3rpc.range_handler
#print axioms Perennial.EtcdGrove.v3rpc.deleteRange_handler
#print axioms Perennial.EtcdGrove.v3rpc.kvServer.wp_Txn
#print axioms Perennial.EtcdGrove.v3rpc.wp_NewKVServer
#print axioms Perennial.EtcdGrove.v3rpc.headerFillingRangeStream.wp_Send
#print axioms Perennial.EtcdGrove.v3rpc.wp_checkRangeStreamRequest
#print axioms Perennial.EtcdGrove.v3rpc.wp_togRPCError

end EtcdGrove
end Perennial
