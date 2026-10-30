/-
**etcd's specs of the KV service with auth on** (the auth plan's E3zb, 2026-10-28;
`KVService.lean`'s, for a member started with auth on): metadata-indexed gRPC specs
(`GrpcSpecMd`), whose replies carry what the server's answers with auth on add
(`v3rpc.srvKVAnsOn`) at the token of the metadata the handler sees (`auth.mdTokenOf`, what
`AuthInfoFromCtx` reads of its context, `auth.ctxTokenOf`):
- a write (`Put`, `DeleteRange`, a writing `Txn`): its grant (`v3rpc.writeGrantOn`: the request with
  the header the server stamped was granted at the committed log before its entry, the header's user
  the empty one or the one the token was issued to, and the entry committed);
- a read (`Range`, a read-only `Txn`), at a lower bound `n` of the auth store's published index the
  caller gives (`auth.authPubLbM`; `0` is free): its check's class (`v3rpc.rangeAuthed`,
  `v3rpc.txnAuthed`: the permissions it saw granted at states recorded at an index at least `n`,
  for an auth info that is the caller's).
The requests the permission cache decides: a delete's key and range end, a writing transaction's
every permission (`auth.reqShape`, `kvShapeAll`). Otherwise as auth off: the replies are
`putReplied`, `rangeReplyOk`, `deleteReplied`, `txnReplied` (the mode-`on` model's state is the
state of the log read, `kvStM true`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.KVService
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ServerKVOn

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **etcd's `Put` with auth on**: `etcdPutSpec`'s, the caller's update told the put's grant at
the token of the attempt's metadata when it fires (`v3rpc.kvOpAuOn`, 5a), the reply also with the
grant. -/
def etcdPutSpecOn (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (cid mid : w64) :
    GrpcSpecMd (GF := GF) pbPutRequest pbPutResponse :=
  fun md (o : OpFull) (Φ : PutRespM → IProp GF) =>
    iprop(∃ F : mvcc.Log, mvcc.idxCert E.γ.idx F ∗
      ∃ Q : KVState → IProp GF, ⌜o.leaseID = W64 0⌝ ∗
        v3rpc.kvOpAuOn s E ρ (auth.mdTokenOf md) (.put o) Q ∗
        ∀ m : PutRespM, putReplied E ρ.rd F o Q cid mid m -∗
          v3rpc.writeGrantOn s E ρ (auth.mdTokenOf md) (irrPut o) -∗ Φ m)

/-- **etcd's `DeleteRange` with auth on**: `etcdDeleteSpec`'s, for a key and range end of the
shape the permission cache decides, the caller's update told the delete's grant (`v3rpc.kvOpAuOn`),
the reply also with the grant. -/
def etcdDeleteSpecOn (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (cid mid : w64) :
    GrpcSpecMd (GF := GF) pbDeleteRangeRequest pbDeleteRangeResponse :=
  fun md (o : OpFull) (Φ : DelRespM → IProp GF) =>
    iprop(⌜auth.reqShape o.key o.base.rangeEnd⌝ ∗ ∃ F : mvcc.Log, mvcc.idxCert E.γ.idx F ∗
      ∃ Q : KVState → IProp GF, ⌜o.base.rangeEnd ≠ [W8 0]⌝ ∗
        v3rpc.kvOpAuOn s E ρ (auth.mdTokenOf md) (.deleteRange o) Q ∗
        ∀ m : DelRespM, deleteReplied E ρ.rd F o Q cid mid m -∗
          v3rpc.writeGrantOn s E ρ (auth.mdTokenOf md) (irrDeleteRange o) -∗ Φ m)

/-- **etcd's `Range` with auth on**: `etcdRangeSpec`'s, with a lower bound `n` of the published
auth index, the reply also with the read's check (`rangeAuthed`). -/
def etcdRangeSpecOn (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64) :
    GrpcSpecMd (GF := GF) pbRangeRequest pbRangeResponse :=
  fun md (o : OpFull) (Φ : RangeRespM → IProp GF) =>
    iprop(∃ (c : w64) (F : mvcc.Log) (Q : KVState → IProp GF) (n : Nat), committedAtLeast γr c ∗
      mvcc.idxCert E.γ.idx F ∗ auth.authPubLbM E.authMode n ∗
      (⌜Q = fun _ => iprop(True)⌝ ∨ (⌜o.base.serializable = false⌝ ∗ kvReadAu γr.kv Q)) ∗
      ∀ m : RangeRespM, rangeReplyOk E γr c F o cid mid Q m -∗
        v3rpc.rangeAuthed s E γr c n (auth.mdTokenOf md) o -∗ Φ m)

/-- **A transaction's auth facts, as its reply carries them** (persistent): a read-only one's
check (`txnAuthed`), a writing one's grant. -/
def txnAuthOn (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64) (n : Nat)
    (tok : Option GoString) (t : TxnModel) : IProp GF :=
  if txn.txnReadonly t then v3rpc.txnAuthed s E γr c n tok t
  else iprop(∃ tw : txn.TxnModelW, ⌜tw.toModel = t⌝ ∗ v3rpc.writeGrantOn s E ρ tok (irrTxn tw))

instance txnAuthOn_persistent (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (c : w64) (n : Nat) (tok : Option GoString) (t : TxnModel) :
    Persistent (txnAuthOn (GF := GF) s E ρ γr c n tok t) := by
  unfold txnAuthOn; split <;> infer_instance

/-- **etcd's `Txn` with auth on**: `etcdTxnSpec`'s, a writing transaction's every permission of the
shape the permission cache decides, with a lower bound `n` of the published auth index, the reply
also with the transaction's auth facts (`txnAuthOn`), a writing one's update told its grant
(`v3rpc.kvOpAuOn`). -/
def etcdTxnSpecOn (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (cid mid : w64) :
    GrpcSpecMd (GF := GF) pbTxnRequest pbTxnResponse :=
  fun md (t : TxnModel) (Φ : TxnRespM → IProp GF) =>
    iprop(⌜TxnModel.plain t ∧ txnModelIn t ∧ (txn.txnReadonly t = false →
        ∀ tw : txn.TxnModelW, tw.toModel = t → kvShapeAll (irrTxn tw))⌝ ∗
      ∃ Q : KVState → IProp GF,
      (⌜txn.txnReadonly t = true ∧ Q = fun _ => iprop(True)⌝ ∨
        (⌜txn.txnReadonly t = true ∧ txn.txnSerializable t = false⌝ ∗ kvReadAu γr.kv Q) ∨
        (⌜txn.txnReadonly t = false ∧ txn.txnPlain t ∧ txnNoZeroEnd t⌝ ∗
          v3rpc.kvOpAuOn s E ρ (auth.mdTokenOf md) (.txn t) Q)) ∗
      ∃ (c : w64) (F : mvcc.Log) (n : Nat), committedAtLeast γr c ∗
      mvcc.idxCert E.γ.idx F ∗ auth.authPubLbM E.authMode n ∗
      ∀ m : TxnRespM, txnReplied E ρ.rd γr c F t Q cid mid m -∗
        txnAuthOn s E ρ γr c n (auth.mdTokenOf md) t -∗ Φ m)

/-- **A client write's grant** (persistent; the auth-mode merge's 5a, 2026-10-29): the write's grant
(`v3rpc.opGrantT`) at the token of some attempt of the call `ctx` on `conn` (the caller does not
know which attempt's metadata the server saw). -/
def clientGrant (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (conn : Loc) (ctx : GoInterface)
    (op : KVOp) (L₀ : List EntryModel) (σ : KVState) : IProp GF :=
  iprop(∃ md, ⌜clientAttemptMd conn ctx md⌝ ∗ v3rpc.opGrantT s E ρ (auth.mdTokenOf md) op L₀ σ)

/-- **A client write's update with auth on** (5a): `v3rpc.kvOpAuOn`'s, fired at most once, at a
lower bound `L₀` of the requested log the caller holds, told the grant of some attempt
(`clientGrant`) when it fires. -/
def clientOpAuOn (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (conn : Loc) (ctx : GoInterface)
    (op : KVOp) (Q : KVState → IProp GF) : IProp GF :=
  iprop(∃ L₀ : List EntryModel, srvReqLogLb ρ.raft L₀ ∗
    kvAu1G ρ.kv (kvOpStep op) (clientGrant s E ρ conn ctx op L₀) Q)

/-- A client's update is one at the token of each of its attempts. -/
theorem clientOpAuOn_attempt (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (conn : Loc)
    (ctx : GoInterface) (md : GrpcMd) (op : KVOp) (Q : KVState → IProp GF)
    (hmd : clientAttemptMd conn ctx md) :
    clientOpAuOn (GF := GF) s E ρ conn ctx op Q ⊢ v3rpc.kvOpAuOn s E ρ (auth.mdTokenOf md) op Q := by
  unfold clientOpAuOn v3rpc.kvOpAuOn
  iintro ⟨%L₀, #H0, Hau⟩
  iexists L₀
  iframe H0
  iapply (kvAu1G_mono ρ.kv (kvOpStep op) (clientGrant s E ρ conn ctx op L₀)
    (v3rpc.opGrantT s E ρ (auth.mdTokenOf md) op L₀) Q ?_) $$ Hau
  intro σ
  unfold clientGrant
  iintro Hg
  iexists md
  iframe Hg
  ipureintro; exact hmd

/-- An update not told the grant is one (at the empty lower bound). -/
theorem clientOpAuOn_of_au1 (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (conn : Loc)
    (ctx : GoInterface) (op : KVOp) (Q : KVState → IProp GF) :
    kvOpAu1 (GF := GF) ρ.kv op Q ⊢ |==> clientOpAuOn s E ρ conn ctx op Q := by
  iintro H
  imod srvReqLogLb_nil (GF := GF) ρ.raft with #H0
  imodintro
  unfold clientOpAuOn
  iexists []
  iframe H0
  unfold kvOpAu1
  iapply kvAu1_G $$ H

/-- **A transaction's update with auth on** (5a): `txnUpdAt`'s, a writing one's update told the
grant of some attempt of the call (`clientOpAuOn`). -/
def txnUpdAtOn (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (conn : Loc) (ctx : GoInterface)
    (γr : ReadNames) (t : TxnModel) (Q : KVState → IProp GF) : IProp GF :=
  iprop(⌜txn.txnReadonly t = true ∧ Q = fun _ => iprop(True)⌝ ∨
    (⌜txn.txnReadonly t = true ∧ txn.txnSerializable t = false⌝ ∗ kvReadAu γr.kv Q) ∨
    (⌜txn.txnReadonly t = false ∧ txn.txnPlain t ∧ txnNoZeroEnd t⌝ ∗
      clientOpAuOn s E ρ conn ctx (.txn t) Q))

end defs

end client
end EtcdGrove
end Perennial
