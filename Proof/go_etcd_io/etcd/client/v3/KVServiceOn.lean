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

theorem auth.ctxTokenOf_md [GooseExts] (ctx : GoInterface) :
    auth.ctxTokenOf ctx = auth.mdTokenOf (metadata.incomingOf ctx) :=
  rfl

namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **etcd's `Put` with auth on**: `etcdPutSpec`'s, the reply also with the put's grant at the
token of the attempt's metadata. -/
def etcdPutSpecOn (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (cid mid : w64) :
    GrpcSpecMd (GF := GF) pbPutRequest pbPutResponse :=
  fun md (o : OpFull) (Φ : PutRespM → IProp GF) =>
    etcdPutSpec E ρ.rd cid mid o
      (fun m => iprop(v3rpc.writeGrantOn s E ρ (auth.mdTokenOf md) (irrPut o) -∗ Φ m))

/-- **etcd's `DeleteRange` with auth on**: `etcdDeleteSpec`'s, for a key and range end of the
shape the permission cache decides, the reply also with the delete's grant. -/
def etcdDeleteSpecOn (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (cid mid : w64) :
    GrpcSpecMd (GF := GF) pbDeleteRangeRequest pbDeleteRangeResponse :=
  fun md (o : OpFull) (Φ : DelRespM → IProp GF) =>
    iprop(⌜auth.reqShape o.key o.base.rangeEnd⌝ ∗ etcdDeleteSpec E ρ.rd cid mid o
      (fun m => iprop(v3rpc.writeGrantOn s E ρ (auth.mdTokenOf md) (irrDeleteRange o) -∗ Φ m)))

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
also with the transaction's auth facts (`txnAuthOn`). -/
def etcdTxnSpecOn (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (cid mid : w64) :
    GrpcSpecMd (GF := GF) pbTxnRequest pbTxnResponse :=
  fun md (t : TxnModel) (Φ : TxnRespM → IProp GF) =>
    iprop(⌜TxnModel.plain t ∧ txnModelIn t ∧ (txn.txnReadonly t = false →
        ∀ tw : txn.TxnModelW, tw.toModel = t → kvShapeAll (irrTxn tw))⌝ ∗
      ∃ Q : KVState → IProp GF,
      (⌜txn.txnReadonly t = true ∧ Q = fun _ => iprop(True)⌝ ∨
        (⌜txn.txnReadonly t = true ∧ txn.txnSerializable t = false⌝ ∗ kvReadAu γr.kv Q) ∨
        (⌜txn.txnReadonly t = false ∧ txn.txnPlain t ∧ txnNoZeroEnd t⌝ ∗
          kvOpAu1 ρ.rd.kv (.txn t) Q)) ∗
      ∃ (c : w64) (F : mvcc.Log) (n : Nat), committedAtLeast γr c ∗
      mvcc.idxCert E.γ.idx F ∗ auth.authPubLbM E.authMode n ∗
      ∀ m : TxnRespM, txnReplied E ρ.rd γr c F t Q cid mid m -∗
        txnAuthOn s E ρ γr c n (auth.mdTokenOf md) t -∗ Φ m)

end defs

end client
end EtcdGrove
end Perennial
