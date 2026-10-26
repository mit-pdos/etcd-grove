/-
**etcd's KV service: the one spec of each method, as the server proves it and the client relies on
it** (D44, 2026-10-25; until then in `client/v3/Results.lean`). Lean-first (no Rocq counterpart).

**etcd's specs of the KV methods** (`etcdPutSpec`, `etcdRangeSpec`, `etcdDeleteSpec`,
`etcdTxnSpec`: predicate transformers over the messages' models, `GrpcSpec`, at a member's apply
environment, read names and ids): a caller asking the request `o` gets a reply message `m` with
`putReplied` (`putReplyOk`, persistent, and the token of the revision the put made, `revMinted`),
`rangeReplyOk` at the committed index `c` the caller knows of, `deleteReplied`, `txnReplied`. The
server's handlers meet them as grpc runs them (`Results.lean`'s `etcd_putMethodOk`, ...,
`etcd_kv_served`, `etcd_kv_started`), which registers them at the member's address
(`isGrpcRpc`).

**The members as the client sees them** (`SrvAt`: an address, an apply environment, read names,
ids) and their registrations (`kvRegsAt`). A call through a client of several members passes the
conjunction of their specs (`anySpec`, `isGrpcRpcs_anySpec`); the reply is that of the member
whose handler ran.

**The client's side at the members** (`isKV api ms`: the members' registrations; the terms the
members' lemmas of the `*kv`'s calls are stated in, `KVMembers.lean`: `kvPutSpec`, ..., `floorsAt`,
`knownAt`, `putUpd`, ..., `putAns`, ..., with the lemmas that a caller's side meets the members'
spec, `putSpec_of`, ...) and **the client's view** (the last section: `isKv api γ dup`, one KV with
its members hidden, the precondition of the calls' specs, and the reply's fields as functions of
the state the update fired at, `putStOk`, ...).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvKVConn
public import Proof.go_etcd_io.etcd.client.v3.InvTxnBuilder
public import Proof.go_etcd_io.etcd.cache.v3.InvEtcd
public import Proof.go_etcd_io.etcd.cache.v3.InvEtcdTxn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRequest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVModelDefs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVLogOk
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.InvUber
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Chain
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.TxnRun
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.RangeModel
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Write
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvIndex
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BucketLemmas
public import Spec.google_golang_org.protobuf.proto.MarshalIRR

@[expose] public section

set_option pp.fullNames true
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

/-! ## Plain operations -/

/-- An operation that is not a nested transaction (what the client's builder makes: `txnOpOf`
never gives one). -/
def TxnOp.plain : TxnOp → Prop
  | .txn _ _ _ => False
  | _ => True

/-- A transaction of plain operations, in both branches. -/
def TxnModel.plain (t : TxnModel) : Prop :=
  (∀ op ∈ t.thenOps, TxnOp.plain op) ∧ ∀ op ∈ t.elseOps, TxnOp.plain op

theorem opWire_plain (op : TxnOp) (h : TxnOp.plain op) : TxnOp.plain (opWire op) := by
  cases op <;> simp_all [TxnOp.plain, opWire]

theorem txnOpOf_plain (o : OpFull) (op : TxnOp) (h : txnOpOf o = some op) : TxnOp.plain op := by
  unfold txnOpOf at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq] at h; subst h; trivial)
    | cases h

/-! ## The response's model -/

mutual
/-- **A response message of an operation answers it** (`skip`: ranges header-only): the
message `m` of the server's response of the operation `op` with result `res` (the txn package's
`responseOpIs`): a get's count and key-values (as the range model's: `rangeKvsOk`, the leases
zeroed by a fast keys-only read), or nothing if header-only; a put's; a delete's count; a nested
transaction's verdict and its branch's responses. The inner headers' revisions and a put's or
delete's previous key-values are unconstrained (the server's `responseOpIs` leaves them so). -/
def opRespRel (skip : Bool) : TxnOp → TxnOpResult → OpRespM → Prop
  | .get o, .range sel n, .range _ kvs more count =>
      if skip then kvs = [] ∧ more = false ∧ count = W64 0
      else count = W64 (n : Int) ∧
        ∃ kvs', rangeKvsOk o sel kvs' ∧ kvs = kvs'.map (txn.leaseZ (txn.fastKeysOnly o))
  | .put .., .put, .put _ _ => True
  | .putKeep .., .put, .put _ _ => True
  | .putIgnVal .., .put, .put _ _ => True
  | .delete _, .delete n, .delete _ d _ => d = W64 (n : Int)
  | .txn _ ts es, .txn ok rs, .txn _ ok' ms =>
      ok' = ok ∧ (if ok then opRespsRel skip ts rs ms else opRespsRel skip es rs ms)
  | _, _, _ => False

/-- `opRespRel` of each operation, in order. -/
def opRespsRel (skip : Bool) : List TxnOp → List TxnOpResult → List OpRespM → Prop
  | [], [], [] => True
  | op :: ops, res :: rs, m :: ms => opRespRel skip op res m ∧ opRespsRel skip ops rs ms
  | _, _, _ => False
end

/-! ## What a transaction's reply tells the client -/

/-- **A transaction within the txn package's model** (`v3rpc.txnInModel` of the model; a
premise): each of its gets reads the transaction's revision and is not a sort cut early by a limit
(`txn.cutEarly`, `issues/etcd-range-sort-none-limit.md`). Until D19c (2026-10-18) of a read-only
transaction only; a writing one's gets are its apply's premise (`txn.txnShape`), which the KV
invariant now keeps of every committed entry. -/
def txnModelIn (t : TxnModel) : Prop :=
  ∀ o : OpFull, TxnOp.get o ∈ t.thenOps ++ t.elseOps → o.base.rev = W64 0 ∧ ¬ txn.cutEarly o

theorem txnWireOf_plain (t : TxnModel) (h : TxnModel.plain t) : TxnModel.plain (txnWireOf t) := by
  refine ⟨?_, ?_⟩
  · intro op hm
    simp only [txnWireOf, List.mem_map] at hm
    obtain ⟨op0, h0, rfl⟩ := hm
    exact opWire_plain op0 (h.1 op0 h0)
  · intro op hm
    simp only [txnWireOf, List.mem_map] at hm
    obtain ⟨op0, h0, rfl⟩ := hm
    exact opWire_plain op0 (h.2 op0 h0)

section reply
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **What a successful `Txn` of `t` delivers to the client** with the reply's message `m`, for a
client that knows the committed index `c` and has the floor `F` (the vertical slice's unit V2).
A read-only `t`: the server's run of `t` at a certified log extending `F`, after the read index
unless serializable (`readLogOk`), the header's revision its last; the verdict and the chosen
branch's responses the run's (`opRespsRel`). A writing `t`: the apply thread's application of
the request the proposed data decode to (`rq'`, whose transaction `t'` is `t` unless a range end
is `[0]`), at `x.log` extending `F`, the header's revision the write's; the verdict and the
responses the run's (ranges header-only if `skip`); mvcc's certificate of the log after and the
token minted (`revMinted`, exclusive: a reply's `Φ` is delivered once), with the write's witness
(`appliedWit γw`, unit C2a, at the request path's read names); unit W-M3: the caller's
certificate of the log read or written (`certOk`: its revisions are reached in the clients'
model) and `Q` of the state of the log the write met (the transaction's update fired there, at
most once: not persistent since 2026-10-20, linkv-txn stage A) or `□ Q`,
for a linearizable read-only `t`, of the log read (its read update, deposited with the read index,
fired there; as `rangeReplyOk`'s). -/
def txnReplied (E : apply.AEnv GF) (γw γr : ReadNames) (c : w64) (F : mvcc.Log) (t : TxnModel)
    (Q : KVState → IProp GF) (cid mid : w64) (m : TxnRespM) : IProp GF :=
  if txn.txnReadonly t then
    iprop(∃ log : mvcc.Log, mvcc.idxCert E.γ.idx log ∗ mvcc.certOk E.γ log ∗
      ⌜2 ≤ log.length ∧ log.length + 3 ≤ 2 ^ 63 ∧ F <+: log ∧
        m.hdr.revision = W64 ((log.length : Int) - 1) ∧ m.hdr.clusterId = cid ∧
        m.hdr.memberId = mid ∧
        m.succeeded = (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).1 ∧
        opRespsRel false (t.branch m.succeeded)
          (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.2 m.resps⌝ ∗
      (if txn.txnSerializable t then iprop(True) else readLogOk γr c log) ∗
      (if txn.txnSerializable t then iprop(True) else □ Q (kvStateOf log)))
  else
    iprop(∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel) (t' : TxnModel)
        (x x' : apply.ApplyKV) (l : mvcc.Log) (skip : Bool),
      ⌜irrWireOf (apply.withHeader (irrTxn t) hm) rq' ∧ rq'.txn = some t' ∧
        (irrNoZeroEnd (irrTxn t) → t' = t) ∧
        apply.applyStep rq' true x x' (.dispatched (.applied l false) skip) ∧
        m.hdr.revision = W64 (mvcc.writeRev x.log
          (txn.srvRunTxn (W64 (x.log.length : Int)) (mvcc.stateAfter x.log) t').2.1 : Int) ∧
        m.hdr.clusterId = cid ∧ m.hdr.memberId = mid ∧
        F <+: x.log ∧ 2 ≤ x.log.length ∧ x.log.length + 4 ≤ 2 ^ 63 ∧
        m.succeeded = (txn.srvRunTxn (W64 (x.log.length : Int)) (mvcc.stateAfter x.log) t').1 ∧
        opRespsRel skip (t'.branch m.succeeded)
          (txn.srvRunTxn (W64 (x.log.length : Int)) (mvcc.stateAfter x.log) t').2.2 m.resps ∧
        -- (linkv-txn stage B1, 2026-10-20) the ranges run
        skip = false⌝ ∗
      mvcc.idxCert E.γ.idx x'.log ∗ revMinted E x.log x'.log ∗ appliedWit γw x'.log ∗
      mvcc.certOk E.γ x'.log ∗ Q (kvStateOf x.log))

/-- **etcd's spec of the KV service's `Txn`** (the vertical slice's unit V2; a predicate
transformer, as `etcdPutSpec`): a caller asking a transaction `t` of plain operations (no nested
transaction: what the client's builder sends) within the txn package's model (`txnModelIn`: if
read-only, gets at the transaction's revision, no sort cut early by a limit), who knows the
committed index `c` and has the floor `F`, gets a reply message `m` with `txnReplied`. A writing
transaction (2026-10-15, unit T2) is plain in the KV model (`txn.txnPlain`: its gets at revision
`0`, its puts with no lease and no `IgnoreLease`), no range end `[0]` (`txnNoZeroEnd`), with the
caller's update over the whole state `kvOpAu1 (.txn t) Q` (fired at most once, since
2026-10-20, linkv-txn stage A; persistent `kvOpAu` until then), whose `Q` of the state it
linearized at the reply carries (unit W-M3: in `txnReplied`, at the state of the log the write
met); a read-only one takes none (`Q` trivial) or, linearizable (unit W-M3), a read update
(`kvReadAu`, at the read names, as `etcdRangeSpec`'s), whose `□ Q` at the state of the log read
the reply carries. -/
def etcdTxnSpec (E : apply.AEnv GF) (γw γr : ReadNames) (cid mid : w64) :
    GrpcSpec (GF := GF) pbTxnRequest pbTxnResponse :=
  fun (t : TxnModel) (Φ : TxnRespM → IProp GF) =>
    iprop(⌜TxnModel.plain t ∧ txnModelIn t⌝ ∗ ∃ Q : KVState → IProp GF,
      (⌜txn.txnReadonly t = true ∧ Q = fun _ => iprop(True)⌝ ∨
        (⌜txn.txnReadonly t = true ∧ txn.txnSerializable t = false⌝ ∗ kvReadAu γr.kv Q) ∨
        (⌜txn.txnReadonly t = false ∧ txn.txnPlain t ∧ txnNoZeroEnd t⌝ ∗
          kvOpAu1 γw.kv (.txn t) Q)) ∗
      ∃ (c : w64) (F : mvcc.Log), committedAtLeast γr c ∗
      mvcc.idxCert E.γ.idx F ∗
      ∀ m : TxnRespM, txnReplied E γw γr c F t Q cid mid m -∗ Φ m)

end reply

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **What a successful `Put` of `o` tells the client** about the reply's message `m` (persistent;
see the file header): since 2026-10-14 (unit C2a) with the witness that the log after is applied
through an index of the committed log at the read names `γr` (`appliedWit`: a linearizable read
at that index reads a log extending it, `client_get_after_put`); unit W-M3: the caller's
certificate of the log after (`certOk`: the put's revision is reached in the clients' model). -/
def putReplyOk (E : apply.AEnv GF) (γr : ReadNames) (F : mvcc.Log) (o : OpFull) (cid mid : w64)
    (m : PutRespM) : IProp GF :=
  iprop(∃ (hm : apply.HeaderModel) (x x' : apply.ApplyKV) (l : mvcc.Log) (skip : Bool),
    ⌜apply.applyStep (apply.withHeader (irrPut o) hm) true x x'
        (.dispatched (.applied l false) skip) ∧
      m.hdr.revision = W64 (x.log.length : Int) ∧ m.hdr.clusterId = cid ∧ m.hdr.memberId = mid ∧
      m.prev = (if o.base.prevKV then mvcc.findKey o.key (mvcc.stateAfter x.log) else none) ∧
      F <+: x.log ∧ 2 ≤ x.log.length ∧ x.log.length + 4 ≤ 2 ^ 63⌝ ∗
    mvcc.idxCert E.γ.idx x'.log ∗ appliedWit γr x'.log ∗ mvcc.certOk E.γ x'.log)

instance putReplyOk_persistent (E : apply.AEnv GF) (γr : ReadNames) (F : mvcc.Log) (o : OpFull)
    (cid mid : w64) (m : PutRespM) : Persistent (putReplyOk E γr F o cid mid m) := by
  unfold putReplyOk; infer_instance

/-- **What a successful `Get` of `o` tells the client** about the reply's message `m`
(persistent; see the file header); 2026-10-14 (unit T1): a linearizable get's result `□ Q` at the
log read (its update, deposited with the read index, fired there; 2026-10-15, unit T2: at the
whole state of the log read, `kvStateOf`); the log read extends the caller's floor `F` (the
vertical slice's unit V2); unit W-M3: the caller's certificate of the log read (`certOk`). -/
def rangeReplyOk (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (F : mvcc.Log) (o : OpFull)
    (cid mid : w64) (Q : KVState → IProp GF) (m : RangeRespM) : IProp GF :=
  iprop(∃ log : mvcc.Log, mvcc.idxCert E.γ.idx log ∗ mvcc.certOk E.γ log ∗
    ⌜2 ≤ log.length ∧ log.length + 3 ≤ 2 ^ 63 ∧
      m.hdr.revision = W64 ((log.length : Int) - 1) ∧ m.hdr.clusterId = cid ∧
      m.hdr.memberId = mid ∧ sint.Z o.base.rev ≤ sint.Z m.hdr.revision ∧
      m.count = txn.srvCount o
        (mvcc.stateAt log (sint.nat (mvcc.rangeRev m.hdr.revision o.base.rev))) true ∧
      txn.srvRangeOk o (mvcc.stateAt log (sint.nat (mvcc.rangeRev m.hdr.revision o.base.rev)))
        m.kvs m.more ∧ F <+: log⌝ ∗
    (if o.base.serializable then iprop(True) else readLogOk γr c log) ∗
    (if o.base.serializable then iprop(True) else □ Q (kvStateOf log)))

instance rangeReplyOk_persistent (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (F : mvcc.Log)
    (o : OpFull) (cid mid : w64) (Q : KVState → IProp GF) (m : RangeRespM) :
    Persistent (rangeReplyOk E γr c F o cid mid Q m) := by
  unfold rangeReplyOk; split <;> infer_instance

/-- **What a successful `Put` of `o` delivers to the client** with the reply's message `m`
(the merge of the generic gRPC specification with the slice's unit V1, 2026-10-14): `putReplyOk`'s
knowledge (with its witness at the read names `γr`, unit C2a) and the token of the revision the
put made (`revMinted`, exclusive: a reply's `Φ` is delivered once, so the generic spec carries
it); unit W-M3: `□ Q` of the state of the log the put met (the put's
update fired there: the state it linearized at). -/
def putReplied (E : apply.AEnv GF) (γr : ReadNames) (F : mvcc.Log) (o : OpFull)
    (Q : KVState → IProp GF) (cid mid : w64) (m : PutRespM) : IProp GF :=
  iprop(∃ (hm : apply.HeaderModel) (x x' : apply.ApplyKV) (l : mvcc.Log) (skip : Bool),
    ⌜apply.applyStep (apply.withHeader (irrPut o) hm) true x x'
        (.dispatched (.applied l false) skip) ∧
      m.hdr.revision = W64 (x.log.length : Int) ∧ m.hdr.clusterId = cid ∧ m.hdr.memberId = mid ∧
      m.prev = (if o.base.prevKV then mvcc.findKey o.key (mvcc.stateAfter x.log) else none) ∧
      F <+: x.log ∧ 2 ≤ x.log.length ∧ x.log.length + 4 ≤ 2 ^ 63⌝ ∗
    mvcc.idxCert E.γ.idx x'.log ∗ revMinted E x.log x'.log ∗ appliedWit γr x'.log ∗
    mvcc.certOk E.γ x'.log ∗ Q (kvStateOf x.log))

open Iris.ProofMode in
/-- A delivered put's result, weakened (2026-10-19, D21 M6). -/
theorem putReplied_mono (E : apply.AEnv GF) (γr : ReadNames) (F : mvcc.Log) (o : OpFull)
    (Q Q' : KVState → IProp GF) (cid mid : w64) (m : PutRespM) (h : ∀ σ, Q σ ⊢ Q' σ) :
    putReplied E γr F o Q cid mid m ⊢ putReplied E γr F o Q' cid mid m := by
  iintro H
  unfold putReplied
  icases H with ⟨%hm, %x, %x', %l, %skip, %Hp, #Hc, Htok, #Hw, #Hok, HQ⟩
  iexists hm, x, x', l, skip
  iframe Hc Htok Hw Hok
  isplitr
  · ipureintro; exact Hp
  iapply h $$ HQ

/-- **etcd's spec of the KV service's `Put`** (a predicate transformer; see the file header): a
caller asking the put `o` gets a reply message `m` with `putReplied` (`putReplyOk`, with its
witness at the read names `γr` (2026-10-14, unit C2a), and the revision's token), at a log
extending the caller's floor `F` (the vertical slice's unit V2); since 2026-10-15 (unit T2) a put
with no lease (any other flags) with the caller's persistent update over the whole state
`kvOpAu (.put o) Q`, whose `□ Q` of the state it linearized at the reply carries. -/
def etcdPutSpec (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64) :
    GrpcSpec (GF := GF) pbPutRequest pbPutResponse :=
  fun (o : OpFull) (Φ : PutRespM → IProp GF) =>
    iprop(∃ F : mvcc.Log, mvcc.idxCert E.γ.idx F ∗
      ∃ Q : KVState → IProp GF, ⌜o.leaseID = W64 0⌝ ∗ kvOpAu1 γr.kv (.put o) Q ∗
          ∀ m : PutRespM, putReplied E γr F o Q cid mid m -∗ Φ m)

/-- **etcd's spec of the KV service's `Range`**: a caller that knows the committed index `c`
(`committedAtLeast γr c`; `0` is free) asking the range `o` gets a reply message `m` with
`rangeReplyOk` at `c`; since 2026-10-14 (unit T1) with the caller's persistent read update
(`kvReadAu`, over the whole state since 2026-10-15, unit T2: a linearizable range), or none (`Q`
trivial). -/
def etcdRangeSpec (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64) :
    GrpcSpec (GF := GF) pbRangeRequest pbRangeResponse :=
  fun (o : OpFull) (Φ : RangeRespM → IProp GF) =>
    iprop(∃ (c : w64) (F : mvcc.Log) (Q : KVState → IProp GF), committedAtLeast γr c ∗
      mvcc.idxCert E.γ.idx F ∗
      (⌜Q = fun _ => iprop(True)⌝ ∨ (⌜o.base.serializable = false⌝ ∗ kvReadAu γr.kv Q)) ∗
      ∀ m : RangeRespM, rangeReplyOk E γr c F o cid mid Q m -∗ Φ m)

/-- **What a successful `DeleteRange` of `o` tells the client** about the reply's message `m`
(persistent): the apply thread's application of the delete `op'` the proposed data decode to
(`o` itself unless a range end is empty, `deleteRange_end_to_end`'s `deleteAppliedOk`), at the log
the entry met, the reply's header revision the delete's write revision, its ids the cluster's and
member's, `Deleted` the number of keys in the range, `PrevKvs` their key-values if asked;
mvcc's certificate of the log after. -/
def deleteReplyOk (E : apply.AEnv GF) (γr : ReadNames) (F : mvcc.Log) (o : OpFull) (cid mid : w64)
    (m : DelRespM) : IProp GF :=
  iprop(∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel) (op' : OpFull) (x x' : apply.ApplyKV)
      (l : mvcc.Log) (skip : Bool),
    ⌜irrWireOf (apply.withHeader (irrDeleteRange o) hm) rq' ∧ rq'.deleteRange = some op' ∧
      (irrNoZeroEnd (irrDeleteRange o) → op' = o) ∧
      apply.applyStep rq' true x x' (.dispatched (.applied l false) skip) ∧
      m.hdr.revision =
        W64 ((mvcc.writeRev x.log (txn.delChanges (mvcc.stateAfter x.log) op') : Nat) : Int) ∧
      m.hdr.clusterId = cid ∧ m.hdr.memberId = mid ∧
      m.deleted = W64 ((rangeIn (mvcc.stateAfter x.log) op').length : Int) ∧
      m.prevs = (if op'.base.prevKV then rangeIn (mvcc.stateAfter x.log) op' else []) ∧
      F <+: x.log ∧ 2 ≤ x.log.length ∧ x.log.length + 4 ≤ 2 ^ 63⌝ ∗
    mvcc.idxCert E.γ.idx x'.log ∗ appliedWit γr x'.log ∗ mvcc.certOk E.γ x'.log)

instance deleteReplyOk_persistent (E : apply.AEnv GF) (γr : ReadNames) (F : mvcc.Log) (o : OpFull)
    (cid mid : w64) (m : DelRespM) : Persistent (deleteReplyOk E γr F o cid mid m) := by
  unfold deleteReplyOk; infer_instance

/-- **What a successful `DeleteRange` of `o` delivers to the client** (as `putReplied`):
`deleteReplyOk`'s knowledge and the revision's token (`revMinted`; none minted if nothing was
deleted). -/
def deleteReplied (E : apply.AEnv GF) (γr : ReadNames) (F : mvcc.Log) (o : OpFull)
    (Q : KVState → IProp GF) (cid mid : w64) (m : DelRespM) : IProp GF :=
  iprop(∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel) (op' : OpFull) (x x' : apply.ApplyKV)
      (l : mvcc.Log) (skip : Bool),
    ⌜irrWireOf (apply.withHeader (irrDeleteRange o) hm) rq' ∧ rq'.deleteRange = some op' ∧
      (irrNoZeroEnd (irrDeleteRange o) → op' = o) ∧
      apply.applyStep rq' true x x' (.dispatched (.applied l false) skip) ∧
      m.hdr.revision =
        W64 ((mvcc.writeRev x.log (txn.delChanges (mvcc.stateAfter x.log) op') : Nat) : Int) ∧
      m.hdr.clusterId = cid ∧ m.hdr.memberId = mid ∧
      m.deleted = W64 ((rangeIn (mvcc.stateAfter x.log) op').length : Int) ∧
      m.prevs = (if op'.base.prevKV then rangeIn (mvcc.stateAfter x.log) op' else []) ∧
      F <+: x.log ∧ 2 ≤ x.log.length ∧ x.log.length + 4 ≤ 2 ^ 63⌝ ∗
    mvcc.idxCert E.γ.idx x'.log ∗ revMinted E x.log x'.log ∗ appliedWit γr x'.log ∗
    mvcc.certOk E.γ x'.log ∗ Q (kvStateOf x.log))

open Iris.ProofMode in
/-- A delivered delete's result, weakened (2026-10-20, linkv-txn stage A). -/
theorem deleteReplied_mono (E : apply.AEnv GF) (γr : ReadNames) (F : mvcc.Log) (o : OpFull)
    (Q Q' : KVState → IProp GF) (cid mid : w64) (m : DelRespM) (h : ∀ σ, Q σ ⊢ Q' σ) :
    deleteReplied E γr F o Q cid mid m ⊢ deleteReplied E γr F o Q' cid mid m := by
  iintro H
  unfold deleteReplied
  icases H with ⟨%hm, %rq', %op', %x, %x', %l, %skip, %Hp, #Hc, Htok, #Hw, #Hok, HQ⟩
  iexists hm, rq', op', x, x', l, skip
  iframe Hc Htok Hw Hok
  isplitr
  · ipureintro; exact Hp
  iapply h $$ HQ

/-- **etcd's spec of the KV service's `DeleteRange`**: a caller asking the delete `o` gets a
reply message `m` with `deleteReplied` (`deleteReplyOk` and the revision's token); since
2026-10-15 (unit T2) a delete whose range end is not `[0]` (the wire keeps it), with the caller's
update over the whole state, fired at most once since 2026-10-20 (linkv-txn stage A, as `Put`
since D21 M6) `kvOpAu1 (.deleteRange o) Q`, whose `Q` of the state it linearized at the reply
carries. -/
def etcdDeleteSpec (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64) :
    GrpcSpec (GF := GF) pbDeleteRangeRequest pbDeleteRangeResponse :=
  fun (o : OpFull) (Φ : DelRespM → IProp GF) =>
    iprop(∃ F : mvcc.Log, mvcc.idxCert E.γ.idx F ∗
      ∃ Q : KVState → IProp GF, ⌜o.base.rangeEnd ≠ [W8 0]⌝ ∗ kvOpAu1 γr.kv (.deleteRange o) Q ∗
      ∀ m : DelRespM, deleteReplied E γr F o Q cid mid m -∗ Φ m)

end defs

/-! ## The members -/

/-- **A member as its client sees it**: its client address and what etcd's specs it registers
there are at (`etcd_kv_started`'s): its apply environment, read names, cluster and member ids. -/
structure SrvAt (GF : BundledGFunctors) [FfiSyntax] where
  addr : GoString
  E : apply.AEnv GF
  γr : ReadNames
  cid : w64
  mid : w64

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The conjunction of the members' specs** (see the section header). -/
def anySpec {Req Rep : ProtoMsg GF} {α : Type _} (ms : List α) (S : α → GrpcSpec Req Rep) :
    GrpcSpec Req Rep :=
  fun m Φ => iprop([∧list] x ∈ ms, S x m Φ)

/-- Each member registering its own spec registers, at every member's address, the conjunction. -/
theorem isGrpcRpcs_anySpec {Req Rep : ProtoMsg GF} {α : Type _} (ms : List α) (addr : α → GoString)
    (name : GoString) (S : α → GrpcSpec Req Rep) :
    ([∗list] x ∈ ms, isGrpcRpc (addr x) name (S x)) ⊢
      isGrpcRpcs (ms.map addr) name (anySpec ms S) := by
  refine .trans ?_ (isGrpcRpcs_of_all (ms.map addr) name (anySpec ms S))
  rw [BigSepL.bigSepL_map]
  refine BigSepL.bigSepL_mono fun {k x} hk => ?_
  have hx : x ∈ ms := List.mem_of_getElem? hk
  exact isGrpcRpc_mono (addr x) name (S x) (anySpec ms S) fun m Φ => by
    unfold anySpec; exact BigAndL.bigAndL_mem (Φ := fun y => S y m Φ) hx

/-- **Proving the conjunction**: each member's conjunct from its persistent facts `C x` and its
share `R x` of the caller's resources (`∧`: the same resources serve every conjunct). -/
theorem anySpec_intro {Req Rep : ProtoMsg GF} {α : Type _} (ms : List α) (S : α → GrpcSpec Req Rep)
    (m : Req.M) (Φ : Rep.M → IProp GF) (C R : α → IProp GF) [∀ x, Persistent (C x)]
    (h : ∀ x, x ∈ ms → C x ∗ R x ⊢ S x m Φ) :
    ([∗list] x ∈ ms, C x) ∗ ([∧list] x ∈ ms, R x) ⊢ anySpec ms S m Φ := by
  unfold anySpec
  refine BigAndL.bigAndL_intro fun k x hk => ?_
  have hx : x ∈ ms := List.mem_of_getElem? hk
  iintro ⟨#HC, HR⟩
  iapply (h x hx)
  isplitl []
  · iapply (BigSepL.bigSepL_mem (Φ := C) hx) $$ HC
  · iapply (BigAndL.bigAndL_mem (Φ := R) hx) $$ HR

/-- **A conjunct per member from shared resources** `R` and each member's persistent facts
`C x` (`∧`: `R` serves every conjunct). -/
theorem bigAndL_of_sep {α : Type _} (ms : List α) (R : IProp GF) (C Φ : α → IProp GF)
    [∀ x, Persistent (C x)] (h : ∀ x, x ∈ ms → R ∗ C x ⊢ Φ x) :
    R ∗ ([∗list] x ∈ ms, C x) ⊢ [∧list] x ∈ ms, Φ x := by
  refine BigAndL.bigAndL_intro fun k x hk => ?_
  have hx : x ∈ ms := List.mem_of_getElem? hk
  iintro ⟨HR, #HC⟩
  iapply (h x hx)
  iframe HR
  iapply (BigSepL.bigSepL_mem (Φ := C) hx) $$ HC

/-- **One server at each of the addresses `addr`** (see the section header). -/
def srvsAt (addr : List GoString) (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64) :
    List (SrvAt GF) :=
  addr.map fun a => ⟨a, E, γr, cid, mid⟩

theorem srvsAt_addr (addr : List GoString) (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64) :
    (srvsAt addr E γr cid mid).map SrvAt.addr = addr := by
  unfold srvsAt
  induction addr with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons]; rw [ih]

theorem srvsAt_mem {addr : List GoString} {E : apply.AEnv GF} {γr : ReadNames} {cid mid : w64}
    {x : SrvAt GF} (h : x ∈ srvsAt addr E γr cid mid) : ∃ a ∈ addr, x = ⟨a, E, γr, cid, mid⟩ := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 h
  exact ⟨a, ha, rfl⟩

/-- A persistent fact of the server, at each of its members. -/
theorem srvsAt_sep (addr : List GoString) (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64)
    (P : IProp GF) (Φ : SrvAt GF → IProp GF)
    (h : ∀ a, a ∈ addr → P ⊢ Φ ⟨a, E, γr, cid, mid⟩) :
    □ P ⊢ [∗list] x ∈ srvsAt addr E γr cid mid, Φ x := by
  refine BigSepL.bigSepL_intro fun k x hk => ?_
  obtain ⟨a, ha, rfl⟩ := srvsAt_mem (List.mem_of_getElem? hk)
  exact intuitionistically_elim.trans (h a ha)

/-- A persistent update of the server, at each of its members, persistent. -/
theorem srvsAt_box (addr : List GoString) (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64)
    (P : IProp GF) (Φ : SrvAt GF → IProp GF) (h : ∀ a, a ∈ addr → P ⊢ Φ ⟨a, E, γr, cid, mid⟩) :
    □ P ⊢ □ [∧list] x ∈ srvsAt addr E γr cid mid, Φ x := by
  refine intuitionistically_mono (BigAndL.bigAndL_intro fun k x hk => ?_)
  obtain ⟨a, ha, rfl⟩ := srvsAt_mem (List.mem_of_getElem? hk)
  exact h a ha

/-- The registrations of one spec at a list of addresses, at each address. -/
theorem isGrpcRpcs_mem {Req Rep : ProtoMsg GF} :
    ∀ (addrs : List GoString) (name : GoString) (S : GrpcSpec Req Rep) (a : GoString),
      a ∈ addrs → isGrpcRpcs addrs name S ⊢ isGrpcRpc a name S
  | [], _, _, _, h => absurd h List.not_mem_nil
  | [b], name, S, a, h => by
    rw [List.mem_singleton.1 h]
  | b :: c :: rest, name, S, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · unfold isGrpcRpcs; iintro ⟨H, -⟩; iexact H
    · unfold isGrpcRpcs
      iintro ⟨-, H⟩
      iapply (isGrpcRpcs_mem (c :: rest) name S a h) $$ H

/-- The server's registration at its addresses, each member's. -/
theorem srvsAt_rpcs {Req Rep : ProtoMsg GF} (addr : List GoString) (E : apply.AEnv GF)
    (γr : ReadNames) (cid mid : w64) (name : GoString) (S : SrvAt GF → GrpcSpec Req Rep)
    (S0 : GrpcSpec Req Rep) (hS : ∀ a, S ⟨a, E, γr, cid, mid⟩ = S0) :
    □ isGrpcRpcs addr name S0 ⊢
      [∗list] x ∈ srvsAt addr E γr cid mid, isGrpcRpc x.addr name (S x) :=
  srvsAt_sep addr E γr cid mid _ (fun x => isGrpcRpc x.addr name (S x)) fun a ha => by
    rw [hS a]; exact isGrpcRpcs_mem addr name S0 a ha

end defs

section members
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **A write through the `*kv` `api` sent at most once** (persistent; D29): a client of
refusal-free members (any retry bound). -/
def writeOnce (api : Loc) (addrs : List GoString) : IProp GF :=
  iprop(⌜∀ a ∈ addrs, noRefusalAt a⌝)

instance writeOnce_persistent (api : Loc) (addrs : List GoString) :
    Persistent (writeOnce (GF := GF) api addrs) := by
  unfold writeOnce; infer_instance

/-- **`New`'s client `cl` sends a write at most once** (persistent; D29): a client of refusal-free
members (any retry bound). -/
def clientWriteOnce (cl : Loc) (addrs : List GoString) : IProp GF :=
  iprop(⌜∀ a ∈ addrs, noRefusalAt a⌝)

instance clientWriteOnce_persistent (cl : Loc) (addrs : List GoString) :
    Persistent (clientWriteOnce (GF := GF) cl addrs) := by
  unfold clientWriteOnce; infer_instance

/-- **A transaction through the `*txn` `tp` sent at most once** (D29): refusal-free members. -/
def txnWriteOnce (tp : Loc) (addrs : List GoString) : IProp GF :=
  iprop(⌜∀ a ∈ addrs, noRefusalAt a⌝)

/-- **etcd's KV registrations at a member** (persistent): etcd's `Put`, `Range`, `DeleteRange` and
`Txn` at its address, at its apply environment, read names and ids (`etcd_kv_started`'s). -/
def kvRegsAt (x : SrvAt GF) : IProp GF :=
  iprop(isGrpcRpc x.addr go!"/etcdserverpb.KV/Put" (etcdPutSpec x.E x.γr x.cid x.mid) ∗
    isGrpcRpc x.addr go!"/etcdserverpb.KV/Range" (etcdRangeSpec x.E x.γr x.cid x.mid) ∗
    isGrpcRpc x.addr go!"/etcdserverpb.KV/DeleteRange"
      (etcdDeleteSpec x.E x.γr x.cid x.mid) ∗
    isGrpcRpc x.addr go!"/etcdserverpb.KV/Txn" (etcdTxnSpec x.E x.γr x.γr x.cid x.mid))

instance kvRegsAt_persistent (x : SrvAt GF) : Persistent (kvRegsAt x) := by
  unfold kvRegsAt; infer_instance

/-! ## A `*kv` of the members: the client's side of etcd's KV service (D44, 2026-10-25)

**`isKV api ms`** (persistent) is what the client's KV calls take: its `*kv` over a connection to
the members' endpoints (`kvObjAt`) and, at each member, etcd's four KV specs registered at its
address (`kvRegsAt`: `etcd_kv_started`'s). The specs of `kv.Put`, `kv.Get`, `kv.Delete`, `kv.Do`
(and `txn.Commit`, with `kvRegs`) are stated with etcd's specs, not with a spec the caller picks:
a call through a client of `ms` passes the conjunction of the members' specs (`kvPutSpec`, ...:
`anySpec`), whose conjuncts the caller proves from its side in the members' terms (`floorsAt`,
`knownAt`, `putUpd`, `rangeUpd`, `delUpd`, `txnUpd`; `putSpec_of`, ...), and the reply is some
member's (`putAns`, `rangeAns`, `delAns`, `txnAns`). The server proves the same four specs
(`etcd_kv_served`). -/

/-- **etcd's KV registrations at the members `ms`** (persistent). -/
def kvRegs (ms : List (SrvAt GF)) : IProp GF :=
  iprop([∗list] x ∈ ms, kvRegsAt x)

instance kvRegs_persistent (ms : List (SrvAt GF)) : Persistent (kvRegs ms) := by
  unfold kvRegs; infer_instance

/-- **A `*kv` of the members `ms`** (persistent; see the section header). -/
def isKV (api : Loc) (ms : List (SrvAt GF)) : IProp GF :=
  iprop(kvObjAt api (ms.map SrvAt.addr) ∗ kvRegs ms)

instance isKV_persistent (api : Loc) (ms : List (SrvAt GF)) : Persistent (isKV api ms) := by
  unfold isKV; infer_instance

/-- The registrations of `Put` at the members. -/
theorem kvRegs_put (ms : List (SrvAt GF)) :
    ([∗list] x ∈ ms, kvRegsAt x) ⊢ [∗list] x ∈ ms,
      isGrpcRpc x.addr go!"/etcdserverpb.KV/Put" (etcdPutSpec x.E x.γr x.cid x.mid) :=
  BigSepL.bigSepL_mono fun _ => by
    iintro #H; iunfold kvRegsAt at H; icases H with ⟨#H1, -, -, -⟩; iexact H1

/-- The registrations of `Range` at the members. -/
theorem kvRegs_range (ms : List (SrvAt GF)) :
    ([∗list] x ∈ ms, kvRegsAt x) ⊢ [∗list] x ∈ ms,
      isGrpcRpc x.addr go!"/etcdserverpb.KV/Range" (etcdRangeSpec x.E x.γr x.cid x.mid) :=
  BigSepL.bigSepL_mono fun _ => by
    iintro #H; iunfold kvRegsAt at H; icases H with ⟨-, #H1, -, -⟩; iexact H1

/-- The registrations of `DeleteRange` at the members. -/
theorem kvRegs_del (ms : List (SrvAt GF)) :
    ([∗list] x ∈ ms, kvRegsAt x) ⊢ [∗list] x ∈ ms,
      isGrpcRpc x.addr go!"/etcdserverpb.KV/DeleteRange"
        (etcdDeleteSpec x.E x.γr x.cid x.mid) :=
  BigSepL.bigSepL_mono fun _ => by
    iintro #H; iunfold kvRegsAt at H; icases H with ⟨-, -, #H1, -⟩; iexact H1

/-- The registrations of `Txn` at the members. -/
theorem kvRegs_txn (ms : List (SrvAt GF)) :
    ([∗list] x ∈ ms, kvRegsAt x) ⊢ [∗list] x ∈ ms,
      isGrpcRpc x.addr go!"/etcdserverpb.KV/Txn" (etcdTxnSpec x.E x.γr x.γr x.cid x.mid) :=
  BigSepL.bigSepL_mono fun _ => by
    iintro #H; iunfold kvRegsAt at H; icases H with ⟨-, -, -, #H1⟩; iexact H1

/-- One member's registrations are its server's at its one address. -/
theorem kvRegs_one (a : GoString) (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64) :
    kvRegsAt (⟨a, E, γr, cid, mid⟩ : SrvAt GF) ⊢ kvRegs (srvsAt [a] E γr cid mid) := by
  unfold kvRegs srvsAt
  exact (BigSepL.bigSepL_singleton (PROP := IProp GF) (Φ := fun _ x => kvRegsAt x)).2

/-- **etcd's `Put` at a connection to the members `ms`**: the members' specs' conjunction. -/
def kvPutSpec (ms : List (SrvAt GF)) : GrpcSpec (GF := GF) pbPutRequest pbPutResponse :=
  anySpec ms fun x => etcdPutSpec x.E x.γr x.cid x.mid

/-- **etcd's `Range` at a connection to the members `ms`**. -/
def kvRangeSpec (ms : List (SrvAt GF)) : GrpcSpec (GF := GF) pbRangeRequest pbRangeResponse :=
  anySpec ms fun x => etcdRangeSpec x.E x.γr x.cid x.mid

/-- **etcd's `DeleteRange` at a connection to the members `ms`**. -/
def kvDeleteSpec (ms : List (SrvAt GF)) :
    GrpcSpec (GF := GF) pbDeleteRangeRequest pbDeleteRangeResponse :=
  anySpec ms fun x => etcdDeleteSpec x.E x.γr x.cid x.mid

/-- **etcd's `Txn` at a connection to the members `ms`**. -/
def kvTxnSpec (ms : List (SrvAt GF)) : GrpcSpec (GF := GF) pbTxnRequest pbTxnResponse :=
  anySpec ms fun x => etcdTxnSpec x.E x.γr x.γr x.cid x.mid

/-- The members' registrations of `Put` register the conjunction at their addresses. -/
theorem kvRegs_rpcPut (ms : List (SrvAt GF)) :
    kvRegs ms ⊢ isGrpcRpcs (ms.map SrvAt.addr) go!"/etcdserverpb.KV/Put" (kvPutSpec ms) :=
  (kvRegs_put ms).trans (isGrpcRpcs_anySpec ms SrvAt.addr _ _)

/-- The members' registrations of `Range` register the conjunction at their addresses. -/
theorem kvRegs_rpcRange (ms : List (SrvAt GF)) :
    kvRegs ms ⊢ isGrpcRpcs (ms.map SrvAt.addr) go!"/etcdserverpb.KV/Range" (kvRangeSpec ms) :=
  (kvRegs_range ms).trans (isGrpcRpcs_anySpec ms SrvAt.addr _ _)

/-- The members' registrations of `DeleteRange` register the conjunction at their addresses. -/
theorem kvRegs_rpcDelete (ms : List (SrvAt GF)) :
    kvRegs ms ⊢
      isGrpcRpcs (ms.map SrvAt.addr) go!"/etcdserverpb.KV/DeleteRange" (kvDeleteSpec ms) :=
  (kvRegs_del ms).trans (isGrpcRpcs_anySpec ms SrvAt.addr _ _)

/-- The members' registrations of `Txn` register the conjunction at their addresses. -/
theorem kvRegs_rpcTxn (ms : List (SrvAt GF)) :
    kvRegs ms ⊢ isGrpcRpcs (ms.map SrvAt.addr) go!"/etcdserverpb.KV/Txn" (kvTxnSpec ms) :=
  (kvRegs_txn ms).trans (isGrpcRpcs_anySpec ms SrvAt.addr _ _)

/-- **The caller's floor at the members** (persistent): each member's certificate of the log
`F` (`[]` is free, `idxCert_nil`). -/
def floorsAt (ms : List (SrvAt GF)) (F : mvcc.Log) : IProp GF :=
  iprop([∗list] x ∈ ms, mvcc.idxCert x.E.γ.idx F)

instance floorsAt_persistent (ms : List (SrvAt GF)) (F : mvcc.Log) :
    Persistent (floorsAt ms F) := by
  unfold floorsAt; infer_instance

/-- **What a reader knows of the members** (persistent): at each, the committed index at least
`c` (`0` is free) and the certificate of the floor `F`. -/
def knownAt (ms : List (SrvAt GF)) (c : w64) (F : mvcc.Log) : IProp GF :=
  iprop([∗list] x ∈ ms, committedAtLeast x.γr c ∗ mvcc.idxCert x.E.γ.idx F)

instance knownAt_persistent (ms : List (SrvAt GF)) (c : w64) (F : mvcc.Log) :
    Persistent (knownAt ms c F) := by
  unfold knownAt; infer_instance

/-- **A put's update at the members**: the caller's update of the put `o` over the whole state at
each member's names (`[∧ list]`: only the member the attempt reaches fires its own). -/
def putUpd (ms : List (SrvAt GF)) (o : OpFull) (Q : KVState → IProp GF) : IProp GF :=
  iprop([∧list] x ∈ ms, kvOpAu1 x.γr.kv (.put o) Q)

/-- **A delete's update at the members** (as `putUpd`). -/
def delUpd (ms : List (SrvAt GF)) (o : OpFull) (Q : KVState → IProp GF) : IProp GF :=
  iprop([∧list] x ∈ ms, kvOpAu1 x.γr.kv (.deleteRange o) Q)

/-- **A range's update at the members**: none (`Q` trivial) or, linearizable, a read update at
each member's names (persistent in a call's precondition: a read may be answered by any member,
and again). -/
def rangeUpd (ms : List (SrvAt GF)) (o : OpFull) (Q : KVState → IProp GF) : IProp GF :=
  iprop([∧list] x ∈ ms, ⌜Q = fun _ => iprop(True)⌝ ∨
    (⌜o.base.serializable = false⌝ ∗ kvReadAu x.γr.kv Q))

/-- **A transaction's update at a member**, at its write names `γw` and read names `γr`: none
(read-only), a read update (read-only, linearizable) or a write's update (writing). -/
def txnUpdAt (γw γr : ReadNames) (t : TxnModel) (Q : KVState → IProp GF) : IProp GF :=
  iprop(⌜txn.txnReadonly t = true ∧ Q = fun _ => iprop(True)⌝ ∨
    (⌜txn.txnReadonly t = true ∧ txn.txnSerializable t = false⌝ ∗ kvReadAu γr.kv Q) ∨
    (⌜txn.txnReadonly t = false ∧ txn.txnPlain t ∧ txnNoZeroEnd t⌝ ∗ kvOpAu1 γw.kv (.txn t) Q))

/-- **A transaction's update at the members** (`txnUpdAt` at each member's names). -/
def txnUpd (ms : List (SrvAt GF)) (t : TxnModel) (Q : KVState → IProp GF) : IProp GF :=
  iprop([∧list] x ∈ ms, txnUpdAt x.γr x.γr t Q)

/-- **A put's answer**: some member's `putReplied`. -/
def putAns (ms : List (SrvAt GF)) (F : mvcc.Log) (o : OpFull) (Q : KVState → IProp GF)
    (m : PutRespM) : IProp GF :=
  iprop(∃ x : SrvAt GF, ⌜x ∈ ms⌝ ∗ putReplied x.E x.γr F o Q x.cid x.mid m)

/-- **A range's answer**: some member's `rangeReplyOk`. -/
def rangeAns (ms : List (SrvAt GF)) (c : w64) (F : mvcc.Log) (o : OpFull)
    (Q : KVState → IProp GF) (m : RangeRespM) : IProp GF :=
  iprop(∃ x : SrvAt GF, ⌜x ∈ ms⌝ ∗ rangeReplyOk x.E x.γr c F o x.cid x.mid Q m)

instance rangeAns_persistent (ms : List (SrvAt GF)) (c : w64) (F : mvcc.Log) (o : OpFull)
    (Q : KVState → IProp GF) (m : RangeRespM) : Persistent (rangeAns ms c F o Q m) := by
  unfold rangeAns; infer_instance

/-- **A delete's answer**: some member's `deleteReplied`. -/
def delAns (ms : List (SrvAt GF)) (F : mvcc.Log) (o : OpFull) (Q : KVState → IProp GF)
    (m : DelRespM) : IProp GF :=
  iprop(∃ x : SrvAt GF, ⌜x ∈ ms⌝ ∗ deleteReplied x.E x.γr F o Q x.cid x.mid m)

/-- **A transaction's answer**: some member's `txnReplied`. -/
def txnAns (ms : List (SrvAt GF)) (c : w64) (F : mvcc.Log) (t : TxnModel)
    (Q : KVState → IProp GF) (m : TxnRespM) : IProp GF :=
  iprop(∃ x : SrvAt GF, ⌜x ∈ ms⌝ ∗ txnReplied x.E x.γr x.γr c F t Q x.cid x.mid m)

/-- **A put's request meets the members' spec**, with the answer `putAns`: a put with no lease,
from the floor and the update at the members. -/
theorem putSpec_of (ms : List (SrvAt GF)) (F : mvcc.Log) (o : OpFull) (Q : KVState → IProp GF)
    (hl : o.leaseID = W64 0) :
    floorsAt ms F ∗ putUpd ms o Q ⊢ kvPutSpec ms o (putAns ms F o Q) := by
  unfold floorsAt putUpd kvPutSpec
  exact anySpec_intro _ _ _ _ (fun x : SrvAt GF => mvcc.idxCert x.E.γ.idx F)
    (fun x : SrvAt GF => kvOpAu1 x.γr.kv (.put o) Q) (fun x hx => by
      iintro ⟨#HFx, Haux⟩
      unfold etcdPutSpec
      iexists F
      iframe HFx
      iexists Q
      isplitr
      · ipureintro; exact hl
      iframe Haux
      iintro %m Hm
      unfold putAns
      iexists x
      iframe Hm
      ipureintro; exact hx)

/-- **A range's request meets the members' spec**, with the answer `rangeAns`. -/
theorem rangeSpec_of (ms : List (SrvAt GF)) (c : w64) (F : mvcc.Log) (o : OpFull)
    (Q : KVState → IProp GF) :
    knownAt ms c F ∗ rangeUpd ms o Q ⊢ kvRangeSpec ms o (rangeAns ms c F o Q) := by
  unfold knownAt rangeUpd kvRangeSpec
  exact anySpec_intro _ _ _ _
    (fun x : SrvAt GF => iprop(committedAtLeast x.γr c ∗ mvcc.idxCert x.E.γ.idx F))
    (fun x : SrvAt GF => iprop(⌜Q = fun _ => iprop(True)⌝ ∨
      (⌜o.base.serializable = false⌝ ∗ kvReadAu x.γr.kv Q)))
    (fun x hx => by
      iintro ⟨⟨#Hcx, #HFx⟩, Hdqx⟩
      unfold etcdRangeSpec
      iexists c, F, Q
      iframe Hcx HFx Hdqx
      iintro %m Hm
      unfold rangeAns
      iexists x
      iframe Hm
      ipureintro; exact hx)

/-- **A delete's request meets the members' spec**, with the answer `delAns`: a delete whose
range end is not `[0]`. -/
theorem deleteSpec_of (ms : List (SrvAt GF)) (F : mvcc.Log) (o : OpFull) (Q : KVState → IProp GF)
    (hz : o.base.rangeEnd ≠ [W8 0]) :
    floorsAt ms F ∗ delUpd ms o Q ⊢ kvDeleteSpec ms o (delAns ms F o Q) := by
  unfold floorsAt delUpd kvDeleteSpec
  exact anySpec_intro _ _ _ _ (fun x : SrvAt GF => mvcc.idxCert x.E.γ.idx F)
    (fun x : SrvAt GF => kvOpAu1 x.γr.kv (.deleteRange o) Q) (fun x hx => by
      iintro ⟨#HFx, Haux⟩
      unfold etcdDeleteSpec
      iexists F
      iframe HFx
      iexists Q
      isplitr
      · ipureintro; exact hz
      iframe Haux
      iintro %m Hm
      unfold delAns
      iexists x
      iframe Hm
      ipureintro; exact hx)

/-- **A transaction's request meets the members' spec**, with the answer `txnAns`: a
transaction of plain operations within the txn package's model. -/
theorem txnSpec_of (ms : List (SrvAt GF)) (c : w64) (F : mvcc.Log) (t : TxnModel)
    (Q : KVState → IProp GF) (hp : TxnModel.plain t) (hin : txnModelIn t) :
    knownAt ms c F ∗ txnUpd ms t Q ⊢ kvTxnSpec ms t (txnAns ms c F t Q) := by
  unfold knownAt txnUpd kvTxnSpec
  exact anySpec_intro _ _ _ _
    (fun x : SrvAt GF => iprop(committedAtLeast x.γr c ∗ mvcc.idxCert x.E.γ.idx F))
    (fun x : SrvAt GF => txnUpdAt x.γr x.γr t Q)
    (fun x hx => by
      iintro ⟨⟨#Hcx, #HFx⟩, Hu⟩
      unfold etcdTxnSpec
      isplitl []
      · ipureintro; exact ⟨hp, hin⟩
      iexists Q
      iunfold txnUpdAt at Hu
      iframe Hu
      iexists c, F
      iframe Hcx HFx
      iintro %m Hm
      unfold txnAns
      iexists x
      iframe Hm
      ipureintro; exact hx)

/-! ### One server over its endpoints (`srvsAt`)

The single-server results' case (`client_*_end_to_end`, `ServerKV*.lean`): every address of `addr`
one member, at one environment, read names and ids. -/

theorem isKV_srvsAt (api : Loc) (addr : List GoString) (E : apply.AEnv GF) (γr : ReadNames)
    (cid mid : w64) :
    kvObjAt api addr ∗ kvRegs (srvsAt addr E γr cid mid) ⊢ isKV api (srvsAt addr E γr cid mid) := by
  unfold isKV; rw [srvsAt_addr]

theorem floorsAt_srvsAt (addr : List GoString) (E : apply.AEnv GF) (γr : ReadNames)
    (cid mid : w64) (F : mvcc.Log) :
    mvcc.idxCert E.γ.idx F ⊢ floorsAt (srvsAt addr E γr cid mid) F := by
  iintro #H
  unfold floorsAt
  iapply (srvsAt_sep addr E γr cid mid (mvcc.idxCert E.γ.idx F)
    (fun x : SrvAt GF => mvcc.idxCert x.E.γ.idx F) (fun _ _ => .rfl)) $$ H

theorem knownAt_srvsAt (addr : List GoString) (E : apply.AEnv GF) (γr : ReadNames)
    (c cid mid : w64) (F : mvcc.Log) :
    committedAtLeast γr c ∗ mvcc.idxCert E.γ.idx F ⊢ knownAt (srvsAt addr E γr cid mid) c F := by
  iintro #H
  unfold knownAt
  iapply (srvsAt_sep addr E γr cid mid iprop(committedAtLeast γr c ∗ mvcc.idxCert E.γ.idx F)
    (fun x : SrvAt GF => iprop(committedAtLeast x.γr c ∗ mvcc.idxCert x.E.γ.idx F))
    (fun _ _ => .rfl)) $$ H

theorem putUpd_srvsAt (addr : List GoString) (E : apply.AEnv GF) (γr : ReadNames)
    (cid mid : w64) (o : OpFull) (Q : KVState → IProp GF) :
    □ kvOpAu1 γr.kv (.put o) Q ⊢ □ putUpd (srvsAt addr E γr cid mid) o Q := by
  unfold putUpd
  exact srvsAt_box addr E γr cid mid _ (fun x : SrvAt GF => kvOpAu1 x.γr.kv (.put o) Q)
    (fun _ _ => .rfl)

theorem delUpd_srvsAt (addr : List GoString) (E : apply.AEnv GF) (γr : ReadNames)
    (cid mid : w64) (o : OpFull) (Q : KVState → IProp GF) :
    □ kvOpAu1 γr.kv (.deleteRange o) Q ⊢ □ delUpd (srvsAt addr E γr cid mid) o Q := by
  unfold delUpd
  exact srvsAt_box addr E γr cid mid _ (fun x : SrvAt GF => kvOpAu1 x.γr.kv (.deleteRange o) Q)
    (fun _ _ => .rfl)

theorem rangeUpd_srvsAt (addr : List GoString) (E : apply.AEnv GF) (γr : ReadNames)
    (cid mid : w64) (o : OpFull) (Q : KVState → IProp GF) :
    □ (⌜Q = fun _ => iprop(True)⌝ ∨ (⌜o.base.serializable = false⌝ ∗ kvReadAu γr.kv Q)) ⊢
      □ rangeUpd (srvsAt addr E γr cid mid) o Q := by
  unfold rangeUpd
  exact srvsAt_box addr E γr cid mid _ (fun x : SrvAt GF => iprop(⌜Q = fun _ => iprop(True)⌝ ∨
    (⌜o.base.serializable = false⌝ ∗ kvReadAu x.γr.kv Q))) (fun _ _ => .rfl)

theorem txnUpd_srvsAt (addr : List GoString) (E : apply.AEnv GF) (γr : ReadNames)
    (cid mid : w64) (t : TxnModel) (Q : KVState → IProp GF) :
    □ txnUpdAt γr γr t Q ⊢ □ txnUpd (srvsAt addr E γr cid mid) t Q := by
  unfold txnUpd
  exact srvsAt_box addr E γr cid mid _ (fun x : SrvAt GF => txnUpdAt x.γr x.γr t Q)
    (fun _ _ => .rfl)

theorem putAns_srvsAt (addr : List GoString) (E : apply.AEnv GF) (γr : ReadNames)
    (cid mid : w64) (F : mvcc.Log) (o : OpFull) (Q : KVState → IProp GF) (m : PutRespM) :
    putAns (srvsAt addr E γr cid mid) F o Q m ⊢ putReplied E γr F o Q cid mid m := by
  unfold putAns
  iintro ⟨%x, %hx, H⟩
  obtain ⟨a, -, rfl⟩ := srvsAt_mem hx
  iexact H

theorem rangeAns_srvsAt (addr : List GoString) (E : apply.AEnv GF) (γr : ReadNames)
    (c cid mid : w64) (F : mvcc.Log) (o : OpFull) (Q : KVState → IProp GF) (m : RangeRespM) :
    rangeAns (srvsAt addr E γr cid mid) c F o Q m ⊢ rangeReplyOk E γr c F o cid mid Q m := by
  unfold rangeAns
  iintro ⟨%x, %hx, H⟩
  obtain ⟨a, -, rfl⟩ := srvsAt_mem hx
  iexact H

theorem delAns_srvsAt (addr : List GoString) (E : apply.AEnv GF) (γr : ReadNames)
    (cid mid : w64) (F : mvcc.Log) (o : OpFull) (Q : KVState → IProp GF) (m : DelRespM) :
    delAns (srvsAt addr E γr cid mid) F o Q m ⊢ deleteReplied E γr F o Q cid mid m := by
  unfold delAns
  iintro ⟨%x, %hx, H⟩
  obtain ⟨a, -, rfl⟩ := srvsAt_mem hx
  iexact H

theorem txnAns_srvsAt (addr : List GoString) (E : apply.AEnv GF) (γr : ReadNames)
    (c cid mid : w64) (F : mvcc.Log) (t : TxnModel) (Q : KVState → IProp GF) (m : TxnRespM) :
    txnAns (srvsAt addr E γr cid mid) c F t Q m ⊢ txnReplied E γr γr c F t Q cid mid m := by
  unfold txnAns
  iintro ⟨%x, %hx, H⟩
  obtain ⟨a, -, rfl⟩ := srvsAt_mem hx
  iexact H

/-- A `*kv`'s precondition, strengthened by persistent facts `C`. -/
theorem kvReqPre_wand (api : Loc) (addr : List GoString) (C P P' : IProp GF) [Persistent C]
    (h : C ∗ P ⊢ P') : C ∗ kvReqPre api addr P ⊢ kvReqPre api addr P' := by
  iintro ⟨#HC, HP⟩
  unfold kvReqPre
  icases HP with (#HP | ⟨%Hnr, HP⟩)
  · ileft
    imodintro
    inext
    iapply h
    iframe HC HP
  · iright
    isplitl []
    · ipureintro; exact Hnr
    inext
    iapply h
    iframe HC HP

/-- A `*txn`'s precondition, strengthened by persistent facts `C`. -/
theorem txnReqPre_wand (tp : Loc) (addr : List GoString) (C P P' : IProp GF) [Persistent C]
    (h : C ∗ P ⊢ P') : C ∗ txnReqPre tp addr P ⊢ txnReqPre tp addr P' := by
  iintro ⟨#HC, HP⟩
  unfold txnReqPre
  icases HP with (#HP | ⟨%Hnr, HP⟩)
  · ileft
    imodintro
    inext
    iapply h
    iframe HC HP
  · iright
    isplitl []
    · ipureintro; exact Hnr
    inext
    iapply h
    iframe HC HP

end members

/-! ## A write's log after it (D48)

The apply thread's log after a member applied a put, a delete or a writing transaction: the
log it met with the write's changes committed (as `ServerKVPut.lean`'s `put_applied_exact`,
..., without the server's assumptions). The state after the write (`kvOpStep`) is the state of
that log, so a write's reply gives that it is a well-formed small log's, too. -/

section applied
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]

/-- An applied outcome without the quota's `ErrNoSpace` passes through every layer of a chain:
it is the backend's (`v3rpc.chainStep_applied_false`). -/
theorem kvs_chainStep_applied_false : ∀ (c : apply.Chain) {rq : apply.IRRModel} {log l : mvcc.Log},
    apply.chainStep apply.backendStep c rq log (.applied l false) →
      apply.backendStep rq log (.applied l false)
  | .backend, _, _, _, h => h
  | .corrupt c, _, _, _, h => by
    simp only [apply.chainStep] at h
    split at h
    · cases h
    · exact kvs_chainStep_applied_false c h
  | .capped c, _, _, _, h => by
    simp only [apply.chainStep] at h
    split at h
    · cases h
    · split at h
      · rcases h with h | h
        · cases h
        · exact kvs_chainStep_applied_false c h
      · exact kvs_chainStep_applied_false c h
  | .auth _ c, _, _, _, h => by
    simp only [apply.chainStep] at h
    split at h
    · rcases h with ⟨-, h⟩ | h
      · cases h
      · exact kvs_chainStep_applied_false c h
    · exact kvs_chainStep_applied_false c h
  | .quota c, _, _, _, h => by
    simp only [apply.chainStep] at h
    exact kvs_chainStep_applied_false c h

/-- **A put's log**: the put's change at the log's next revision. -/
theorem kvs_put_applied_log (o : OpFull) (hm : apply.HeaderModel) (x x' : apply.ApplyKV)
    (l : mvcc.Log) (skip : Bool)
    (h : apply.applyStep (apply.withHeader (irrPut o) hm) true x x'
      (.dispatched (.applied l false) skip)) :
    x'.log = x.log ++ [[txn.putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter x.log))]] := by
  have hk : apply.dispatchKind (apply.withHeader (irrPut o) hm) = .put := by
    simp [apply.dispatchKind, apply.withHeader, irrPut, apply.irrEmpty]
  obtain ⟨-, hd, hl, -⟩ := h
  rw [hl]
  unfold apply.dispatchStep at hd
  rw [hk] at hd
  simp only [apply.preV3Kind, apply.storeKind, Bool.false_eq_true, ↓reduceIte,
    false_or] at hd
  have hb := kvs_chainStep_applied_false x.chain hd
  unfold apply.backendStep at hb
  rw [hk] at hb
  obtain ⟨op, hop, hb | hb | hb⟩ := hb
  · cases hb.2
  · cases hb.2.2
  · simp [apply.withHeader, irrPut, apply.irrEmpty] at hop
    subst hop
    cases hb.2
    rfl

/-- **A delete's log**: the delete `op'` of the decoded request committed. -/
theorem kvs_delete_applied_log (op op' : OpFull) (hm : apply.HeaderModel) (rq' : apply.IRRModel)
    (x x' : apply.ApplyKV) (l : mvcc.Log) (skip : Bool)
    (hw : irrWireOf (apply.withHeader (irrDeleteRange op) hm) rq')
    (hop : rq'.deleteRange = some op')
    (h : apply.applyStep rq' true x x' (.dispatched (.applied l false) skip)) :
    x'.log = mvcc.commitLog x.log (txn.delChanges (mvcc.stateAfter x.log) op') := by
  have hk : apply.dispatchKind rq' = .deleteRange := by
    rw [hw.2.2.1]
    simp [apply.dispatchKind, apply.withHeader, irrDeleteRange, apply.irrEmpty]
  obtain ⟨-, hd, hl, -⟩ := h
  rw [hl]
  unfold apply.dispatchStep at hd
  rw [hk] at hd
  simp only [apply.preV3Kind, apply.storeKind, Bool.false_eq_true, ↓reduceIte,
    false_or] at hd
  have hb := kvs_chainStep_applied_false x.chain hd
  unfold apply.backendStep at hb
  rw [hk] at hb
  obtain ⟨op'', hop', hb⟩ := hb
  rw [hop] at hop'
  cases hop'
  cases hb
  rfl

/-- **A transaction's log**: its run's changes committed. -/
theorem kvs_txn_applied_log (t t' : TxnModel) (hm : apply.HeaderModel) (rq' : apply.IRRModel)
    (x x' : apply.ApplyKV) (l : mvcc.Log) (skip : Bool)
    (hw : irrWireOf (apply.withHeader (irrTxn t) hm) rq') (ht : rq'.txn = some t')
    (h : apply.applyStep rq' true x x' (.dispatched (.applied l false) skip)) :
    x'.log = mvcc.commitLog x.log
      (txn.srvRunTxn (W64 (x.log.length : Int)) (mvcc.stateAfter x.log) t').2.1 := by
  have hk : apply.dispatchKind rq' = .txn := by
    rw [hw.2.2.1]
    simp [apply.dispatchKind, apply.withHeader, irrTxn, apply.irrEmpty]
  obtain ⟨-, hd, hl, -⟩ := h
  rw [hl]
  unfold apply.dispatchStep at hd
  rw [hk] at hd
  simp only [apply.preV3Kind, apply.storeKind, Bool.false_eq_true, ↓reduceIte,
    false_or] at hd
  have hb := kvs_chainStep_applied_false x.chain hd
  unfold apply.backendStep at hb
  rw [hk] at hb
  obtain ⟨t'', ht'', ⟨hb, -⟩ | ⟨hb, -⟩⟩ := hb
  · cases hb
  · rw [ht] at ht''
    cases ht''
    cases hb
    rfl

/-- **The state after a write is its log's**: the log after `l` with the changes `cs`
committed, a certified log `C` extending it (`l` not empty). -/
theorem kvLogOk_commit {l C : mvcc.Log} (cs : List mvcc.Change) (hp : mvcc.commitLog l cs <+: C)
    (hne : l ≠ []) (hc : mvcc.LogWf' C ∧ C.length < 2 ^ 63 ∧ txn.LogSmall C) :
    kvLogOk ((kvStateOf l).commit cs) := by
  rw [← kvStateOf_commitLog l cs hne]
  refine kvLogOk_of_prefix hp hc.1 hc.2.2 hc.2.1 ?_
  unfold mvcc.commitLog; split
  · exact hne
  · simp

end applied

/-! ## The client's view: one KV, its members hidden (D44, 2026-10-25)

**`isKv api γ dup`** (persistent) is what the specs of the `*kv`'s calls take (`kv.Put`, `kv.Get`,
`kv.Delete`, `kv.Do`, and `txn.Commit` with the builder's `txnKvIs`): the `*kv` `api` is a client
of some members (`∃ ms`: hidden), each registering etcd's KV specs at its address (`kvRegsAt`),
all at the state of one KV: every member's state name is `γ`'s (`x.γr.kv.st = γ.st`: a cluster
booted together, `srvMemberBoot_alloc`), so a
single update at `γ` is each member's (`kvOpAu1_names`, `kvReadAu_names`). Unless `dup`, the
members never refuse a request (`noRefusalAt`, D29): a write is delivered at most once, so its
atomic update may be fired at most once; if `dup` (the client's retry interceptor may resend it),
it must be persistent: the specs take a write's atomic update under `□?dup`.

The specs take the caller's update at `γ` and give the reply's fields as functions of the state
`σ` the update fired at (`putStOk`, `rangeStOk`, `delStOk`, `txnStOk`), and (D48) that `σ` is a
well-formed small log's (`kvLogOk`: the store's receipts bound its changes, `isKv`'s
`receiptBound GF ≤ 2 ^ 62`, `idxCert_logOk`). Their proofs go through the
members' (`KVMembers.lean`: etcd's specs at each member, a reply some member's), at the floor `[]`
and the committed index `0` (`isKv`'s `srvStart`); what a member's reply says of its
server (certificates, the revision's token, the applied index's witness) is the members' lemmas',
which the results about the server's own model use (`ServerKV*.lean`). -/

section abstract
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **What a call starts from at a member** (persistent): its committed index at least `0` and the
floor `[]` (both free, `srvStart_alloc`). -/
def srvStart (x : SrvAt GF) : IProp GF :=
  iprop(committedAtLeast x.γr (W64 0) ∗ mvcc.idxCert x.E.γ.idx [])

instance srvStart_persistent (x : SrvAt GF) : Persistent (srvStart x) := by
  unfold srvStart; infer_instance

/-- The members' floors. -/
theorem srvStart_idx (ms : List (SrvAt GF)) :
    ([∗list] x ∈ ms, srvStart x) ⊢ [∗list] x ∈ ms, mvcc.idxCert x.E.γ.idx [] :=
  BigSepL.bigSepL_mono fun _ => by
    iintro #H; iunfold srvStart at H; icases H with ⟨-, #H1⟩; iexact H1

/-- The members' committed indices and floors. -/
theorem srvStart_both (ms : List (SrvAt GF)) :
    ([∗list] x ∈ ms, srvStart x) ⊢
      [∗list] x ∈ ms, committedAtLeast x.γr (W64 0) ∗ mvcc.idxCert x.E.γ.idx [] :=
  BigSepL.bigSepL_mono fun _ => by
    iintro #H; iunfold srvStart at H; iexact H

/-- A log's state's next revision is its length. -/
theorem kvStateOf_rev_succ (l : mvcc.Log) (h : 2 ≤ l.length) :
    (kvStateOf l).rev + 1 = l.length := by
  rw [kvStateOf_rev]; omega

/-- **A write's revision is its state's after the changes** (`writeRev`, `KVState.commit`). -/
theorem kvStateOf_commit_rev (l : mvcc.Log) (cs : List mvcc.Change) (h : 2 ≤ l.length) :
    ((kvStateOf l).commit cs).rev = mvcc.writeRev l cs := by
  unfold mvcc.writeRev
  by_cases hc : cs = []
  · simp only [hc, KVState.commit_nil, ↓reduceIte, kvStateOf_rev]
  · rw [KVState.commit_rev _ _ hc, kvStateOf_rev]; simp only [hc, ↓reduceIte]; omega

/-- An update reads only the KV state's name. -/
theorem kvOpAu1_names (γk γk' : KVNames) (hst : γk.st = γk'.st)
    (op : KVOp) (Q : KVState → IProp GF) : kvOpAu1 (GF := GF) γk op Q = kvOpAu1 γk' op Q := by
  unfold kvOpAu1 kvAu1 etcdKV; rw [hst]

/-- A read update reads only the KV state's name. -/
theorem kvReadAu_names (γk γk' : KVNames) (hst : γk.st = γk'.st) (Q : KVState → IProp GF) :
    kvReadAu (GF := GF) γk Q = kvReadAu γk' Q := by
  unfold kvReadAu kvAu etcdKV; rw [hst]

/-- **The `*kv` `api` of the members `ms` at the KV `γ`** (persistent; see the section header). -/
def isKvOf (api : Loc) (γ : KVNames) (dup : Bool) (ms : List (SrvAt GF)) : IProp GF :=
  iprop(kvObjAt api (ms.map SrvAt.addr) ∗ kvRegs ms ∗ ([∗list] x ∈ ms, srvStart x) ∗
    ⌜(∀ x ∈ ms, x.γr.kv.st = γ.st) ∧ (dup = false → ∀ x ∈ ms, noRefusalAt x.addr) ∧
      receiptBound GF ≤ 2 ^ 62⌝)

instance isKvOf_persistent (api : Loc) (γ : KVNames) (dup : Bool) (ms : List (SrvAt GF)) :
    Persistent (isKvOf api γ dup ms) := by
  unfold isKvOf; infer_instance

/-- **The `*kv` `api` is a client of etcd's KV `γ`** (persistent; see the section header): of some
members, each at `γ`'s state; unless `dup`, refusal-free (a write is delivered at
most once); (D48) the store's receipts at most `2 ^ 62` (a sealed log is small, `idxCert_logOk`). -/
def isKv (api : Loc) (γ : KVNames) (dup : Bool) : IProp GF :=
  iprop(∃ ms : List (SrvAt GF), isKvOf api γ dup ms)

instance isKv_persistent (api : Loc) (γ : KVNames) (dup : Bool) :
    Persistent (isKv (GF := GF) api γ dup) := by
  unfold isKv; infer_instance

/-- A client of the members `ms` at `γ` is a client of `γ`. -/
theorem isKv_intro (api : Loc) (γ : KVNames) (dup : Bool) (ms : List (SrvAt GF))
    (hn : ∀ x ∈ ms, x.γr.kv.st = γ.st)
    (hr : dup = false → ∀ x ∈ ms, noRefusalAt x.addr) (hrb : receiptBound GF ≤ 2 ^ 62) :
    kvObjAt api (ms.map SrvAt.addr) ∗ kvRegs ms ∗ ([∗list] x ∈ ms, srvStart x) ⊢
      isKv api γ dup := by
  iintro ⟨#Ho, #Hr, #Hs⟩
  unfold isKv isKvOf
  iexists ms
  iframe #
  ipureintro; exact ⟨hn, hr, hrb⟩

/-- **A write's update, by the client's kind** (`rf`: refusal-free): persistent, or (a write sent
at most once, D29) fired at most once. -/
def writeUpd (rf : Bool) (P : IProp GF) : IProp GF :=
  iprop(□ P ∨ (⌜rf = true⌝ ∗ P))

/-- A persistent update serves any client. -/
theorem writeUpd_box (rf : Bool) (P : IProp GF) : (□ P : IProp GF) ⊢ writeUpd rf P := by
  unfold writeUpd; iintro #H; ileft; iexact H

/-- **A range's update at `γ`**: none (`Q` trivial) or, linearizable, a read update. -/
def rangeUpdK (γ : KVNames) (o : OpFull) (Q : KVState → IProp GF) : IProp GF :=
  iprop(⌜Q = fun _ => iprop(True)⌝ ∨ (⌜o.base.serializable = false⌝ ∗ kvReadAu γ Q))

instance rangeUpdK_persistent (γ : KVNames) (o : OpFull) (Q : KVState → IProp GF) :
    Persistent (rangeUpdK γ o Q) := by
  unfold rangeUpdK; infer_instance

/-- **A transaction's update at `γ`**: none (read-only), a read update (read-only, linearizable)
or a write's update (writing). -/
def txnUpdK (γ : KVNames) (t : TxnModel) (Q : KVState → IProp GF) : IProp GF :=
  iprop(⌜txn.txnReadonly t = true ∧ Q = fun _ => iprop(True)⌝ ∨
    (⌜txn.txnReadonly t = true ∧ txn.txnSerializable t = false⌝ ∗ kvReadAu γ Q) ∨
    (⌜txn.txnReadonly t = false ∧ txn.txnPlain t ∧ txnNoZeroEnd t⌝ ∗ kvOpAu1 γ (.txn t) Q))

/-- **What a put's reply says** (`m`): the state `σ` the update fired at (`Q σ`), the reply's
revision `σ`'s next, its previous key-value the key's record in `σ`'s current store if asked;
(D48) `σ` and the state after the put well-formed small logs' (`kvLogOk`). -/
def putStOk (o : OpFull) (Q : KVState → IProp GF) (m : PutRespM) : IProp GF :=
  iprop(∃ σ : KVState, Q σ ∗ ⌜m.hdr.revision = W64 ((σ.rev + 1 : Nat) : Int) ∧
    m.prev = (if o.base.prevKV then (σ.store.lookup o.key).map (KVRec.toKv o.key) else none) ∧
    σ.rev + 4 < 2 ^ 63 ∧ kvLogOk σ ∧ kvLogOk (kvOpStep (.put o) σ)⌝)

/-- **What a range's reply says**: a state `σ` (the one the read update fired at, `□ Q σ`, if
linearizable) at whose current revision the reply's header is, of whose store at the revision the
range reads (`readRev`: the one asked, at most the current, or the current) the reply's key-values
are the selection (`srvRangeOk`: the server's selection, sorted and limited as asked) and the
reply's count the count. -/
def rangeStOk (o : OpFull) (Q : KVState → IProp GF) (m : RangeRespM) : IProp GF :=
  iprop(∃ σ : KVState, (if o.base.serializable then iprop(True) else iprop(□ Q σ)) ∗
    ⌜sint.Z o.base.rev ≤ (σ.rev : Int) ∧
      txn.srvRangeOk o (σ.at (σ.readRev o.base.rev)).kvs m.kvs m.more ∧
      m.count = txn.srvCount o (σ.at (σ.readRev o.base.rev)).kvs true ∧
      m.hdr.revision = W64 (σ.rev : Int) ∧ σ.rev + 3 < 2 ^ 63 ∧ kvLogOk σ⌝)

/-- **What a delete's reply says**: the state `σ` the update fired at (`Q σ`), the reply's count
the keys of the range, its previous key-values theirs if asked, its revision the state's after
the delete (`kvOpStep`); (D48) `σ` and the state after the delete well-formed small logs'
(`kvLogOk`). -/
def delStOk (o : OpFull) (Q : KVState → IProp GF) (m : DelRespM) : IProp GF :=
  iprop(∃ σ : KVState, Q σ ∗ ⌜m.deleted = W64 ((rangeIn σ.kvs o).length : Int) ∧
    m.prevs = (if o.base.prevKV then rangeIn σ.kvs o else []) ∧
    m.hdr.revision = W64 ((kvOpStep (.deleteRange o) σ).rev : Int) ∧ σ.rev + 4 < 2 ^ 63 ∧
    kvLogOk σ ∧ kvLogOk (kvOpStep (.deleteRange o) σ)⌝)

/-- **What a transaction's reply says**: the state `σ` the update fired at (`Q σ` if writing;
`□ Q σ` if read-only and linearizable), the reply's verdict and its branch's responses the run's
at `σ` (`srvRunTxn`, `opRespsRel`), its revision `σ`'s (read-only) or the state's after the
transaction's changes (writing); (D48) `σ` a well-formed small log's (`kvLogOk`), and so the
state after a writing transaction's changes. -/
def txnStOk (t : TxnModel) (Q : KVState → IProp GF) (m : TxnRespM) : IProp GF :=
  iprop(∃ σ : KVState,
    (if txn.txnReadonly t then
      (if txn.txnSerializable t then iprop(True) else iprop(□ Q σ)) else Q σ) ∗
    ⌜m.succeeded = (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs t).1 ∧
      opRespsRel false (t.branch m.succeeded)
        (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs t).2.2 m.resps ∧
      m.hdr.revision = W64 ((if txn.txnReadonly t then σ.rev else
        (σ.commit (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs t).2.1).rev : Nat) : Int) ∧
      σ.rev + 3 < 2 ^ 63 ∧ kvLogOk σ ∧
      (txn.txnReadonly t = false → kvLogOk (σ.commit (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs t).2.1))⌝)

/-! ### The specs' atomic updates, in the proofs' terms -/

/-- An update under `□?dup` (persistent if the client's writes may be delivered more than once)
is a write's update by the client's kind. -/
theorem writeUpd_of_if (dup : Bool) (P P' : IProp GF) (h : P ⊢ P') :
    (□?dup P : IProp GF) ⊢ writeUpd (!dup) P' := by
  cases dup
  · show P ⊢ _
    unfold writeUpd
    iintro H
    iright
    isplitl []
    · ipureintro; rfl
    iapply h; iexact H
  · show (□ P : IProp GF) ⊢ _
    unfold writeUpd
    iintro #H
    ileft
    imodintro
    iapply h; iexact H

/-- A write's atomic update, as the specs state it, is `kvOpAu1`'s. -/
theorem writeAu_upd (dup : Bool) (γ : KVNames) (op : KVOp) (Q : KVState → IProp GF) :
    iprop(□?dup (AU <{ ∃∃ (σ : KVState), etcdKV γ σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
        <{ etcdKV γ (kvOpStep op σ), COMM Q σ }>)) ⊢ writeUpd (!dup) (kvOpAu1 γ op Q) :=
  writeUpd_of_if dup _ _ (by
    unfold kvOpAu1 kvAu1
    iintro H
    iexact H)

/-- A range's update, as the specs state it, is `rangeUpdK`'s. -/
theorem readAu_upd (γ : KVNames) (o : OpFull) (Q : KVState → IProp GF) :
    iprop(□ (⌜Q = fun _ => iprop(True)⌝ ∨ (⌜o.base.serializable = false⌝ ∗
      AU <{ ∃∃ (σ : KVState), etcdKV γ σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
        <{ etcdKV γ σ, COMM □ Q σ }>))) ⊢ □ rangeUpdK γ o Q := by
  unfold rangeUpdK kvReadAu kvAu
  iintro #H
  imodintro
  icases H with (%h | ⟨%h, #Ha⟩)
  · ileft; ipureintro; exact h
  · iright
    isplitr
    · ipureintro; exact h
    imodintro
    iexact Ha

/-- A transaction's update, as the spec states it, is `txnUpdK`'s. -/
theorem txnAu_upd (dup : Bool) (γ : KVNames) (t : TxnModel) (Q : KVState → IProp GF) :
    iprop(□?dup (⌜txn.txnReadonly t = true ∧ Q = fun _ => iprop(True)⌝ ∨
      (⌜txn.txnReadonly t = true ∧ txn.txnSerializable t = false⌝ ∗
        □ AU <{ ∃∃ (σ : KVState), etcdKV γ σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
          <{ etcdKV γ σ, COMM □ Q σ }>) ∨
      (⌜txn.txnReadonly t = false ∧ txn.txnPlain t ∧ txnNoZeroEnd t⌝ ∗
        AU <{ ∃∃ (σ : KVState), etcdKV γ σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
          <{ etcdKV γ (kvOpStep (.txn t) σ), COMM Q σ }>))) ⊢
      writeUpd (!dup) (txnUpdK γ t Q) :=
  writeUpd_of_if dup _ _ (by
    unfold txnUpdK kvReadAu kvAu kvOpAu1 kvAu1
    iintro (%H | ⟨%H, #Ha⟩ | ⟨%H, Ha⟩)
    · ileft; ipureintro; exact H
    · iright; ileft
      isplitr
      · ipureintro; exact H
      iexact Ha
    · iright; iright
      isplitr
      · ipureintro; exact H
      iexact Ha)

/-- A client that is refusal-free unless `dup`, by `writeUpd`'s flag. -/
theorem noRefusal_of_dup (ms : List (SrvAt GF)) (dup : Bool)
    (hr : dup = false → ∀ x ∈ ms, noRefusalAt x.addr) :
    (!dup) = true → ∀ x ∈ ms, noRefusalAt x.addr :=
  fun h => hr (by cases dup <;> simp_all)

/-! ### From `γ` to the members, from the members' replies to `γ`'s -/

/-- A put's update at `γ` is each member's. -/
theorem putUpd_of (ms : List (SrvAt GF)) (γ : KVNames)
    (hn : ∀ x ∈ ms, x.γr.kv.st = γ.st) (o : OpFull) (Q : KVState → IProp GF) :
    kvOpAu1 γ (.put o) Q ⊢ putUpd ms o Q := by
  unfold putUpd
  exact BigAndL.bigAndL_intro fun k x hk => by
    have h := hn x (List.mem_of_getElem? hk)
    rw [kvOpAu1_names x.γr.kv γ h]

/-- A delete's update at `γ` is each member's. -/
theorem delUpd_of (ms : List (SrvAt GF)) (γ : KVNames)
    (hn : ∀ x ∈ ms, x.γr.kv.st = γ.st) (o : OpFull) (Q : KVState → IProp GF) :
    kvOpAu1 γ (.deleteRange o) Q ⊢ delUpd ms o Q := by
  unfold delUpd
  exact BigAndL.bigAndL_intro fun k x hk => by
    have h := hn x (List.mem_of_getElem? hk)
    rw [kvOpAu1_names x.γr.kv γ h]

/-- A range's update at `γ` is each member's, persistently. -/
theorem rangeUpd_of (ms : List (SrvAt GF)) (γ : KVNames)
    (hn : ∀ x ∈ ms, x.γr.kv.st = γ.st) (o : OpFull) (Q : KVState → IProp GF) :
    (□ rangeUpdK γ o Q : IProp GF) ⊢ □ rangeUpd ms o Q := by
  unfold rangeUpd rangeUpdK
  refine intuitionistically_mono (BigAndL.bigAndL_intro fun k x hk => ?_)
  have h := hn x (List.mem_of_getElem? hk)
  rw [kvReadAu_names x.γr.kv γ h]

/-- A transaction's update at `γ` is each member's. -/
theorem txnUpd_of (ms : List (SrvAt GF)) (γ : KVNames)
    (hn : ∀ x ∈ ms, x.γr.kv.st = γ.st) (t : TxnModel)
    (Q : KVState → IProp GF) :
    txnUpdK γ t Q ⊢ txnUpd ms t Q := by
  unfold txnUpd
  exact BigAndL.bigAndL_intro fun k x hk => by
    have h := hn x (List.mem_of_getElem? hk)
    unfold txnUpdAt txnUpdK
    rw [kvReadAu_names x.γr.kv γ h, kvOpAu1_names x.γr.kv γ h]

/-- A transaction's update says whether its range ends are `[0]` (a writing one's are not). -/
theorem txnUpdK_nz (γ : KVNames) (t : TxnModel) (Q : KVState → IProp GF) :
    txnUpdK γ t Q ⊢ ⌜txn.txnReadonly t = false → txnNoZeroEnd t⌝ ∗ txnUpdK γ t Q := by
  unfold txnUpdK
  iintro (%H | ⟨%H, #Ha⟩ | ⟨%H, Ha⟩)
  · isplitr
    · ipureintro; intro h; rw [H.1] at h; cases h
    ileft; ipureintro; exact H
  · isplitr
    · ipureintro; intro h; rw [H.1] at h; cases h
    iright; ileft; iframe Ha; ipureintro; exact H
  · isplitr
    · ipureintro; intro _; exact H.2.2
    iright; iright; iframe Ha; ipureintro; exact H

/-- A write's update, by the client's kind, says what its update says. -/
theorem writeUpd_txn_nz (rf : Bool) (γ : KVNames) (t : TxnModel) (Q : KVState → IProp GF) :
    writeUpd rf (txnUpdK γ t Q) ⊢
      ⌜txn.txnReadonly t = false → txnNoZeroEnd t⌝ ∗ writeUpd rf (txnUpdK γ t Q) := by
  unfold writeUpd
  iintro (#H | ⟨%Hr, H⟩)
  · ihave ⟨%Hz, -⟩ := txnUpdK_nz γ t Q $$ H
    isplitr
    · ipureintro; exact Hz
    ileft; iexact H
  · ihave ⟨%Hz, H⟩ := txnUpdK_nz γ t Q $$ H
    isplitr
    · ipureintro; exact Hz
    iright; iframe H; ipureintro; exact Hr

/-- A write's update, by the client's kind, is a `*kv`'s precondition at the members. -/
theorem kvReqPre_of_upd (api : Loc) (ms : List (SrvAt GF)) (rf : Bool)
    (hr : rf = true → ∀ x ∈ ms, noRefusalAt x.addr) (P P' : IProp GF) (h : P ⊢ P') :
    writeUpd rf P ⊢ kvReqPre api (ms.map SrvAt.addr) P' := by
  unfold writeUpd kvReqPre
  iintro (#HP | ⟨%Hr, HP⟩)
  · ileft; imodintro; inext; iapply h; iexact HP
  · iright
    isplitl []
    · ipureintro
      intro a ha
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
      exact hr Hr x hx
    inext; iapply h; iexact HP

/-- A write's update, by the client's kind, is a `*txn`'s precondition at the members. -/
theorem txnReqPre_of_upd (tp : Loc) (ms : List (SrvAt GF)) (rf : Bool)
    (hr : rf = true → ∀ x ∈ ms, noRefusalAt x.addr) (P P' : IProp GF) (h : P ⊢ P') :
    writeUpd rf P ⊢ txnReqPre tp (ms.map SrvAt.addr) P' := by
  unfold writeUpd txnReqPre
  iintro (#HP | ⟨%Hr, HP⟩)
  · ileft; imodintro; inext; iapply h; iexact HP
  · iright
    isplitl []
    · ipureintro
      intro a ha
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
      exact hr Hr x hx
    inext; iapply h; iexact HP

/-- A delete of a range whose end is not `[0]` is read as itself. -/
theorem irrNoZeroEnd_delete (o : OpFull) (hz : o.base.rangeEnd ≠ [W8 0]) :
    irrNoZeroEnd (irrDeleteRange o) := by
  refine ⟨fun o' h => by simp [irrDeleteRange, apply.irrEmpty] at h, fun o' h => ?_,
    fun t h => by simp [irrDeleteRange, apply.irrEmpty] at h⟩
  simp only [irrDeleteRange, Option.some.injEq] at h
  subst h
  exact hz

/-- A transaction with no range end `[0]` is read as itself. -/
theorem irrNoZeroEnd_txn (t : TxnModel) (hz : txnNoZeroEnd t) : irrNoZeroEnd (irrTxn t) := by
  refine ⟨fun o h => by simp [irrTxn, apply.irrEmpty] at h,
    fun o h => by simp [irrTxn, apply.irrEmpty] at h, fun t' h => ?_⟩
  simp only [irrTxn, Option.some.injEq] at h
  subst h
  exact hz

open Iris.ProofMode in
/-- **A certified log is a well-formed small log** (D48): the certificate's facts (as
`idxSealed_pure`'s) and the receipts' bound on its changes (as `idxSealed_small`'s). -/
theorem idxCert_logOk (γ : mvcc.IdxNames) (log : mvcc.Log) (hrb : receiptBound GF ≤ 2 ^ 62) :
    mvcc.idxCert (GF := GF) γ log ⊢ ⌜mvcc.LogWf' log ∧ log.length < 2 ^ 63 ∧ txn.LogSmall log⌝ := by
  unfold mvcc.idxCert
  iintro ⟨-, %Hp, -, %Hm⟩
  ipureintro
  refine ⟨Hp.1, Hp.2.1, ?_⟩
  unfold txn.LogSmall txn.logChanges; unfold mvcc.logCh at Hm; omega

/-- The state of a write's log, the certified log after it extending it, is well formed. -/
theorem kvLogOk_of_step {rq : apply.IRRModel} {v3 : Bool} {x x' : apply.ApplyKV} {out : apply.ApplyOut}
    (h : apply.applyStep rq v3 x x' out) (hl : 2 ≤ x.log.length)
    (hc : mvcc.LogWf' x'.log ∧ x'.log.length < 2 ^ 63 ∧ txn.LogSmall x'.log) :
    kvLogOk (kvStateOf x.log) :=
  kvLogOk_of_prefix (applyStep_prefix rq v3 x x' out h) hc.1 hc.2.2 hc.2.1
    (by intro he; rw [he] at hl; simp at hl)

/-- Some member's put reply says what `putStOk` says. -/
theorem putAns_st (hrb : receiptBound GF ≤ 2 ^ 62) (ms : List (SrvAt GF)) (F : mvcc.Log)
    (o : OpFull) (Q : KVState → IProp GF)
    (m : PutRespM) : putAns ms F o Q m ⊢ putStOk o Q m := by
  unfold putAns putStOk
  iintro ⟨%x, -, H⟩
  iunfold putReplied at H
  icases H with ⟨%hm, %y, %y', %l, %skip, %Hp, #Hc, -, -, -, HQ⟩
  ihave %Hl := idxCert_logOk _ _ hrb $$ Hc
  obtain ⟨hst, hrev, -, -, hprev, -, hlen, hb⟩ := Hp
  have hne : y.log ≠ [] := by intro he; rw [he] at hlen; simp at hlen
  iexists kvStateOf y.log
  iframe HQ
  ipureintro
  refine ⟨?_, ?_, ?_, kvLogOk_of_step hst hlen Hl, ?_⟩
  · rw [hrev, kvStateOf_rev_succ _ hlen]
  · rw [hprev, ← findKey_kvs, ← kvStateOf_kvs]; rfl
  · rw [kvStateOf_rev]; omega
  · -- (D48) the state after the put: the log after it
    have hlog := kvs_put_applied_log o hm y y' l skip hst
    simp only [kvOpStep]
    split
    · exact kvLogOk_of_step hst hlen Hl
    · rw [kvStateOf_kvs]
      refine kvLogOk_commit _ ?_ hne Hl
      rw [hlog, mvcc.commitLog, if_neg (List.cons_ne_nil _ _)]
      exact List.prefix_refl _

/-- Some member's range reply says what `rangeStOk` says. -/
theorem rangeAns_st (hrb : receiptBound GF ≤ 2 ^ 62) (ms : List (SrvAt GF)) (c : w64)
    (F : mvcc.Log) (o : OpFull)
    (Q : KVState → IProp GF) (m : RangeRespM) :
    rangeAns ms c F o Q m ⊢ rangeStOk o Q m := by
  unfold rangeAns rangeStOk
  iintro ⟨%x, -, H⟩
  iunfold rangeReplyOk at H
  icases H with ⟨%l, #Hc, -, %Hl, -, HQ⟩
  ihave %Hlk := idxCert_logOk _ _ hrb $$ Hc
  obtain ⟨hlen, hlen', hrev, -, -, hle, hcount, hsel, -⟩ := Hl
  have h2 : sint.Z (W64 ((l.length : Int) - 1)) = (l.length : Int) - 1 := by word
  have hle' : sint.Z o.base.rev ≤ (l.length : Int) - 1 := by rw [hrev, h2] at hle; exact hle
  have hn : sint.nat (W64 ((l.length : Int) - 1)) = l.length - 1 := by unfold sint.nat; word
  -- the revision read: the one asked, or the header's (the log's last)
  have hRR : (kvStateOf l).readRev o.base.rev =
      sint.nat (mvcc.rangeRev m.hdr.revision o.base.rev) := by
    unfold KVState.readRev mvcc.rangeRev
    rw [kvStateOf_rev, hrev]
    by_cases h0 : sint.Z o.base.rev ≤ 0
    · simp only [h0, ↓reduceIte]; rw [hn]
    · simp only [h0, ↓reduceIte]
  have hRle : sint.nat (mvcc.rangeRev m.hdr.revision o.base.rev) ≤ l.length - 1 := by
    unfold mvcc.rangeRev; rw [hrev]
    by_cases h0 : sint.Z o.base.rev ≤ 0
    · simp only [h0, ↓reduceIte]; exact hn ▸ Nat.le_refl _
    · simp only [h0, ↓reduceIte]
      show (sint.Z o.base.rev).toNat ≤ l.length - 1
      omega
  iexists kvStateOf l
  iframe HQ
  ipureintro
  rw [hRR, kvStateOf_at_kvs l _ hRle]
  refine ⟨?_, hsel, hcount, ?_, ?_, kvLogOk_of l Hlk.1 Hlk.2.2 Hlk.2.1
    (by intro he; rw [he] at hlen; simp at hlen)⟩
  · rw [kvStateOf_rev]; omega
  · rw [hrev, kvStateOf_rev]
    congr 1
    omega
  · rw [kvStateOf_rev]; omega

/-- Some member's delete reply says what `delStOk` says (a range end not `[0]`). -/
theorem delAns_st (hrb : receiptBound GF ≤ 2 ^ 62) (ms : List (SrvAt GF)) (F : mvcc.Log)
    (o : OpFull) (Q : KVState → IProp GF)
    (m : DelRespM) (hz : o.base.rangeEnd ≠ [W8 0]) : delAns ms F o Q m ⊢ delStOk o Q m := by
  unfold delAns delStOk
  iintro ⟨%x, -, H⟩
  iunfold deleteReplied at H
  icases H with ⟨%hm, %rq', %op', %y, %y', %l, %skip, %Hp, #Hc, -, -, -, HQ⟩
  ihave %Hl := idxCert_logOk _ _ hrb $$ Hc
  obtain ⟨hw, hop', Hz, hst, hrev, -, -, hdel, hprevs, -, hlen, hb⟩ := Hp
  have hlog := kvs_delete_applied_log _ _ hm rq' y y' l skip hw hop' hst
  have hop : op' = o := Hz (irrNoZeroEnd_delete o hz)
  subst hop
  have hne : y.log ≠ [] := by intro he; rw [he] at hlen; simp at hlen
  have hs := kvStateOf_kvs y.log
  iexists kvStateOf y.log
  iframe HQ
  ipureintro
  refine ⟨by rw [hs]; exact hdel, by rw [hs]; exact hprevs, ?_, ?_, kvLogOk_of_step hst hlen Hl,
    ?_⟩
  · rw [hrev]
    simp only [kvOpStep]
    rw [hs, kvStateOf_commit_rev _ _ hlen]
  · rw [kvStateOf_rev]; omega
  · -- (D48) the state after the delete: the log after it
    simp only [kvOpStep]
    rw [hs]
    refine kvLogOk_commit _ ?_ hne Hl
    rw [hlog]; try exact List.prefix_refl _

/-- Some member's transaction reply says what `txnStOk` says (a writing one's range ends not
`[0]`). -/
theorem txnAns_st (hrb : receiptBound GF ≤ 2 ^ 62) (ms : List (SrvAt GF)) (c : w64)
    (F : mvcc.Log) (t : TxnModel)
    (Q : KVState → IProp GF) (m : TxnRespM)
    (hz : txn.txnReadonly t = false → txnNoZeroEnd t) :
    txnAns ms c F t Q m ⊢ txnStOk t Q m := by
  unfold txnAns txnStOk
  iintro ⟨%x, -, H⟩
  unfold txnReplied
  cases hro : txn.txnReadonly t
  · -- writing
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases H with ⟨%hm, %rq', %t', %y, %y', %l, %skip, %Hp, #Hc, -, -, -, HQ⟩
    ihave %Hl := idxCert_logOk _ _ hrb $$ Hc
    obtain ⟨hw, ht', Hz, hst, hrev, -, -, -, hlen, hb4, hok, hrel, hsk⟩ := Hp
    have hlog := kvs_txn_applied_log _ _ hm rq' y y' l skip hw ht' hst
    have ht : t' = t := Hz (irrNoZeroEnd_txn t (hz hro))
    subst ht hsk
    have hne : y.log ≠ [] := by intro he; rw [he] at hlen; simp at hlen
    have hr : ((kvStateOf y.log).rev + 1 : Nat) = y.log.length := kvStateOf_rev_succ _ hlen
    have hs := kvStateOf_kvs y.log
    iexists kvStateOf y.log
    iframe HQ
    ipureintro
    rw [hr, hs]
    refine ⟨hok, hrel, ?_, ?_, kvLogOk_of_step hst hlen Hl, fun _ => ?_⟩
    · rw [hrev, ← hs, kvStateOf_commit_rev _ _ hlen]
    · rw [kvStateOf_rev]; omega
    · -- (D48) the state after the transaction: the log after it
      refine kvLogOk_commit _ ?_ hne Hl
      rw [hlog]; try exact List.prefix_refl _
  · -- read-only
    simp only [↓reduceIte]
    icases H with ⟨%log, #Hc, -, %Hp, -, HQ⟩
    ihave %Hl := idxCert_logOk _ _ hrb $$ Hc
    obtain ⟨hlen, hb3, -, hrev, -, -, hok, hrel⟩ := Hp
    have hr : ((kvStateOf log).rev + 1 : Nat) = log.length := kvStateOf_rev_succ _ hlen
    have hs := kvStateOf_kvs log
    iexists kvStateOf log
    iframe HQ
    ipureintro
    rw [hr, hs]
    refine ⟨hok, hrel, ?_, ?_, kvLogOk_of log Hl.1 Hl.2.2 Hl.2.1
      (by intro he; rw [he] at hlen; simp at hlen), fun h => by cases h⟩
    · rw [hrev, kvStateOf_rev]
      congr 1
      omega
    · rw [kvStateOf_rev]; omega

/-! ### The calls' outcomes, weakened -/

theorem putCallOut_mono (Q Q' : PutRespM → IProp GF) (resp : Loc) (err : GoInterface)
    (h : ∀ m, Q m ⊢ Q' m) : putCallOut Q resp err ⊢ putCallOut Q' resp err := by
  unfold putCallOut
  iintro (⟨%He, %m, Hm, Hq⟩ | ⟨%He, #Hs, #Hc⟩)
  · ileft
    isplitl []
    · ipureintro; exact He
    iexists m
    iframe Hm
    iapply (h m) $$ Hq
  · iright; iframe #; ipureintro; exact He

theorem rangeCallOut_mono (Q Q' : RangeRespM → IProp GF) (resp : Loc) (err : GoInterface)
    (h : ∀ m, Q m ⊢ Q' m) : rangeCallOut Q resp err ⊢ rangeCallOut Q' resp err := by
  unfold rangeCallOut
  iintro (⟨%He, %m, Hm, Hq⟩ | ⟨%He, #Hs, #Hc⟩)
  · ileft
    isplitl []
    · ipureintro; exact He
    iexists m
    iframe Hm
    iapply (h m) $$ Hq
  · iright; iframe #; ipureintro; exact He

theorem deleteCallOut_mono (Q Q' : DelRespM → IProp GF) (resp : Loc) (err : GoInterface)
    (h : ∀ m, Q m ⊢ Q' m) : deleteCallOut Q resp err ⊢ deleteCallOut Q' resp err := by
  unfold deleteCallOut
  iintro (⟨%He, %m, Hm, Hq⟩ | ⟨%He, #Hs, #Hc⟩)
  · ileft
    isplitl []
    · ipureintro; exact He
    iexists m
    iframe Hm
    iapply (h m) $$ Hq
  · iright; iframe #; ipureintro; exact He

theorem txnCallOut_mono (Q Q' : TxnRespM → IProp GF) (resp : Loc) (err : GoInterface)
    (h : ∀ m, Q m ⊢ Q' m) : txnCallOut Q resp err ⊢ txnCallOut Q' resp err := by
  unfold txnCallOut
  iintro (⟨%He, %m, Hm, Hq⟩ | ⟨%He, #Hs, #Hc⟩)
  · ileft
    isplitl []
    · ipureintro; exact He
    iexists m
    iframe Hm
    iapply (h m) $$ Hq
  · iright; iframe #; ipureintro; exact He

/-! ### The specs' outcomes, in the proofs' terms -/

theorem putCallOut_st (o : OpFull) (Q : KVState → IProp GF) (resp : Loc) (err : GoInterface) :
    putCallOut (putStOk o Q) resp err ⊢
      (⌜err = GoInterface.nil⌝ ∗ ∃ (m : PutRespM) (σ : KVState), putRespMsg resp m ∗ Q σ ∗
        ⌜m.hdr.revision = W64 ((σ.rev + 1 : Nat) : Int) ∧
          m.prev = (if o.base.prevKV then (σ.store.lookup o.key).map (KVRec.toKv o.key) else none) ∧
          σ.rev + 4 < 2 ^ 63 ∧ kvLogOk σ ∧ kvLogOk (kvOpStep (.put o) σ)⌝) ∨
      (⌜err ≠ GoInterface.nil ∧ resp = null⌝ ∗ kvErr err) := by
  unfold putCallOut putStOk kvErr
  iintro (⟨%He, %m, Hm, %σ, HQ, %Hs⟩ | ⟨%He, #Hs, #Hc⟩)
  · ileft
    isplitl []
    · ipureintro; exact He
    iexists m, σ
    iframe Hm HQ
    ipureintro; exact Hs
  · iright
    isplitl []
    · ipureintro; exact ⟨He.1, He.2.2⟩
    iframe #
    ipureintro; exact He.2.1

theorem rangeCallOut_st (o : OpFull) (Q : KVState → IProp GF) (resp : Loc) (err : GoInterface) :
    rangeCallOut (rangeStOk o Q) resp err ⊢
      (⌜err = GoInterface.nil⌝ ∗ ∃ (m : RangeRespM) (σ : KVState), rangeRespMsg resp m ∗
        (if o.base.serializable then iprop(True) else iprop(□ Q σ)) ∗
        ⌜sint.Z o.base.rev ≤ (σ.rev : Int) ∧
          txn.srvRangeOk o (σ.at (σ.readRev o.base.rev)).kvs m.kvs m.more ∧
          m.count = txn.srvCount o (σ.at (σ.readRev o.base.rev)).kvs true ∧
          m.hdr.revision = W64 (σ.rev : Int) ∧ σ.rev + 3 < 2 ^ 63 ∧ kvLogOk σ⌝) ∨
      (⌜err ≠ GoInterface.nil ∧ resp = null⌝ ∗ kvErr err) := by
  unfold rangeCallOut rangeStOk kvErr
  iintro (⟨%He, %m, Hm, %σ, HQ, %Hs⟩ | ⟨%He, #Hs, #Hc⟩)
  · ileft
    isplitl []
    · ipureintro; exact He
    iexists m, σ
    iframe Hm HQ
    ipureintro; exact Hs
  · iright
    isplitl []
    · ipureintro; exact ⟨He.1, He.2.2⟩
    iframe #
    ipureintro; exact He.2.1

theorem deleteCallOut_st (o : OpFull) (Q : KVState → IProp GF) (resp : Loc) (err : GoInterface) :
    deleteCallOut (delStOk o Q) resp err ⊢
      (⌜err = GoInterface.nil⌝ ∗ ∃ (m : DelRespM) (σ : KVState), delRespMsg resp m ∗ Q σ ∗
        ⌜m.deleted = W64 ((rangeIn σ.kvs o).length : Int) ∧
          m.prevs = (if o.base.prevKV then rangeIn σ.kvs o else []) ∧
          m.hdr.revision = W64 ((kvOpStep (.deleteRange o) σ).rev : Int) ∧ σ.rev + 4 < 2 ^ 63 ∧
          kvLogOk σ ∧ kvLogOk (kvOpStep (.deleteRange o) σ)⌝) ∨
      (⌜err ≠ GoInterface.nil ∧ resp = null⌝ ∗ kvErr err) := by
  unfold deleteCallOut delStOk kvErr
  iintro (⟨%He, %m, Hm, %σ, HQ, %Hs⟩ | ⟨%He, #Hs, #Hc⟩)
  · ileft
    isplitl []
    · ipureintro; exact He
    iexists m, σ
    iframe Hm HQ
    ipureintro; exact Hs
  · iright
    isplitl []
    · ipureintro; exact ⟨He.1, He.2.2⟩
    iframe #
    ipureintro; exact He.2.1

theorem txnCallOut_st (t : TxnModel) (Q : KVState → IProp GF) (resp : Loc) (err : GoInterface) :
    txnCallOut (txnStOk t Q) resp err ⊢
      (⌜err = GoInterface.nil⌝ ∗ ∃ (m : TxnRespM) (σ : KVState), txnRespMsg resp m ∗
        (if txn.txnReadonly t then
          (if txn.txnSerializable t then iprop(True) else iprop(□ Q σ)) else Q σ) ∗
        ⌜m.succeeded = (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs t).1 ∧
          opRespsRel false (t.branch m.succeeded) (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs t).2.2 m.resps ∧
          m.hdr.revision = W64 ((if txn.txnReadonly t then σ.rev else
            (σ.commit (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs t).2.1).rev : Nat) : Int) ∧
          σ.rev + 3 < 2 ^ 63 ∧ kvLogOk σ ∧
          (txn.txnReadonly t = false → kvLogOk (σ.commit (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs t).2.1))⌝) ∨
      (⌜err ≠ GoInterface.nil ∧ resp = null⌝ ∗ kvErr err) := by
  unfold txnCallOut txnStOk kvErr
  iintro (⟨%He, %m, Hm, %σ, HQ, %Hs⟩ | ⟨%He, #Hs, #Hc⟩)
  · ileft
    isplitl []
    · ipureintro; exact He
    iexists m, σ
    iframe Hm HQ
    ipureintro; exact Hs
  · iright
    isplitl []
    · ipureintro; exact ⟨He.1, He.2.2⟩
    iframe #
    ipureintro; exact He.2.1

/-- **What `kv.Do` returns** for the `Op` `o`: a range's answer in the `get` field (an invalid
sort option is a client error, `rpctypes.ErrInvalidSortOption`), a put's in the `put` field, a
delete's in the `del` field (`rangeCallOut`, `putCallOut`, `deleteCallOut`, after
`ContextError`: a client error). -/
def doOut (o : OpFull) (Qp : PutRespM → IProp GF) (Qr : RangeRespM → IProp GF)
    (Qd : DelRespM → IProp GF) (r : go_etcd_io.etcd.client.v3.OpResponse) (err : GoInterface) :
    IProp GF :=
  if o.t = W64 1 then rangeCallOut Qr r.get' err
  else if o.t = W64 2 then putCallOut Qp r.put' err
  else deleteCallOut Qd r.del' err

theorem doOut_mono (o : OpFull) (Qp Qp' : PutRespM → IProp GF) (Qr Qr' : RangeRespM → IProp GF)
    (Qd Qd' : DelRespM → IProp GF) (r : go_etcd_io.etcd.client.v3.OpResponse) (err : GoInterface)
    (hr : o.t = W64 1 → ∀ m, Qr m ⊢ Qr' m) (hp : o.t = W64 2 → ∀ m, Qp m ⊢ Qp' m)
    (hd : o.t ≠ W64 1 → o.t ≠ W64 2 → ∀ m, Qd m ⊢ Qd' m) :
    doOut o Qp Qr Qd r err ⊢ doOut o Qp' Qr' Qd' r err := by
  unfold doOut
  by_cases h1 : o.t = W64 1
  · simp only [h1, ↓reduceIte]
    exact rangeCallOut_mono _ _ _ _ (hr h1)
  · by_cases h2 : o.t = W64 2
    · simp only [h1, h2, ↓reduceIte]
      exact putCallOut_mono _ _ _ _ (hp h2)
    · simp only [h1, h2, ↓reduceIte]
      exact deleteCallOut_mono _ _ _ _ (hd h1 h2)

/-- **A builder's connection may be any of its `*kv`'s** (its `kv` field's, `txnKvIs`). -/
theorem txnObjAt_conn (tp api : Loc) (addr addr' : List GoString) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (b : TxnBuild) :
    txnObjAt tp addr ci cd b ∗ txnKvIs tp api ∗ kvObjAt api addr' ⊢ txnObjAt tp addr' ci cd b := by
  iintro ⟨Hobj, #Hkv, #Hk'⟩
  iunfold txnObjAt at Hobj
  icases Hobj with ⟨%Htp, %api0, %cosl, %csl, %ssl, %fsl, %cps, %sps, %fps, %iw, #Hkvf, -, Hrest⟩
  iunfold txnKvIs at Hkv
  icombine Hkvf Hkv gives %Heq
  subst Heq
  unfold txnObjAt
  isplitl []
  · ipureintro; exact Htp
  iexists api0, cosl, csl, ssl, fsl, cps, sps, fps, iw
  iframe Hkvf Hk' Hrest

end abstract

section start_alloc
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **A call's start at every member**: the committed index at least `0` and the floor `[]`, both
free. -/
theorem srvStart_alloc (ms : List (SrvAt GF)) :
    ⊢ |==> [∗list] x ∈ ms, srvStart (GF := GF) x := by
  induction ms with
  | nil => iintro; imodintro; iapply BigSepL.bigSepL_nil.2; itrivial
  | cons x ms ih =>
    iintro
    imod mvcc.idxCert_nil (GF := GF) x.E.γ.idx with #HF0
    imod monoNatLbOwn_0 (GF := GF) x.γr.committed with #Hc0
    imod ih with #Hr
    imodintro
    iapply BigSepL.bigSepL_cons.2
    iframe Hr
    iunfold srvStart
    iframe HF0
    iunfold committedAtLeast
    iExactEq Hc0; rfl

end start_alloc

end client
end EtcdGrove
end Perennial
