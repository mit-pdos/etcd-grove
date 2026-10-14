/-
**The client meets the server** (unit C1, 2026-10-14; over the generic gRPC specification since
2026-10-14): the client's `kv.Put` and `kv.Get` on a `KV` made by `NewKV` over a connection to a
gRPC server, end to end through the transport (grpc's `ClientConn.Invoke`, the client side of the
trust boundary: `Spec/google_golang_org/grpc/ClientConn__Invoke.lean`; since unit P3a the
interceptor chain over one attempt, the client's retry interceptor proved and assumed of the
connection, `isEtcdConn`, through `kvObjAt`: `client/v3/EtcdInvoke.lean`), and etcd's gRPC handlers
(`v3rpc/Results.lean`: `put_end_to_end`, `range_end_to_end`, `deleteRange_end_to_end`) meeting
etcd's specs of the KV methods, served at an address (`grpc.serve`, the server side), with the
trust base of each printed in the build log (`#print axioms`). Lean-first (no Rocq counterpart);
the design: `notes/decisions.md`, "A generic gRPC specification".

**etcd's specs of the KV methods** (`etcdPutSpec`, `etcdRangeSpec`, `etcdDeleteSpec`: predicate
transformers over the messages' models, `GrpcSpec`): a caller asking the request `o` gets a reply
message `m` with `putReplyOk` (`rangeReplyOk` at the committed index `c` the caller knows of,
`committedAtLeast γr c`, persistent, `0` free; `deleteReplyOk`).

**The handlers** (`etcd_putHandlerOk`, `etcd_rangeHandlerOk`, `etcd_deleteHandlerOk`:
`grpcHandlerOk`): `kvServer.Put`/`Range`/`DeleteRange` at the server's `*kvServer` `p` (what
`pb.RegisterKVServer` registers, behind the quota wrapper and the server's unary interceptors,
which stay inside the trust boundary: `notes/decisions.md`), with the per-run slot `etcdRunSlot`
(the reader slots of `s.leadTimeMu`, the store, the logger and the read loop: every run gives
them back) and the context the runtime made; the id credit a run takes is minted from the
server's id budget `□ |==> idCred ρ.ids 1` (`srvStarted`'s, the server's own idealization: the
generator's `2 ^ 48 - 1` ids are assumed not to wrap).

**What the client learns** (`putReplyOk`, `rangeReplyOk`, `deleteReplyOk`, persistent): for a
`Put`, the apply thread's application of the put the server decoded at the log the entry met, the
reply's header revision that log's length, its ids the cluster's and member's, its previous
key-value the state's if asked, mvcc's certificate of the log after (`put_end_to_end`'s
`putAppliedOk`, carried to the reply); for a `Get`, the txn package's range at a certified log of
at least two revisions (`range_end_to_end`'s `rangeAnsOk`), read after the read index unless
serializable (`readLogOk γr c log`), the reply's key-values, `More` and `Count` the server's
selection; for a `DeleteRange`, the application of the delete the proposed data decode to.

The results:
* **`etcd_kv_served`** (the server side): a server with the listener at `addr` that hands the
  runtime `N` run slots registers etcd's three specs at `addr` (`isGrpcRpc`).
* **`client_put_end_to_end`**: `kv.Put(ctx, key, val)` with no options on a connection to `addr`
  whose `Put` is registered with `etcdPutSpec`: `nil` and a reply holding a message `m`
  (`putRespMsg`) with `putReplyOk` for the put `key ↦ val`; or an error.
* **`client_get_end_to_end`**: `kv.Get(ctx, key)` with no options, `Range` registered with
  `etcdRangeSpec`: `nil` and a reply holding a message `m` (`rangeRespMsg`) with `rangeReplyOk`
  for the get of `key`; or an error.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.Link
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Results

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

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A run's slot** (see the file header): the reader slots a run of etcd's KV handlers holds
and gives back: `s.leadTimeMu`'s (`srvCall`'s), the store's, the logger's and the read loop's
(`srvRdCall`'s). The server hands the gRPC runtime a number of them when it serves (bounded
`RWMutex` slots: at most that many runs at a time). -/
def etcdRunSlot (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  iprop(srvLeadTimeReader s ∗ mvcc.storeReader E.s E.γ ∗ srvLgReader s ∗ srvReadReader s γr)

/-- **What a successful `Put` of `o` tells the client** about the reply's message `m` (persistent;
see the file header). -/
def putReplyOk (E : apply.AEnv GF) (o : OpFull) (cid mid : w64) (m : PutRespM) : IProp GF :=
  iprop(∃ (hm : apply.HeaderModel) (x x' : apply.ApplyKV) (l : mvcc.Log) (skip : Bool),
    ⌜apply.applyStep (apply.withHeader (irrPut o) hm) true x x'
        (.dispatched (.applied l false) skip) ∧
      m.hdr.revision = W64 (x.log.length : Int) ∧ m.hdr.clusterId = cid ∧ m.hdr.memberId = mid ∧
      m.prev = (if o.base.prevKV then mvcc.findKey o.key (mvcc.stateAfter x.log) else none)⌝ ∗
    mvcc.idxCert E.γ.idx x'.log)

instance putReplyOk_persistent (E : apply.AEnv GF) (o : OpFull) (cid mid : w64) (m : PutRespM) :
    Persistent (putReplyOk E o cid mid m) := by
  unfold putReplyOk; infer_instance

/-- **What a successful `Get` of `o` tells the client** about the reply's message `m`
(persistent; see the file header). -/
def rangeReplyOk (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (o : OpFull) (cid mid : w64)
    (m : RangeRespM) : IProp GF :=
  iprop(∃ log : mvcc.Log, mvcc.idxCert E.γ.idx log ∗
    ⌜2 ≤ log.length ∧ log.length + 3 ≤ 2 ^ 63 ∧
      m.hdr.revision = W64 ((log.length : Int) - 1) ∧ m.hdr.clusterId = cid ∧
      m.hdr.memberId = mid ∧ sint.Z o.base.rev ≤ sint.Z m.hdr.revision ∧
      m.count = txn.srvCount o
        (mvcc.stateAt log (sint.nat (mvcc.rangeRev m.hdr.revision o.base.rev))) true ∧
      txn.srvRangeOk o (mvcc.stateAt log (sint.nat (mvcc.rangeRev m.hdr.revision o.base.rev)))
        m.kvs m.more⌝ ∗
    (if o.base.serializable then iprop(True) else readLogOk γr c log))

instance rangeReplyOk_persistent (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (o : OpFull)
    (cid mid : w64) (m : RangeRespM) : Persistent (rangeReplyOk E γr c o cid mid m) := by
  unfold rangeReplyOk; split <;> infer_instance

/-- **etcd's spec of the KV service's `Put`** (a predicate transformer; see the file header): a
caller asking the put `o` gets a reply message `m` with `putReplyOk`. -/
def etcdPutSpec (E : apply.AEnv GF) (cid mid : w64) : GrpcSpec (GF := GF) pbPutRequest pbPutResponse :=
  fun (o : OpFull) (Φ : PutRespM → IProp GF) =>
    iprop(∀ m : PutRespM, putReplyOk E o cid mid m -∗ Φ m)

/-- **etcd's spec of the KV service's `Range`**: a caller that knows the committed index `c`
(`committedAtLeast γr c`; `0` is free) asking the range `o` gets a reply message `m` with
`rangeReplyOk` at `c`. -/
def etcdRangeSpec (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64) :
    GrpcSpec (GF := GF) pbRangeRequest pbRangeResponse :=
  fun (o : OpFull) (Φ : RangeRespM → IProp GF) =>
    iprop(∃ c : w64, committedAtLeast γr c ∗ ∀ m : RangeRespM, rangeReplyOk E γr c o cid mid m -∗ Φ m)

/-- **What a successful `DeleteRange` of `o` tells the client** about the reply's message `m`
(persistent): the apply thread's application of the delete `op'` the proposed data decode to
(`o` itself unless a range end is empty, `deleteRange_end_to_end`'s `deleteAppliedOk`), at the log
the entry met, the reply's header revision the delete's write revision, its ids the cluster's and
member's, `Deleted` the number of keys in the range, `PrevKvs` their key-values if asked;
mvcc's certificate of the log after. -/
def deleteReplyOk (E : apply.AEnv GF) (o : OpFull) (cid mid : w64) (m : DelRespM) : IProp GF :=
  iprop(∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel) (op' : OpFull) (x x' : apply.ApplyKV)
      (l : mvcc.Log) (skip : Bool),
    ⌜irrWireOf (apply.withHeader (irrDeleteRange o) hm) rq' ∧ rq'.deleteRange = some op' ∧
      (irrNoZeroEnd (irrDeleteRange o) → op' = o) ∧
      apply.applyStep rq' true x x' (.dispatched (.applied l false) skip) ∧
      m.hdr.revision =
        W64 ((mvcc.writeRev x.log (txn.delChanges (mvcc.stateAfter x.log) op') : Nat) : Int) ∧
      m.hdr.clusterId = cid ∧ m.hdr.memberId = mid ∧
      m.deleted = W64 ((rangeIn (mvcc.stateAfter x.log) op').length : Int) ∧
      m.prevs = (if op'.base.prevKV then rangeIn (mvcc.stateAfter x.log) op' else [])⌝ ∗
    mvcc.idxCert E.γ.idx x'.log)

instance deleteReplyOk_persistent (E : apply.AEnv GF) (o : OpFull) (cid mid : w64)
    (m : DelRespM) : Persistent (deleteReplyOk E o cid mid m) := by
  unfold deleteReplyOk; infer_instance

/-- **etcd's spec of the KV service's `DeleteRange`**: a caller asking the delete `o` gets a
reply message `m` with `deleteReplyOk`. -/
def etcdDeleteSpec (E : apply.AEnv GF) (cid mid : w64) :
    GrpcSpec (GF := GF) pbDeleteRangeRequest pbDeleteRangeResponse :=
  fun (o : OpFull) (Φ : DelRespM → IProp GF) =>
    iprop(∀ m : DelRespM, deleteReplyOk E o cid mid m -∗ Φ m)

/-- **etcd's KV methods** as registered: `Put`, `Range` and `DeleteRange` of the `*kvServer` `p`,
with etcd's specs. -/
def etcdKVMethods (p : Loc) (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64) :
    List (GrpcMethod GF) :=
  [⟨go!"/etcdserverpb.KV/Put", pbPutRequest, pbPutResponse, etcdPutSpec E cid mid, 
     (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!!
      go!"Put")⟩,
   ⟨go!"/etcdserverpb.KV/Range", pbRangeRequest, pbRangeResponse, etcdRangeSpec E γr cid mid,
     (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!!
      go!"Range")⟩,
   ⟨go!"/etcdserverpb.KV/DeleteRange", pbDeleteRangeRequest, pbDeleteRangeResponse,
     etcdDeleteSpec E cid mid,
     (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!!
      go!"DeleteRange")⟩]

end defs

section proofs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `kvServerAt` reads of the server's parameters only what does not depend on the committed index
the caller knew of (`hdrIs`: the KV's `Rev()` resources). -/
theorem kvServerAt_srvKVAns (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (c c' cid mid n : w64) :
    v3rpc.kvServerAt (GF := GF) p s (v3rpc.srvKVAns s E ρ γr c) cid mid n =
      v3rpc.kvServerAt p s (v3rpc.srvKVAns s E ρ γr c') cid mid n := rfl

/-- A run's call resources give back its slot (the committed index dropped). -/
theorem etcdRunSlot_back (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (c : w64) :
    srvLeadTimeReader (GF := GF) s ∗ srvRdCall s E γr c ⊢ etcdRunSlot s E γr := by
  iintro ⟨Hlt, Hrd⟩
  unfold srvRdCall etcdRunSlot
  icases Hrd with ⟨Hsr, Hlg, -, Hrr⟩
  iframe

/-- **A run's context carries no trace** (`traceutil.ctxTraceIs ci none`, what `v3rpc.srvCall`
needs, unit P1b): `TraceKey` is a type of etcd's packages, under which the server's runtime sets no
value (`grpcRunCtx`, part of the trusted runtime). -/
theorem ctxTraceIs_none_of_runCtx (ci : GoInterfaceOk) :
    grpcRunCtx (GF := GF) ci ⊢ traceutil.ctxTraceIs ci none := by
  iintro #H
  iunfold grpcRunCtx at H
  unfold traceutil.ctxTraceIs
  iintro !> %Φ HΦ
  simp only [traceutil.traceKeyVal, go_etcd_io.etcd.pkg.v3.traceutil.TraceKey.ty]
  iapply H
  · ipureintro
    exact ⟨go!"pkg/v3/traceutil.TraceKey", rfl⟩
  inext
  iapply HΦ
  ipureintro
  left; rfl

/-- **etcd's `Put` handler meets etcd's `Put` spec** (`grpcHandlerOk`; from `put_end_to_end`):
a run, with its slot, the runtime's context, an id credit the server mints (`□ |==> idCred ρ.ids
1`, `srvStarted`'s), the decoded request: its slot back, the reply holds the response's
message, with `putReplyOk`. -/
theorem etcd_putHandlerOk (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (cid mid n : w64) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗
        v3rpc.kvServerAt p s (v3rpc.srvKVAns s E ρ γr (W64 0)) cid mid n ∗
        □ (|==> idCred ρ.ids 1) ⊢
      grpcHandlerOk (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!!
      go!"Put") (etcdRunSlot s E γr) (etcdPutSpec E cid mid) := by
  iintro ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hat, #HNR⟩
  unfold grpcHandlerOk
  iintro %o %Φ %ci %cd %r !> %Ψ ⟨Hslot, #Hctx, #Hrc, #Hr, Hspec⟩ HΨ
  ihave #Htr := ctxTraceIs_none_of_runCtx ci $$ Hrc
  rw [show (pbPutRequest (GF := GF)).recv r o = txn.putRequestIs r o from rfl]
  iunfold etcdRunSlot at Hslot
  icases Hslot with ⟨Hlt, Hsr, Hlg, Hrd⟩
  ihave Hu := HNR
  imod Hu with Hid
  imod (monoNatLbOwn_0 (GF := GF) γr.committed) with #H0
  iapply wp_fupd
  iapply (v3rpc.put_end_to_end p s E ρ γr (W64 0) cid mid n (GoInterface.ok ci) r o) $$
    [Hlt Hsr Hlg Hrd Hid]
  · iframe #
    unfold v3rpc.srvCall srvRdCall committedAtLeast
    isplitl [Hlt Hid]
    · iexists ci, cd
      iframe
      iframe #
      ipureintro; rfl
    iframe
    rw [show uint.nat (W64 0) = 0 from rfl]
    iframe H0
  inext
  iintro %resp %err Hpost
  cases hc : v3rpc.putCheck o with
  | some e =>
    icases Hpost with ⟨#Hco, Hc, Hc0⟩
    unfold v3rpc.srvCall
    icases Hc with ⟨%ci', %cd', -, -, -, -, Hlt⟩
    iunfold v3rpc.checkOut at Hco
    icases Hco with ⟨-, #Hev⟩
    iunfold txn.errVarIs at Hev
    icases Hev with ⟨%e', -, %He'⟩
    imodintro
    iapply HΨ
    isplitl [Hlt Hc0]
    · iapply etcdRunSlot_back s E γr (W64 0)
      iframe
    iintro %Hnil
    rw [He'] at Hnil; cases Hnil
  | none =>
    icases Hpost with (⟨%Herr, %h, %rv, %rv', #Hh, Hf, -, Hc0, Hap⟩ | ⟨%Herr, %e, Hc0, Hep⟩)
    · obtain ⟨rfl, Hrn⟩ := Herr
      iunfold v3rpc.putAppliedOk at Hap
      icases Hap with ⟨Hlt, %hm, %x, %x', %l, %skip, %Hst, Hout, #Hcert⟩
      iunfold apply.putOutcomeIs at Hout
      icases Hout with ⟨#Hpr, -⟩
      iunfold txn.putResponseIs at Hpr
      icases Hpr with ⟨-, %h2, %pk, #Hh2, %Hh2n, #Hrev, #Hpk, #Hprev⟩
      icombine Hh Hh2 gives %Heq
      subst Heq
      iunfold v3rpc.hdrFilled at Hf
      icases Hf with ⟨-, %t, %ld, Hcid, Hmid, Ht, Hl⟩
      ipersist Hcid
      ipersist Hmid
      ipersist Ht
      ipersist Hl
      imodintro
      iapply HΨ
      isplitl [Hlt Hc0]
      · iapply etcdRunSlot_back s E γr (W64 0)
        iframe
      iintro -
      iexists (PutRespM.mk (HdrM.mk cid mid (W64 (x.log.length : Int)) t ld)
        (if o.base.prevKV then mvcc.findKey o.key (mvcc.stateAfter x.log) else none))
      isplitl []
      · simp only [pbPutResponse]
        unfold putRespMsg hdrFull
        isplitl []
        · ipureintro; exact Hrn
        iexists h, pk
        iframe #
        ipureintro; exact Hh2n
      · iunfold etcdPutSpec at Hspec
        iapply Hspec
        unfold putReplyOk
        iexists hm, x, x', l, skip
        iframe #
        ipureintro
        exact ⟨Hst.1, rfl, rfl, rfl, rfl⟩
    · iunfold v3rpc.putErrOk at Hep
      icases Hep with ⟨Hlt, -⟩
      imodintro
      iapply HΨ
      isplitl [Hlt Hc0]
      · iapply etcdRunSlot_back s E γr (W64 0)
        iframe
      iintro %Hnil
      exact absurd Hnil Herr.2

/-- **etcd's `Range` handler meets etcd's `Range` spec** (`grpcHandlerOk`; from
`range_end_to_end`): as `etcd_putHandlerOk`, the reply with `rangeReplyOk` at the committed index
the caller knew of. -/
theorem etcd_rangeHandlerOk (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (cid mid n : w64) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗
        v3rpc.kvServerAt p s (v3rpc.srvKVAns s E ρ γr (W64 0)) cid mid n ∗
        □ (|==> idCred ρ.ids 1) ⊢
      grpcHandlerOk (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!!
      go!"Range") (etcdRunSlot s E γr) (etcdRangeSpec E γr cid mid) := by
  iintro ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hat, #HNR⟩
  unfold grpcHandlerOk
  iintro %o %Φ %ci %cd %r !> %Ψ ⟨Hslot, #Hctx, #Hrc, #Hr, Hspec⟩ HΨ
  ihave #Htr := ctxTraceIs_none_of_runCtx ci $$ Hrc
  rw [show (pbRangeRequest (GF := GF)).recv r o = txn.rangeRequestIs r o from rfl]
  iunfold etcdRangeSpec at Hspec
  icases Hspec with ⟨%c, #Hc0, Hspec⟩
  rw [kvServerAt_srvKVAns p s E ρ γr (W64 0) c]
  iunfold etcdRunSlot at Hslot
  icases Hslot with ⟨Hlt, Hsr, Hlg, Hrd⟩
  ihave Hu := HNR
  imod Hu with Hid
  iapply wp_fupd
  iapply (v3rpc.range_end_to_end p s E ρ γr c cid mid n (GoInterface.ok ci) r o) $$
    [Hlt Hsr Hlg Hrd Hid]
  · iframe #
    unfold v3rpc.srvCall srvRdCall
    isplitl [Hlt Hid]
    · iexists ci, cd
      iframe
      iframe #
      ipureintro; rfl
    iframe
    iframe Hc0
  inext
  iintro %resp %err Hpost
  cases hc : v3rpc.rangeCheck o with
  | some e =>
    icases Hpost with ⟨#Hco, Hc, Hcr⟩
    unfold v3rpc.srvCall
    icases Hc with ⟨%ci', %cd', -, -, -, -, Hlt⟩
    iunfold v3rpc.checkOut at Hco
    icases Hco with ⟨-, #Hev⟩
    iunfold txn.errVarIs at Hev
    icases Hev with ⟨%e', -, %He'⟩
    imodintro
    iapply HΨ
    isplitl [Hlt Hcr]
    · iapply etcdRunSlot_back s E γr c
      iframe
    iintro %Hnil
    rw [He'] at Hnil; cases Hnil
  | none =>
    icases Hpost with (⟨%Herr, %h, %rv, %rv', #Hh, Hf, -, Hcr, -, Hlt, Hans⟩ |
      ⟨%Herr, %e, Hcr, -, Hlt⟩)
    · obtain ⟨rfl, Hrn⟩ := Herr
      iunfold v3rpc.rangeAnsOk at Hans
      icases Hans with ⟨%log, #Hcert, %Hlog, #Hrl, Hres⟩
      iunfold txn.rangeResult at Hres
      icases Hres with (⟨%Hx, -⟩ | ⟨%Hx, -⟩ | ⟨%Hx, %kvs, %more, #Hrr, %Hsel⟩)
      · exact absurd Hx.2 Hrn
      · exact absurd Hx.2.2.2 Hrn
      iunfold txn.rangeResponseIs at Hrr
      icases Hrr with ⟨-, %h2, %sl, %ps, #Hh2, %Hh2n, #Hrev, #Hkvs, #Hps, #Hkv, #Hmore, #Hcount⟩
      icombine Hh Hh2 gives %Heq
      subst Heq
      iunfold v3rpc.hdrFilled at Hf
      icases Hf with ⟨-, %t, %ld, Hcid, Hmid, Ht, Hl⟩
      ipersist Hcid
      ipersist Hmid
      ipersist Ht
      ipersist Hl
      imodintro
      iapply HΨ
      isplitl [Hlt Hcr]
      · iapply etcdRunSlot_back s E γr c
        iframe
      iintro -
      iexists (RangeRespM.mk (HdrM.mk cid mid (W64 ((log.length : Int) - 1)) t ld) kvs more
        (txn.srvCount o (mvcc.stateAt log (sint.nat (mvcc.rangeRev (W64 ((log.length : Int) - 1))
          o.base.rev))) true))
      isplitl []
      · simp only [pbRangeResponse]
        unfold rangeRespMsg hdrFull
        isplitl []
        · ipureintro; exact Hrn
        iexists h, sl, ps
        iframe #
        ipureintro; exact Hh2n
      · iapply Hspec
        unfold rangeReplyOk
        iexists log
        iframe #
        ipureintro
        exact ⟨Hlog.1, Hlog.2.1, rfl, rfl, rfl, Hx.1, rfl, Hsel⟩
    · imodintro
      iapply HΨ
      isplitl [Hlt Hcr]
      · iapply etcdRunSlot_back s E γr c
        iframe
      iintro %Hnil
      exact absurd Hnil Herr.2

/-- **etcd's `DeleteRange` handler meets etcd's `DeleteRange` spec** (`grpcHandlerOk`; from
`deleteRange_end_to_end`): as `etcd_putHandlerOk`, the reply with `deleteReplyOk`. A third
registered method needs only this (its spec and handler proof), no new axiom. -/
theorem etcd_deleteHandlerOk (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (cid mid n : w64) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗
        v3rpc.kvServerAt p s (v3rpc.srvKVAns s E ρ γr (W64 0)) cid mid n ∗
        □ (|==> idCred ρ.ids 1) ⊢
      grpcHandlerOk
        (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!!
          go!"DeleteRange")
        (etcdRunSlot s E γr) (etcdDeleteSpec E cid mid) := by
  iintro ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hat, #HNR⟩
  unfold grpcHandlerOk
  iintro %o %Φ %ci %cd %r !> %Ψ ⟨Hslot, #Hctx, #Hrc, #Hr, Hspec⟩ HΨ
  ihave #Htr := ctxTraceIs_none_of_runCtx ci $$ Hrc
  rw [show (pbDeleteRangeRequest (GF := GF)).recv r o = txn.deleteRangeRequestIs r o from rfl]
  iunfold etcdRunSlot at Hslot
  icases Hslot with ⟨Hlt, Hsr, Hlg, Hrd⟩
  ihave Hu := HNR
  imod Hu with Hid
  imod (monoNatLbOwn_0 (GF := GF) γr.committed) with #H0
  iapply wp_fupd
  iapply (v3rpc.deleteRange_end_to_end p s E ρ γr (W64 0) cid mid n (GoInterface.ok ci) r o) $$
    [Hlt Hsr Hlg Hrd Hid]
  · iframe #
    unfold v3rpc.srvCall srvRdCall committedAtLeast
    isplitl [Hlt Hid]
    · iexists ci, cd
      iframe
      iframe #
      ipureintro; rfl
    iframe
    rw [show uint.nat (W64 0) = 0 from rfl]
    iframe H0
  inext
  iintro %resp %err Hpost
  cases hc : v3rpc.deleteCheck o with
  | some e =>
    icases Hpost with ⟨#Hco, Hc, Hc0⟩
    unfold v3rpc.srvCall
    icases Hc with ⟨%ci', %cd', -, -, -, -, Hlt⟩
    iunfold v3rpc.checkOut at Hco
    icases Hco with ⟨-, #Hev⟩
    iunfold txn.errVarIs at Hev
    icases Hev with ⟨%e', -, %He'⟩
    imodintro
    iapply HΨ
    isplitl [Hlt Hc0]
    · iapply etcdRunSlot_back s E γr (W64 0)
      iframe
    iintro %Hnil
    rw [He'] at Hnil; cases Hnil
  | none =>
    icases Hpost with (⟨%Herr, %h, %rv, %rv', #Hh, Hf, -, Hc0, Hap⟩ | ⟨%Herr, %e, Hc0, Hep⟩)
    · obtain ⟨rfl, Hrn⟩ := Herr
      iunfold v3rpc.deleteAppliedOk at Hap
      icases Hap with ⟨Hlt, %hm, %rq', %op', %x, %x', %l, %skip, %Hst, Hout, #Hcert⟩
      iunfold apply.deleteOutcomeIs at Hout
      icases Hout with ⟨#Hdr, -⟩
      iunfold txn.deleteRangeResponseIs at Hdr
      icases Hdr with ⟨-, %h2, %sl, %ps, #Hh2, %Hh2n, #Hrev, #Hdel, #Hpk, #Hps, #Hkvs⟩
      icombine Hh Hh2 gives %Heq
      subst Heq
      iunfold v3rpc.hdrFilled at Hf
      icases Hf with ⟨-, %t, %ld, Hcid, Hmid, Ht, Hl⟩
      ipersist Hcid
      ipersist Hmid
      ipersist Ht
      ipersist Hl
      imodintro
      iapply HΨ
      isplitl [Hlt Hc0]
      · iapply etcdRunSlot_back s E γr (W64 0)
        iframe
      iintro -
      iexists (DelRespM.mk (HdrM.mk cid mid
          (W64 ((mvcc.writeRev x.log (txn.delChanges (mvcc.stateAfter x.log) op') : Nat) : Int))
          t ld)
        (W64 ((rangeIn (mvcc.stateAfter x.log) op').length : Int))
        (if op'.base.prevKV then rangeIn (mvcc.stateAfter x.log) op' else []))
      isplitl []
      · simp only [pbDeleteRangeResponse]
        unfold delRespMsg hdrFull
        isplitl []
        · ipureintro; exact Hrn
        iexists h, sl, ps
        iframe #
        ipureintro; exact Hh2n
      · iunfold etcdDeleteSpec at Hspec
        iapply Hspec
        unfold deleteReplyOk
        iexists hm, rq', op', x, x', l, skip
        iframe #
        ipureintro
        exact ⟨Hst.1, Hst.2.1, Hst.2.2.1, Hst.2.2.2.1, rfl, rfl, rfl, rfl, rfl⟩
    · iunfold v3rpc.deleteErrOk at Hep
      icases Hep with ⟨Hlt, -⟩
      imodintro
      iapply HΨ
      isplitl [Hlt Hc0]
      · iapply etcdRunSlot_back s E γr (W64 0)
        iframe
      iintro %Hnil
      exact absurd Hnil Herr.2

/-- **etcd's server serves its KV methods** (the server side, `grpc_serve_rpcs`): a server with
the listener at `addr` that hands the gRPC runtime `N` run slots (`etcdRunSlot`) registers etcd's
`Put`, `Range` and `DeleteRange` specs at `addr` (`isGrpcRpc`). Premises: the server's (`isServerReq`,
`isServerRead`, its `*kvServer`, the id budget `□ |==> idCred ρ.ids 1` of `srvStarted`), the
packages'. -/
theorem etcd_kv_served (addr : GoString) (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (γr : ReadNames) (cid mid n : w64) (N : Nat) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗
        v3rpc.kvServerAt p s (v3rpc.srvKVAns s E ρ γr (W64 0)) cid mid n ∗
        □ (|==> idCred ρ.ids 1) ∗ grpcListener addr ∗
        ([∗list] _x ∈ List.replicate N (), etcdRunSlot s E γr) ⊢
      |={⊤}=> isGrpcRpc addr go!"/etcdserverpb.KV/Put" (etcdPutSpec E cid mid) ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/Range" (etcdRangeSpec E γr cid mid) ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/DeleteRange" (etcdDeleteSpec E cid mid) := by
  iintro ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hat, #HNR, Hl, Hslots⟩
  ihave #Hp := etcd_putHandlerOk p s E ρ γr cid mid n $$ []
  · iframe #
  ihave #Hr := etcd_rangeHandlerOk p s E ρ γr cid mid n $$ []
  · iframe #
  ihave #Hd := etcd_deleteHandlerOk p s E ρ γr cid mid n $$ []
  · iframe #
  imod (grpc_serve_rpcs addr (etcdKVMethods p E γr cid mid) (etcdRunSlot s E γr) N
    (by simp only [etcdKVMethods, List.map]; decide)) $$ [Hl Hslots] with Hrpcs
  · iframe
    imodintro
    simp only [etcdKVMethods]
    iframe #
    iapply BigSepL.bigSepL_nil.2
    itrivial
  simp only [etcdKVMethods]
  icases Hrpcs with ⟨#H1, #H2, #H3, -⟩
  imodintro
  iframe #

/-- **`client_put_end_to_end`** (see the file header): `kv.Put(ctx, key, val)` with no options
(`optsAt sl []`, e.g. `nil`) on a `*kv` over a connection to the server at `addr` (`kvObjAt`:
what `NewKV` returns, `v3.wp_NewKV`) whose `Put` is registered with etcd's spec (`isGrpcRpc`, what
`etcd_kv_served` gives): `nil` and the reply's message `m` with `putReplyOk` for the put
`key ↦ val` the server decodes (no lease, no previous key-value, value and lease not ignored); or
an error and no reply. Premises: the registration, the context's (`ctxErrClient`), the package's.
-/
theorem client_put_end_to_end (api : Loc) (addr : GoString) (E : apply.AEnv GF) (cid mid : w64)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (key val : GoString) (sl : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvObjAt api addr ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/Put" (etcdPutSpec E cid mid) ∗
        context.isContext ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] }}
      (App (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
          go!"Put")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : PutRespM, putRespMsg resp m ∗
            putReplyOk E (txn.putOpOf key val (W64 0) false false false) cid mid m) ∨
          ⌜err ≠ GoInterface.nil ∧ resp = null⌝ }} := by
  iintro %Φ ⟨#Pc, #Hkv, #Hrpc, #Hctx, #Hce, #Hopts⟩ HΦ
  iapply (v3.kv.wp_Put api addr ci cd key val sl [] (etcdPutSpec E cid mid)
    (putReplyOk E (txn.putOpOf key val (W64 0) false false false) cid mid)) $$ []
  · iframe #
    isplitl []
    · ipureintro
      refine ⟨?_, rfl⟩
      unfold opPutModel OpFull.putPanics opFold OpFull.putInit OpFull.newOp OpModel.zero
      simp
    · have Hw : putWireOf (opPutModel key val []) =
          txn.putOpOf key val (W64 0) false false false := rfl
      rw [Hw]
      imodintro
      inext
      unfold etcdPutSpec
      iintro %m Hm
      iexact Hm
  inext
  iintro %resp %err Hout
  iapply HΦ
  iunfold putCallOut at Hout
  icases Hout with (⟨%Herr, %m, Hm, Hq⟩ | ⟨%Herr, -⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m
    iframe
  · iright
    ipureintro; exact ⟨Herr.1, Herr.2.2⟩

/-- **`client_get_end_to_end`** (see the file header): `kv.Get(ctx, key)` with no options on a
`*kv` over a connection to the server at `addr` whose `Range` is registered with etcd's spec, by
a client that knows the committed index `c` (`committedAtLeast γr c`; `0` is free): `nil` and the
reply's message `m` with `rangeReplyOk` for the get of `key` the server decodes (the key alone, at
the latest revision, linearizable: read after the read index, at a log extending the log applied
through an index at least `c`); or an error and no reply. -/
theorem client_get_end_to_end (api : Loc) (addr : GoString) (E : apply.AEnv GF) (γr : ReadNames)
    (c cid mid : w64) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key : GoString) (sl : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvObjAt api addr ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/Range" (etcdRangeSpec E γr cid mid) ∗
        context.isContext ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗ committedAtLeast γr c }}
      (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
          go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : RangeRespM, rangeRespMsg resp m ∗
            rangeReplyOk E γr c (txn.rangeOpOf key [] (W64 0) (W64 0) (W32 0) (W32 0) false false
              false (W64 0) (W64 0) (W64 0) (W64 0)) cid mid m) ∨
          ⌜err ≠ GoInterface.nil ∧ resp = null⌝ }} := by
  iintro %Φ ⟨#Pc, #Hkv, #Hrpc, #Hctx, #Hce, #Hopts, #Hc0⟩ HΦ
  iapply (v3.kv.wp_Get api addr ci cd key sl [] (etcdRangeSpec E γr cid mid)
    (rangeReplyOk E γr c (txn.rangeOpOf key [] (W64 0) (W64 0) (W32 0) (W32 0) false false false
      (W64 0) (W64 0) (W64 0) (W64 0)) cid mid)) $$ []
  · iframe #
    isplitl []
    · ipureintro
      refine ⟨?_, rfl, rfl⟩
      unfold opGetPanics opFold OpFull.newOp
      simp
    · have Hw : rangeWireOf (opGetModel key []) = txn.rangeOpOf key [] (W64 0) (W64 0) (W32 0)
          (W32 0) false false false (W64 0) (W64 0) (W64 0) (W64 0) := rfl
      rw [Hw]
      imodintro
      inext
      unfold etcdRangeSpec
      iexists c
      iframe #
      iintro %m Hm
      iexact Hm
  inext
  iintro %resp %err Hout
  iapply HΦ
  iunfold rangeCallOut at Hout
  icases Hout with (⟨%Herr, %m, Hm, Hq⟩ | ⟨%Herr, -⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m
    iframe
  · iright
    ipureintro; exact ⟨Herr.1, Herr.2.2⟩

end proofs

end client

#print axioms Perennial.EtcdGrove.client.client_put_end_to_end
#print axioms Perennial.EtcdGrove.client.client_get_end_to_end
#print axioms Perennial.EtcdGrove.client.etcd_putHandlerOk
#print axioms Perennial.EtcdGrove.client.etcd_rangeHandlerOk
#print axioms Perennial.EtcdGrove.client.etcd_deleteHandlerOk
#print axioms Perennial.EtcdGrove.client.etcd_kv_served
#print axioms Perennial.EtcdGrove.client.v3.kv.wp_Put
#print axioms Perennial.EtcdGrove.client.v3.kv.wp_Get
#print axioms Perennial.EtcdGrove.client.v3.kv.wp_Do
#print axioms Perennial.EtcdGrove.client.v3.wp_NewKV
#print axioms Perennial.EtcdGrove.client.v3.wp_ContextError

end EtcdGrove
end Perennial
