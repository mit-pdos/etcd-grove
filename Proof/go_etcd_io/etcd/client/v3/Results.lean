/-
**The client meets the server** (unit C1, 2026-10-14): the client's `kv.Put` and `kv.Get` on a
`KV` made by `NewKV` over a connection to etcd's server, end to end through the gRPC transport
(grpc's `ClientConn.Invoke`, the trust boundary: `Spec/google_golang_org/grpc/
ClientConn__Invoke.lean`) and the server's gRPC handlers (`v3rpc/Results.lean`:
`put_end_to_end`, `range_end_to_end`), with the trust base of each printed in the build log
(`#print axioms`). Lean-first (no Rocq counterpart); the design: `notes/decisions.md`, "The client
meets the server (unit C1)".

**The server's end of the connection** (`etcdKVConn p s E ρ γr`): the handlers of the
`*kvServer` `p` (`kvServer.Put`, `kvServer.Range`, what `pb.RegisterKVServer` registers, behind the
quota wrapper whose success is the handler's: `notes/decisions.md`), and what the server's
runtime gives each run: `srvCall` (a context, one id credit, a reader slot of `s.leadTimeMu`) and
`srvRdCall` but the committed index the caller knew of (the store's reader slots, the logger's
and the read loop's): the server's runtime holds them (an assumption of the transport contract:
the server answers fewer requests than its id generator's `2 ^ 48 - 1` credits, the reader slots
come back). A linearizable `Get` brings the committed index `c` it knows of
(`committedAtLeast γr c`, persistent; `0` is free).

**What the client learns** (`putReplyOk`, `rangeReplyOk`, persistent): for a `Put`, the apply
thread's application of the put the server decoded at the log the entry met, the reply's header
revision that log's length, its ids the cluster's and member's, its previous key-value the
state's if asked, mvcc's certificate of the log after (`put_end_to_end`'s `putAppliedOk`, carried
to the reply); for a `Get`, the txn package's range at a certified log of at least two revisions
(`range_end_to_end`'s `rangeAnsOk`), read after the read index unless serializable
(`readLogOk γr c log`), the reply's key-values, `More` and `Count` the server's selection.

The results:
* **`client_put_end_to_end`**: `kv.Put(ctx, key, val)` with no options: `nil` and a reply holding
  a message `m` (`putRespMsg`) with `putReplyOk` for the put `key ↦ val`; or an error.
* **`client_get_end_to_end`**: `kv.Get(ctx, key)` with no options: `nil` and a reply holding a
  message `m` (`rangeRespMsg`) with `rangeReplyOk` for the get of `key`; or an error.
* **`etcd_putRunOk`**, **`etcd_rangeRunOk`**: what a run of the server's handlers gives
  (`putRunOk`, `rangeRunOk` at `etcdKVConn`), from `put_end_to_end`, `range_end_to_end`.
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

/-- **etcd's server at the other end of a connection** (see the file header). -/
def etcdKVConn (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) : KVConn GF where
  put := (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!!
    go!"Put")
  range := (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!!
    go!"Range")
  R ctx := iprop(v3rpc.srvCall s ρ ctx ∗ mvcc.storeReader E.s E.γ ∗ srvLgReader s ∗
    srvReadReader s γr)

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

/-- **A run of etcd's `Put` handler** (`putRunOk` at `etcdKVConn`; from `put_end_to_end`): the
reply holds the response's message, with `putReplyOk`. -/
theorem etcd_putRunOk (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (cid mid n : w64) (o : OpFull) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗
        v3rpc.kvServerAt p s (v3rpc.srvKVAns s E ρ γr (W64 0)) cid mid n ⊢
      putRunOk (etcdKVConn p s E ρ γr) o (putReplyOk E o cid mid) := by
  iintro ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hat⟩
  unfold putRunOk
  simp only [etcdKVConn]
  iintro %ctx %r !> %Φ ⟨⟨Hc, Hsr, Hlg, Hrd⟩, #Hr⟩ HΦ
  imod (monoNatLbOwn_0 (GF := GF) γr.committed) with #H0
  iapply wp_fupd
  iapply (v3rpc.put_end_to_end p s E ρ γr (W64 0) cid mid n ctx r o) $$ [Hc Hsr Hlg Hrd]
  · iframe #
    iframe
    unfold srvRdCall committedAtLeast
    iframe
    rw [show uint.nat (W64 0) = 0 from rfl]
    iexact H0
  inext
  iintro %resp %err Hpost
  cases hc : v3rpc.putCheck o with
  | some e =>
    icases Hpost with ⟨#Hco, -, -⟩
    iunfold v3rpc.checkOut at Hco
    icases Hco with ⟨-, #Hev⟩
    iunfold txn.errVarIs at Hev
    icases Hev with ⟨%e', -, %He'⟩
    imodintro
    iapply HΦ
    iintro %Hnil
    rw [He'] at Hnil; cases Hnil
  | none =>
    icases Hpost with (⟨%Herr, %h, %rv, %rv', #Hh, Hf, -, -, Hap⟩ | ⟨%Herr, -⟩)
    · obtain ⟨rfl, Hrn⟩ := Herr
      iunfold v3rpc.putAppliedOk at Hap
      icases Hap with ⟨-, %hm, %x, %x', %l, %skip, %Hst, Hout, #Hcert⟩
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
      iapply HΦ
      iintro -
      iexists (PutRespM.mk (HdrM.mk cid mid (W64 (x.log.length : Int)) t ld)
        (if o.base.prevKV then mvcc.findKey o.key (mvcc.stateAfter x.log) else none))
      isplitl []
      · unfold putRespMsg hdrFull
        isplitl []
        · ipureintro; exact Hrn
        iexists h, pk
        iframe #
        ipureintro; exact Hh2n
      · imodintro
        unfold putReplyOk
        iexists hm, x, x', l, skip
        iframe #
        ipureintro
        exact ⟨Hst.1, rfl, rfl, rfl, rfl⟩
    · imodintro
      iapply HΦ
      iintro %Hnil
      exact absurd Hnil Herr.2

/-- **A run of etcd's `Range` handler** (`rangeRunOk` at `etcdKVConn`; from `range_end_to_end`),
for a client that knows the committed index `c` (`committedAtLeast γr c`): the reply holds the
response's message, with `rangeReplyOk` at `c`. -/
theorem etcd_rangeRunOk (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (c cid mid n : w64) (o : OpFull) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗
        v3rpc.kvServerAt p s (v3rpc.srvKVAns s E ρ γr (W64 0)) cid mid n ∗
        committedAtLeast γr c ⊢
      rangeRunOk (etcdKVConn p s E ρ γr) o (rangeReplyOk E γr c o cid mid) := by
  iintro ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hat, #Hc0⟩
  rw [kvServerAt_srvKVAns p s E ρ γr (W64 0) c]
  unfold rangeRunOk
  simp only [etcdKVConn]
  iintro %ctx %r !> %Φ ⟨⟨Hc, Hsr, Hlg, Hrd⟩, #Hr⟩ HΦ
  iapply wp_fupd
  iapply (v3rpc.range_end_to_end p s E ρ γr c cid mid n ctx r o) $$ [Hc Hsr Hlg Hrd]
  · iframe #
    iframe
    unfold srvRdCall
    iframe
    iexact Hc0
  inext
  iintro %resp %err Hpost
  cases hc : v3rpc.rangeCheck o with
  | some e =>
    icases Hpost with ⟨#Hco, -, -⟩
    iunfold v3rpc.checkOut at Hco
    icases Hco with ⟨-, #Hev⟩
    iunfold txn.errVarIs at Hev
    icases Hev with ⟨%e', -, %He'⟩
    imodintro
    iapply HΦ
    iintro %Hnil
    rw [He'] at Hnil; cases Hnil
  | none =>
    icases Hpost with (⟨%Herr, %h, %rv, %rv', #Hh, Hf, -, -, -, -, Hans⟩ | ⟨%Herr, -⟩)
    · obtain ⟨rfl, Hrn⟩ := Herr
      iunfold v3rpc.rangeAnsOk at Hans
      icases Hans with ⟨%log, #Hcert, %Hlog, #Hrl, #Hres⟩
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
      iapply HΦ
      iintro -
      iexists (RangeRespM.mk (HdrM.mk cid mid (W64 ((log.length : Int) - 1)) t ld) kvs more
        (txn.srvCount o (mvcc.stateAt log (sint.nat (mvcc.rangeRev (W64 ((log.length : Int) - 1))
          o.base.rev))) true))
      isplitl []
      · unfold rangeRespMsg hdrFull
        isplitl []
        · ipureintro; exact Hrn
        iexists h, sl, ps
        iframe #
        ipureintro; exact Hh2n
      · imodintro
        unfold rangeReplyOk
        iexists log
        iframe #
        ipureintro
        exact ⟨Hlog.1, Hlog.2.1, rfl, rfl, rfl, Hx.1, rfl, Hsel⟩
    · imodintro
      iapply HΦ
      iintro %Hnil
      exact absurd Hnil Herr.2

/-- **`client_put_end_to_end`** (see the file header): `kv.Put(ctx, key, val)` with no options
(`optsAt sl []`, e.g. `nil`) on a `*kv` over a connection to etcd's server (`kvObjAt` at
`etcdKVConn`: what `NewKV` returns, `v3.wp_NewKV`): `nil` and the reply's message `m` with
`putReplyOk` for the put `key ↦ val` the server decodes (no lease, no previous key-value, value
and lease not ignored); or an error and no reply. Premises: the server's (`isServerReq`,
`isServerRead`, its `*kvServer`), the context's (`ctxErrClient`), the packages'. -/
theorem client_put_end_to_end (api p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (cid mid n : w64) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key val : GoString) (sl : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗
        v3rpc.kvServerAt p s (v3rpc.srvKVAns s E ρ γr (W64 0)) cid mid n ∗
        kvObjAt api (etcdKVConn p s E ρ γr) ∗ context.isContext ci cd ∗ ctxErrClient ci cd ∗
        optsAt sl [] }}
      (App (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
          go!"Put")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : PutRespM, putRespMsg resp m ∗
            putReplyOk E (txn.putOpOf key val (W64 0) false false false) cid mid m) ∨
          ⌜err ≠ GoInterface.nil ∧ resp = null⌝ }} := by
  iintro %Φ ⟨#Pc, #Pv, #Ps, #Hsrv, #Hsrd, #Hat, #Hkv, #Hctx, #Hce, #Hopts⟩ HΦ
  ihave #Hrun := etcd_putRunOk p s E ρ γr cid mid n (txn.putOpOf key val (W64 0) false false false)
    $$ []
  · iframe #
  iapply (v3.kv.wp_Put api (etcdKVConn p s E ρ γr) ci cd key val sl []
    (putReplyOk E (txn.putOpOf key val (W64 0) false false false) cid mid)) $$ []
  · iframe #
    isplitl []
    · ipureintro
      refine ⟨?_, rfl⟩
      unfold opPutModel OpFull.putPanics opFold OpFull.putInit OpFull.newOp OpModel.zero
      simp
    · have Hw : putWireOf (opPutModel key val []) =
          txn.putOpOf key val (W64 0) false false false := rfl
      rw [Hw]; iexact Hrun
  inext
  iintro %resp %err #Hout
  iapply HΦ
  iunfold putCallOut at Hout
  icases Hout with (⟨%Herr, %m, #Hm, #Hq⟩ | %Herr)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m
    iframe #
  · iright
    ipureintro; exact ⟨Herr.1, Herr.2.2⟩

/-- **`client_get_end_to_end`** (see the file header): `kv.Get(ctx, key)` with no options on a
`*kv` over a connection to etcd's server, by a client that knows the committed index `c`
(`committedAtLeast γr c`; `0` is free): `nil` and the reply's message `m` with
`rangeReplyOk` for the get of `key` the server decodes (the key alone, at the latest revision,
linearizable: read after the read index, at a log extending the log applied through an index at
least `c`); or an error and no reply. -/
theorem client_get_end_to_end (api p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (c cid mid n : w64) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key : GoString) (sl : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗
        v3rpc.kvServerAt p s (v3rpc.srvKVAns s E ρ γr (W64 0)) cid mid n ∗
        kvObjAt api (etcdKVConn p s E ρ γr) ∗ context.isContext ci cd ∗ ctxErrClient ci cd ∗
        optsAt sl [] ∗ committedAtLeast γr c }}
      (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
          go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : RangeRespM, rangeRespMsg resp m ∗
            rangeReplyOk E γr c (txn.rangeOpOf key [] (W64 0) (W64 0) (W32 0) (W32 0) false false
              false (W64 0) (W64 0) (W64 0) (W64 0)) cid mid m) ∨
          ⌜err ≠ GoInterface.nil ∧ resp = null⌝ }} := by
  iintro %Φ ⟨#Pc, #Pv, #Ps, #Hsrv, #Hsrd, #Hat, #Hkv, #Hctx, #Hce, #Hopts, #Hc0⟩ HΦ
  ihave #Hrun := etcd_rangeRunOk p s E ρ γr c cid mid n (txn.rangeOpOf key [] (W64 0) (W64 0)
    (W32 0) (W32 0) false false false (W64 0) (W64 0) (W64 0) (W64 0)) $$ []
  · iframe #
  iapply (v3.kv.wp_Get api (etcdKVConn p s E ρ γr) ci cd key sl []
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
      rw [Hw]; iexact Hrun
  inext
  iintro %resp %err #Hout
  iapply HΦ
  iunfold rangeCallOut at Hout
  icases Hout with (⟨%Herr, %m, #Hm, #Hq⟩ | %Herr)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m
    iframe #
  · iright
    ipureintro; exact ⟨Herr.1, Herr.2.2⟩

end proofs

end client

#print axioms Perennial.EtcdGrove.client.client_put_end_to_end
#print axioms Perennial.EtcdGrove.client.client_get_end_to_end
#print axioms Perennial.EtcdGrove.client.etcd_putRunOk
#print axioms Perennial.EtcdGrove.client.etcd_rangeRunOk
#print axioms Perennial.EtcdGrove.client.v3.kv.wp_Put
#print axioms Perennial.EtcdGrove.client.v3.kv.wp_Get
#print axioms Perennial.EtcdGrove.client.v3.kv.wp_Do
#print axioms Perennial.EtcdGrove.client.v3.wp_NewKV
#print axioms Perennial.EtcdGrove.client.v3.wp_ContextError

end EtcdGrove
end Perennial
