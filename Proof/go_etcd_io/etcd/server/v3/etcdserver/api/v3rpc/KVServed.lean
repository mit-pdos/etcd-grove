/-
**etcd's server serves its KV methods** (`etcd_kv_served`; the server side of the gRPC
boundary, `grpc.serve`): etcd's specs of the KV methods (`InvKVService.lean`) met by its handlers
and registered at the server's address (`isGrpcRpc`), what the client's results
(`client/v3/Results.lean`: `etcd_put_served`, `client_put_etcd`, `client_put_end_to_end`, ...)
take. Moved here from `client/v3/Results.lean` (2026-10-15). Lean-first (no Rocq counterpart).

**The handlers** (`etcd_putHandlerOk`, `etcd_rangeHandlerOk`, `etcd_deleteHandlerOk`,
`etcd_txnHandlerOk`: `grpcHandlerOk`): `kvServer.Put`/`Range`/`DeleteRange`/`Txn` at the
server's `*kvServer` `p` (`v3rpc/Results.lean`: `put_end_to_end`, ...), with the per-run slot
`etcdRunSlot` (the reader slots of `s.leadTimeMu`, the store, the logger and the read loop: every
run gives them back) and the context the runtime made; the id credit a run takes is minted from
the server's id budget `□ |==> idCred ρ.ids 1` (`srvStarted`'s, the server's own idealization:
the generator's `2 ^ 48 - 1` ids are assumed not to wrap).

**As grpc runs them** (unit P3b; `etcd_putMethodOk`, ...: `grpcMethodOk`): the generated
`_KV_Put_Handler` (`_KV_Range_Handler`, `_KV_DeleteRange_Handler`, `_KV_Txn_Handler`, proved) on
the `*quotaKVServer` `q` that `RegisterKVServer` is given (`NewQuotaKVServer(s)`: its `Put` and
`Txn` check the quota first, `quotaKVServer.Put`/`Txn` proved; its `Range`/`DeleteRange` are
`p`'s, promoted), under the server's chain of transparent interceptors (`srvInterceptorsOk`:
`newLogUnaryInterceptor`'s and `newUnaryInterceptor`'s, proved; grpc-prometheus's, assumed); a
run's slot as the runtime holds it is `etcdGrpcSlot` (`etcdRunSlot`, a reader slot of
`leadTimeMu` for the quota's alarm, the log interceptor's of `lgMu`).

**`etcd_kv_served`**: the gRPC server at `addr` built with etcd's chain of interceptors and the KV
service registered on the quota wrapper (`grpcServerAt`), that hands the runtime `N` run slots,
registers etcd's four specs at `addr` (`isGrpcRpc`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvKVService
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.QuotaLemmas

@[expose] public section

set_option pp.fullNames true
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

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
    (c c' cid mid n : w64) (F F' : mvcc.Log) (d d' : v3rpc.KVDep GF) :
    v3rpc.kvServerAt (GF := GF) p s (v3rpc.srvKVAns s E ρ γr c F d) cid mid n =
      v3rpc.kvServerAt p s (v3rpc.srvKVAns s E ρ γr c' F' d') cid mid n := rfl

open Iris.ProofMode in
/-- **A range's deposit's result at the log read** (2026-10-14, unit T1): the server's answer's
(`rangeAnsOk`'s, at a committed raft log whose model is the log read) as the client's `□ Q` of the
state of the log read (2026-10-15, unit T2), for no deposit (`Q` trivial) or the client's read. -/
theorem rangeQ_of_ans (γr : ReadNames) (d : v3rpc.KVDep GF) (Q : KVState → IProp GF)
    (o : OpFull) (log : mvcc.Log)
    (h : (d = .none ∧ Q = fun _ => iprop(True)) ∨ d = .read Q) :
    (if o.base.serializable then iprop(True) else
      ∃ L : List EntryModel, srvRLogLb γr.raft L ∗ ⌜kvModel γr.kv L = log⌝ ∗
        □ v3rpc.rangeDepQ γr.kv d L : IProp GF) ⊢
      (if o.base.serializable then iprop(True) else □ Q (kvStateOf log)) := by
  cases hs : o.base.serializable
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iintro ⟨%L, -, %HL, #HQ⟩
    rcases h with ⟨rfl, rfl⟩ | rfl
    · iintro !>; itrivial
    · simp only [v3rpc.rangeDepQ]
      rw [← HL]
      iintro !>
      iexact HQ
  · simp only [↓reduceIte]; iintro -; itrivial

/-- A run's call resources give back its slot (the committed index dropped). -/
theorem etcdRunSlot_back (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (c : w64) :
    srvLeadTimeReader (GF := GF) s ∗ srvRdCall s E γr c ⊢ etcdRunSlot s E γr := by
  iintro ⟨Hlt, Hrd⟩
  unfold srvRdCall etcdRunSlot
  icases Hrd with ⟨Hsr, Hlg, -, Hrr, Hard⟩
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
message, with `putReplied` (`putReplyOk` and the revision's token). -/
theorem etcd_putHandlerOk (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (cid mid n : w64) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗
        v3rpc.kvServerAt p s (v3rpc.srvKVAns s E ρ γr (W64 0) [] .none) cid mid n ∗
        □ (|==> idCred ρ.ids 1) ⊢
      grpcHandlerOk (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!!
      go!"Put") (etcdRunSlot s E γr) (etcdPutSpec E ρ.rd cid mid) := by
  iintro ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hat, #HNR⟩
  unfold grpcHandlerOk
  iintro %o %Φ %ci %cd %r !> %Ψ ⟨Hslot, #Hctx, #Hrc, #Hr, Hspec⟩ HΨ
  ihave #Htr := ctxTraceIs_none_of_runCtx ci $$ Hrc
  rw [show (pbPutRequest (GF := GF)).recv r o = txn.putRequestIs r o from rfl]
  iunfold etcdPutSpec at Hspec
  icases Hspec with ⟨%F, #HF, Hspec⟩
  ihave ⟨%d, Hdep, %Hdp, Hk⟩ : iprop(∃ d : v3rpc.KVDep GF, v3rpc.kvDepOwn ρ γr d ∗
      ⌜v3rpc.kvDepPre d (.put o)⌝ ∗
      ∀ m : PutRespM, putReplied E ρ.rd F o cid mid m ∗ (∃ σ, □ v3rpc.opDepQ d σ) -∗ Φ m)
      $$ [Hspec]
  · icases Hspec with ⟨%Q, %Hpl, #Hau, Hk⟩
    iexists (.op (.put o) Q)
    rw [show v3rpc.kvDepOwn (GF := GF) ρ γr (.op (.put o) Q) = kvOpAu ρ.kv (.put o) Q from rfl]
    isplitr
    · iexact Hau
    isplitr
    · ipureintro; exact ⟨⟨Q, rfl⟩, Hpl⟩
    iintro %m ⟨Hm, Hq⟩
    iapply Hk
    iframe Hm
    simp only [v3rpc.opDepQ]; iexact Hq
  rw [kvServerAt_srvKVAns p s E ρ γr (W64 0) (W64 0) cid mid n [] F .none d]
  iunfold etcdRunSlot at Hslot
  icases Hslot with ⟨Hlt, Hsr, Hlg, Hrd, Hard⟩
  ihave Hu := HNR
  imod Hu with Hid
  imod (monoNatLbOwn_0 (GF := GF) γr.committed) with #H0
  iapply wp_fupd
  iapply (v3rpc.put_end_to_end p s E ρ γr (W64 0) cid mid n (GoInterface.ok ci) r o F d) $$
    [Hlt Hsr Hlg Hrd Hard Hid Hdep]
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
    ipureintro; exact Hdp
  inext
  iintro %resp %err Hpost
  cases hc : v3rpc.putCheck o with
  | some e =>
    icases Hpost with ⟨#Hco, Hc, Hc0, -⟩
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
    icases Hpost with (⟨%Herr, %h, %rv, %rv', #Hh, Hf, -, Hc0, Hap, #HQv⟩ | ⟨%Herr, %e, Hc0, Hep⟩)
    · obtain ⟨rfl, Hrn⟩ := Herr
      iunfold v3rpc.putAppliedOk at Hap
      icases Hap with ⟨Hlt, Hap⟩
      iunfold v3rpc.putApplied at Hap
      -- the revision's token (`revMinted`, exclusive) goes to the reply's `Φ` (`putReplied`),
      -- with the witness (`appliedWit`, persistent)
      icases Hap with ⟨%hm, %x, %x', %l, %skip, %Hst, Hout, #Hcert, Htok, #Hwit⟩
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
      · iapply Hk
        isplitl [Htok]
        · unfold putReplied
          iexists hm, x, x', l, skip
          iframe Htok
          iframe #
          ipureintro
          exact ⟨Hst.1, rfl, rfl, rfl, rfl, Hst.2.2⟩
        iexact HQv
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
        v3rpc.kvServerAt p s (v3rpc.srvKVAns s E ρ γr (W64 0) [] .none) cid mid n ∗
        □ (|==> idCred ρ.ids 1) ⊢
      grpcHandlerOk (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!!
      go!"Range") (etcdRunSlot s E γr) (etcdRangeSpec E γr cid mid) := by
  iintro ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hat, #HNR⟩
  unfold grpcHandlerOk
  iintro %o %Φ %ci %cd %r !> %Ψ ⟨Hslot, #Hctx, #Hrc, #Hr, Hspec⟩ HΨ
  ihave #Htr := ctxTraceIs_none_of_runCtx ci $$ Hrc
  rw [show (pbRangeRequest (GF := GF)).recv r o = txn.rangeRequestIs r o from rfl]
  iunfold etcdRangeSpec at Hspec
  icases Hspec with ⟨%c, %F, %Q, #Hc0, #HF, Hdq, Hk⟩
  ihave ⟨%d, Hdep, %Hdp, %Hdd⟩ : iprop(∃ d : v3rpc.KVDep GF, v3rpc.kvDepOwn ρ γr d ∗
      ⌜v3rpc.kvDepPre d (.range o)⌝ ∗
      ⌜(d = .none ∧ Q = fun _ => iprop(True)) ∨ d = .read Q⌝) $$ [Hdq]
  · icases Hdq with (%HQ | ⟨%Hser, #Hau⟩)
    · iexists .none
      rw [show v3rpc.kvDepOwn (GF := GF) ρ γr .none = iprop(True) from rfl]
      isplitr
      · itrivial
      ipureintro
      exact ⟨(fun Q' h => by cases h), Or.inl ⟨rfl, HQ⟩⟩
    · iexists (.read Q)
      rw [show v3rpc.kvDepOwn (GF := GF) ρ γr (.read Q) = kvReadAu γr.kv Q from rfl]
      iframe Hau
      ipureintro
      exact ⟨(fun Q' h => by cases h; exact Hser), Or.inr rfl⟩
  rw [kvServerAt_srvKVAns p s E ρ γr (W64 0) c cid mid n [] F .none d]
  iunfold etcdRunSlot at Hslot
  icases Hslot with ⟨Hlt, Hsr, Hlg, Hrd, Hard⟩
  ihave Hu := HNR
  imod Hu with Hid
  iapply wp_fupd
  iapply (v3rpc.range_end_to_end p s E ρ γr c cid mid n (GoInterface.ok ci) r o F d) $$
    [Hlt Hsr Hlg Hrd Hard Hid Hdep]
  · iframe #
    unfold v3rpc.srvCall srvRdCall
    isplitl [Hlt Hid]
    · iexists ci, cd
      iframe
      iframe #
      ipureintro; rfl
    iframe
    iframe Hc0
    ipureintro; exact Hdp
  inext
  iintro %resp %err Hpost
  cases hc : v3rpc.rangeCheck o with
  | some e =>
    icases Hpost with ⟨#Hco, Hc, Hcr, -⟩
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
      icases Hans with ⟨%log, #Hcert, %Hlog, #Hrl, HQl, Hres⟩
      ihave #HQl' := rangeQ_of_ans γr d Q o log Hdd $$ HQl
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
      · iapply Hk
        unfold rangeReplyOk
        iexists log
        iframe #
        ipureintro
        exact ⟨Hlog.1, Hlog.2.1, rfl, rfl, rfl, Hx.1, rfl, Hsel, Hlog.2.2.2⟩
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
        v3rpc.kvServerAt p s (v3rpc.srvKVAns s E ρ γr (W64 0) [] .none) cid mid n ∗
        □ (|==> idCred ρ.ids 1) ⊢
      grpcHandlerOk
        (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!!
          go!"DeleteRange")
        (etcdRunSlot s E γr) (etcdDeleteSpec E ρ.rd cid mid) := by
  iintro ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hat, #HNR⟩
  unfold grpcHandlerOk
  iintro %o %Φ %ci %cd %r !> %Ψ ⟨Hslot, #Hctx, #Hrc, #Hr, Hspec⟩ HΨ
  ihave #Htr := ctxTraceIs_none_of_runCtx ci $$ Hrc
  rw [show (pbDeleteRangeRequest (GF := GF)).recv r o = txn.deleteRangeRequestIs r o from rfl]
  iunfold etcdDeleteSpec at Hspec
  icases Hspec with ⟨%F, #HF, %Q, %Hz, #Hau, Hk⟩
  rw [kvServerAt_srvKVAns p s E ρ γr (W64 0) (W64 0) cid mid n [] F .none
    (.op (.deleteRange o) Q)]
  iunfold etcdRunSlot at Hslot
  icases Hslot with ⟨Hlt, Hsr, Hlg, Hrd, Hard⟩
  ihave Hu := HNR
  imod Hu with Hid
  imod (monoNatLbOwn_0 (GF := GF) γr.committed) with #H0
  iapply wp_fupd
  iapply (v3rpc.deleteRange_end_to_end p s E ρ γr (W64 0) cid mid n (GoInterface.ok ci) r o F
      (.op (.deleteRange o) Q)) $$ [Hlt Hsr Hlg Hrd Hard Hid]
  · rw [show v3rpc.kvDepOwn (GF := GF) ρ γr (.op (.deleteRange o) Q) = kvOpAu ρ.kv (.deleteRange o) Q from rfl]
    iframe #
    unfold v3rpc.srvCall srvRdCall committedAtLeast
    isplitl [Hlt Hid]
    · iexists ci, cd
      iframe
      iframe #
      ipureintro; rfl
    iframe
    rw [show uint.nat (W64 0) = 0 from rfl]
    iframe H0
    ipureintro; exact ⟨⟨Q, rfl⟩, Hz⟩
  inext
  iintro %resp %err Hpost
  cases hc : v3rpc.deleteCheck o with
  | some e =>
    icases Hpost with ⟨#Hco, Hc, Hc0, -⟩
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
    icases Hpost with (⟨%Herr, %h, %rv, %rv', #Hh, Hf, -, Hc0, Hap, #HQv⟩ | ⟨%Herr, %e, Hc0, Hep⟩)
    · obtain ⟨rfl, Hrn⟩ := Herr
      iunfold v3rpc.deleteAppliedOk at Hap
      icases Hap with ⟨Hlt, Hap⟩
      iunfold v3rpc.deleteApplied at Hap
      -- the revision's token (`revMinted`) goes to the reply's `Φ` (`deleteReplied`)
      icases Hap with ⟨%hm, %rq', %op', %x, %x', %l, %skip, %Hst, Hout, #Hcert, Htok, #Hwit⟩
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
      · iapply Hk
        isplitl [Htok]
        · unfold deleteReplied
          iexists hm, rq', op', x, x', l, skip
          iframe Htok
          iframe #
          ipureintro
          exact ⟨Hst.1, Hst.2.1, Hst.2.2.1, Hst.2.2.2.1, rfl, rfl, rfl, rfl, rfl, Hst.2.2.2.2.2⟩
        simp only [v3rpc.opDepQ] at *
        iexact HQv
    · iunfold v3rpc.deleteErrOk at Hep
      icases Hep with ⟨Hlt, -⟩
      imodintro
      iapply HΨ
      isplitl [Hlt Hc0]
      · iapply etcdRunSlot_back s E γr (W64 0)
        iframe
      iintro %Hnil
      exact absurd Hnil Herr.2

/-- **etcd's `Txn` handler meets etcd's `Txn` spec** (`grpcHandlerOk`; from `txn_end_to_end`; the
vertical slice's unit V2): as `etcd_rangeHandlerOk`, for a transaction of plain operations within
the txn package's model (`etcdTxnSpec`'s premises), the reply with `txnReplied` at the committed
index the caller knew of and its floor. -/
theorem etcd_txnHandlerOk (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (cid mid n : w64) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗
        v3rpc.kvServerAt p s (v3rpc.srvKVAns s E ρ γr (W64 0) [] .none) cid mid n ∗
        □ (|==> idCred ρ.ids 1) ⊢
      grpcHandlerOk (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!!
      go!"Txn") (etcdRunSlot s E γr) (etcdTxnSpec E ρ.rd γr cid mid) := by
  iintro ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hat, #HNR⟩
  unfold grpcHandlerOk
  iintro %t %Φ %ci %cd %r !> %Ψ ⟨Hslot, #Hctx, #Hrc, #Hr, Hspec⟩ HΨ
  ihave #Htr := ctxTraceIs_none_of_runCtx ci $$ Hrc
  rw [show (pbTxnRequest (GF := GF)).recv r t = iprop(txn.txnRequestIs r t ∗ txnWireOk r t)
    from rfl]
  iunfold etcdTxnSpec at Hspec
  icases Hspec with ⟨%Hpl, %Q, Hnp, %c, %F, #Hc0, #HF, Hspec⟩
  obtain ⟨hp, hin⟩ := Hpl
  icases Hr with ⟨#Hreq, #Hw⟩
  ihave ⟨%ts, %es, #Htq, #Htw, %Hmod⟩ := txnReq_of_requestIs r t hp $$ [$Hreq $Hw]
  -- the deposit (unit T2): none for a read-only transaction, else the client's update
  ihave ⟨%d, Hdep, %Hdp, %HdQ⟩ : iprop(∃ d : v3rpc.KVDep GF, v3rpc.kvDepOwn ρ γr d ∗
      ⌜v3rpc.kvDepPre d (.txn t.cmps ts es)⌝ ∗
      ⌜(txn.txnReadonly t = true ∧ Q = fun _ => iprop(True)) ∨
        (txn.txnReadonly t = false ∧ d = .op (.txn t) Q)⌝) $$ [Hnp]
  · icases Hnp with (%Hro | ⟨%Hw, #Hau⟩)
    · iexists .none
      rw [show v3rpc.kvDepOwn (GF := GF) ρ γr .none = iprop(True) from rfl]
      isplitr
      · itrivial
      ipureintro
      refine ⟨?_, Or.inl Hro⟩
      intro t' ht'
      rw [Hmod] at ht'
      cases ht'
      left; exact Hro.1
    · iexists (.op (.txn t) Q)
      rw [show v3rpc.kvDepOwn (GF := GF) ρ γr (.op (.txn t) Q) = kvOpAu ρ.kv (.txn t) Q from rfl]
      iframe Hau
      ipureintro
      refine ⟨?_, Or.inr ⟨Hw.1, rfl⟩⟩
      intro t' ht'
      rw [Hmod] at ht'
      cases ht'
      right; exact ⟨⟨Q, rfl⟩, Hw.2⟩
  rw [kvServerAt_srvKVAns p s E ρ γr (W64 0) c cid mid n [] F .none d]
  iunfold etcdRunSlot at Hslot
  icases Hslot with ⟨Hlt, Hsr, Hlg, Hrd⟩
  ihave Hu := HNR
  imod Hu with Hid
  iapply wp_fupd
  iapply (v3rpc.txn_end_to_end p s E ρ γr c cid mid n (GoInterface.ok ci) r t.cmps ts es F d) $$
    [Hlt Hsr Hlg Hrd Hid Hdep]
  · iframe #
    unfold v3rpc.srvCall srvRdCall
    isplitl [Hlt Hid]
    · iexists ci, cd
      iframe
      iframe #
      ipureintro; rfl
    iframe
    iframe Hc0
    isplitr
    · ipureintro; exact txnInModel_of t _ _ _ hin Hmod
    ipureintro; exact Hdp
  inext
  iintro %resp %err Hpost
  cases hc : v3rpc.txnAllCheck (sint.Z n) t.cmps ts es with
  | some e =>
    simp only [hc]
    icases Hpost with ⟨#Hco, Hc, Hcr, -⟩
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
    simp only [hc]
    icases Hpost with (⟨%Herr, %h, %rv, %rv', #Hh, Hf, -, Hcr, Hlt, %t', %Ht', Hans⟩ |
      ⟨%Herr, %e, Hcr, Hlt, -⟩)
    · rw [Hmod] at Ht'
      cases Ht'
      obtain ⟨rfl, Hrn⟩ := Herr
      cases hro : txn.txnReadonly t with
      | true =>
        simp only [hro, ↓reduceIte]
        icases Hans with ⟨-, Hans⟩
        iunfold v3rpc.txnReadAns at Hans
        icases Hans with ⟨%log, #Hcert, %Hlog, #Hrl, Hres⟩
        imod (txnRespMsg_of_server false resp h _ t _ _ cid mid) $$ [$Hh $Hf $Hres]
          with ⟨%m, #Hm, %Hmm⟩
        imodintro
        iapply HΨ
        isplitl [Hlt Hcr]
        · iapply etcdRunSlot_back s E γr c
          iframe
        iintro -
        iexists m
        isplitl []
        · simp only [pbTxnResponse]; iexact Hm
        iapply Hspec
        isplitl
        rotate_left
        · rcases HdQ with ⟨-, rfl⟩ | ⟨h, -⟩
          · iexists ⟨[], 0⟩; iintro !>; itrivial
          · rw [hro] at h; cases h
        unfold txnReplied
        simp only [hro, ↓reduceIte]
        iexists log
        iframe #
        ipureintro
        obtain ⟨h1, h2, h3, h4, h5⟩ := Hmm
        refine ⟨Hlog.1, Hlog.2.1, Hlog.2.2.2, ?_, h2, h3, h4, ?_⟩
        · rw [h1]
        · rw [h4]; exact h5
      | false =>
        simp only [hro, Bool.false_eq_true, ↓reduceIte]
        icases Hans with ⟨Hans, #HQv⟩
        iunfold v3rpc.txnAppliedAns at Hans
        icases Hans with ⟨%hm, %rq', %t'', %x, %x', %l, %skip, %Hst, Hout, #Hcert, HMint, #Hwit⟩
        iunfold apply.txnOutcomeIs at Hout
        icases Hout with ⟨#Hres, -⟩
        imod (txnRespMsg_of_server skip resp h _ t'' _ _ cid mid) $$ [$Hh $Hf $Hres]
          with ⟨%m, #Hm, %Hmm⟩
        imodintro
        iapply HΨ
        isplitl [Hlt Hcr]
        · iapply etcdRunSlot_back s E γr c
          iframe
        iintro -
        iexists m
        isplitl []
        · simp only [pbTxnResponse]; iexact Hm
        iapply Hspec
        isplitl
        rotate_left
        · rcases HdQ with ⟨h, -⟩ | ⟨-, rfl⟩
          · rw [hro] at h; cases h
          · simp only [v3rpc.opDepQ] at *; iexact HQv
        unfold txnReplied
        simp only [hro, Bool.false_eq_true, ↓reduceIte]
        iexists hm, rq', t'', x, x', l, skip
        iframe Hcert HMint Hwit
        ipureintro
        obtain ⟨h1, h2, h3, h4, h5⟩ := Hmm
        obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ := Hst
        refine ⟨s1, s2, s3, s4, ?_, h2, h3, s6, s7, s8, h4, ?_⟩
        · rw [h1]
        · rw [h4]; exact h5
    · obtain ⟨-, Hne⟩ := Herr
      imodintro
      iapply HΨ
      isplitl [Hlt Hcr]
      · iapply etcdRunSlot_back s E γr c
        iframe
      iintro %Hnil
      exact absurd Hnil Hne

/-- A put or delete request at a pointer: the learner check reads nothing of it. -/
theorem putReq_learnerOk (l : Loc) :
    ⊢ v3rpc.learnerReqOk (GF := GF)
      (interface.mkOk (go.GoType.PointerType etcdserverpb.PutRequest.ty) #l) :=
  v3rpc.learnerReqOk_ptr _ l (by
    simp [etcdserverpb.PutRequest.ty, etcdserverpb.RangeRequest.ty])

theorem deleteReq_learnerOk (l : Loc) :
    ⊢ v3rpc.learnerReqOk (GF := GF)
      (interface.mkOk (go.GoType.PointerType etcdserverpb.DeleteRangeRequest.ty) #l) :=
  v3rpc.learnerReqOk_ptr _ l (by
    simp [etcdserverpb.DeleteRangeRequest.ty, etcdserverpb.RangeRequest.ty])

/-- **etcd's `Put`, as grpc runs it** (`grpcMethodOk`): the generated `_KV_Put_Handler` on the
`*quotaKVServer` `q` whose `Put` meets etcd's spec, under a chain of transparent interceptors
(for requests the learner check reads); the run's resource is the method's and the
interceptors'. -/
theorem etcd_putMethodOk [v3rpc.QuotaKVServerIsKVServer] (q : Loc) (E : apply.AEnv GF)
    (γr : ReadNames) (cid mid : w64) (S : IProp GF) (ics : List GoFunc) (Rs : List (IProp GF)) :
    grpcHandlerOk (q @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty @!! go!"Put")
        S (etcdPutSpec E γr cid mid) ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
        srvInterceptorsOk v3rpc.learnerReqOk ics Rs ⊢
      grpcMethodOk (@! etcdserverpb._KV_Put_Handler)
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q)
        ics iprop(S ∗ [∗list] R ∈ Rs, R) (etcdPutSpec E γr cid mid) := by
  iintro ⟨#Hh, #Ppb, #Hics⟩
  unfold grpcMethodOk
  iintro %m %Φ %ci %cd %dec %ui !> %Ψ ⟨⟨HS, HRs⟩, #Hctx, #Hrc, #Hdec, #Hch, HSpec⟩ HΨ
  ihave #Hbl : iprop(□ ∀ l : Loc, l ↦ (zero_val etcdserverpb.PutRequest) -∗
      (pbPutRequest (GF := GF)).blank l) $$ []
  · iintro !> %l Hl; simp only [pbPutRequest]; iexact Hl
  ihave #HQr : iprop(□ ∀ l : Loc, (pbPutRequest (GF := GF)).recv l m -∗
      v3rpc.learnerReqOk (interface.mkOk (go.GoType.PointerType etcdserverpb.PutRequest.ty) #l)) $$ []
  · iintro !> %l -
    iapply putReq_learnerOk
  iapply (v3rpc.etcdserverpb.wp__KV_Put_Handler pbPutRequest pbPutResponse (etcdPutSpec E γr cid mid)
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty, #q⟩
    S ics Rs v3rpc.learnerReqOk m Φ ci cd dec ui rfl rfl v3rpc.QuotaKVServerIsKVServer.is_kv)
    $$ [HS HRs HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, HRs, Hres⟩
  iapply HΨ
  iframe

/-- **etcd's `Range`, as grpc runs it** (as `etcd_putMethodOk`). -/
theorem etcd_rangeMethodOk [v3rpc.QuotaKVServerIsKVServer] (q : Loc) (E : apply.AEnv GF)
    (γr : ReadNames) (cid mid : w64) (S : IProp GF) (ics : List GoFunc) (Rs : List (IProp GF)) :
    grpcHandlerOk (q @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty @!! go!"Range")
        S (etcdRangeSpec E γr cid mid) ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ srvInterceptorsOk v3rpc.learnerReqOk ics Rs ⊢
      grpcMethodOk (@! etcdserverpb._KV_Range_Handler)
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q)
        ics iprop(S ∗ [∗list] R ∈ Rs, R) (etcdRangeSpec E γr cid mid) := by
  iintro ⟨#Hh, #Ppb, #Hics⟩
  unfold grpcMethodOk
  iintro %m %Φ %ci %cd %dec %ui !> %Ψ ⟨⟨HS, HRs⟩, #Hctx, #Hrc, #Hdec, #Hch, HSpec⟩ HΨ
  ihave #Hbl : iprop(□ ∀ l : Loc, l ↦ (zero_val etcdserverpb.RangeRequest) -∗
      (pbRangeRequest (GF := GF)).blank l) $$ []
  · iintro !> %l Hl; simp only [pbRangeRequest]; iexact Hl
  ihave #HQr : iprop(□ ∀ l : Loc, (pbRangeRequest (GF := GF)).recv l m -∗
      v3rpc.learnerReqOk (interface.mkOk (go.GoType.PointerType etcdserverpb.RangeRequest.ty) #l)) $$ []
  · iintro !> %l #Hr
    rw [show (pbRangeRequest (GF := GF)).recv l m = txn.rangeRequestIs l m from rfl]
    iapply (v3rpc.learnerReqOk_range l m)
    iexact Hr
  iapply (v3rpc.etcdserverpb.wp__KV_Range_Handler pbRangeRequest pbRangeResponse
    (etcdRangeSpec E γr cid mid)
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty, #q⟩
    S ics Rs v3rpc.learnerReqOk m Φ ci cd dec ui rfl rfl v3rpc.QuotaKVServerIsKVServer.is_kv)
    $$ [HS HRs HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, HRs, Hres⟩
  iapply HΨ
  iframe

/-- **etcd's `DeleteRange`, as grpc runs it** (as `etcd_putMethodOk`). -/
theorem etcd_deleteMethodOk [v3rpc.QuotaKVServerIsKVServer] (q : Loc) (E : apply.AEnv GF)
    (γr : ReadNames) (cid mid : w64) (S : IProp GF) (ics : List GoFunc) (Rs : List (IProp GF)) :
    grpcHandlerOk (q @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty @!! go!"DeleteRange")
        S (etcdDeleteSpec E γr cid mid) ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ srvInterceptorsOk v3rpc.learnerReqOk ics Rs ⊢
      grpcMethodOk (@! etcdserverpb._KV_DeleteRange_Handler)
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q)
        ics iprop(S ∗ [∗list] R ∈ Rs, R) (etcdDeleteSpec E γr cid mid) := by
  iintro ⟨#Hh, #Ppb, #Hics⟩
  unfold grpcMethodOk
  iintro %m %Φ %ci %cd %dec %ui !> %Ψ ⟨⟨HS, HRs⟩, #Hctx, #Hrc, #Hdec, #Hch, HSpec⟩ HΨ
  ihave #Hbl : iprop(□ ∀ l : Loc, l ↦ (zero_val etcdserverpb.DeleteRangeRequest) -∗
      (pbDeleteRangeRequest (GF := GF)).blank l) $$ []
  · iintro !> %l Hl; simp only [pbDeleteRangeRequest]; iexact Hl
  ihave #HQr : iprop(□ ∀ l : Loc, (pbDeleteRangeRequest (GF := GF)).recv l m -∗
      v3rpc.learnerReqOk (interface.mkOk (go.GoType.PointerType etcdserverpb.DeleteRangeRequest.ty) #l)) $$ []
  · iintro !> %l -
    iapply deleteReq_learnerOk
  iapply (v3rpc.etcdserverpb.wp__KV_DeleteRange_Handler pbDeleteRangeRequest pbDeleteRangeResponse
    (etcdDeleteSpec E γr cid mid)
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty, #q⟩
    S ics Rs v3rpc.learnerReqOk m Φ ci cd dec ui rfl rfl v3rpc.QuotaKVServerIsKVServer.is_kv)
    $$ [HS HRs HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, HRs, Hres⟩
  iapply HΨ
  iframe

theorem txnReq_learnerOk (l : Loc) :
    ⊢ v3rpc.learnerReqOk (GF := GF)
      (interface.mkOk (go.GoType.PointerType etcdserverpb.TxnRequest.ty) #l) :=
  v3rpc.learnerReqOk_ptr _ l (by
    simp [etcdserverpb.TxnRequest.ty, etcdserverpb.RangeRequest.ty])

/-- **etcd's `Txn`, as grpc runs it** (as `etcd_putMethodOk`; the vertical slice's unit V2). -/
theorem etcd_txnMethodOk [v3rpc.QuotaKVServerIsKVServer] (q : Loc) (E : apply.AEnv GF)
    (γw γr : ReadNames) (cid mid : w64) (S : IProp GF) (ics : List GoFunc) (Rs : List (IProp GF)) :
    grpcHandlerOk (q @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty @!! go!"Txn")
        S (etcdTxnSpec E γw γr cid mid) ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ srvInterceptorsOk v3rpc.learnerReqOk ics Rs ⊢
      grpcMethodOk (@! etcdserverpb._KV_Txn_Handler)
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q)
        ics iprop(S ∗ [∗list] R ∈ Rs, R) (etcdTxnSpec E γw γr cid mid) := by
  iintro ⟨#Hh, #Ppb, #Hics⟩
  unfold grpcMethodOk
  iintro %m %Φ %ci %cd %dec %ui !> %Ψ ⟨⟨HS, HRs⟩, #Hctx, #Hrc, #Hdec, #Hch, HSpec⟩ HΨ
  ihave #Hbl : iprop(□ ∀ l : Loc, l ↦ (zero_val etcdserverpb.TxnRequest) -∗
      (pbTxnRequest (GF := GF)).blank l) $$ []
  · iintro !> %l Hl; simp only [pbTxnRequest]; iexact Hl
  ihave #HQr : iprop(□ ∀ l : Loc, (pbTxnRequest (GF := GF)).recv l m -∗
      v3rpc.learnerReqOk (interface.mkOk (go.GoType.PointerType etcdserverpb.TxnRequest.ty) #l)) $$ []
  · iintro !> %l -
    iapply txnReq_learnerOk
  iapply (v3rpc.etcdserverpb.wp__KV_Txn_Handler pbTxnRequest pbTxnResponse (etcdTxnSpec E γw γr cid mid)
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty, #q⟩
    S ics Rs v3rpc.learnerReqOk m Φ ci cd dec ui rfl rfl v3rpc.QuotaKVServerIsKVServer.is_kv)
    $$ [HS HRs HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, HRs, Hres⟩
  iapply HΨ
  iframe

/-- **etcd's server serves its KV methods** (the server side, `grpc_serve_rpcs`; unit P3b: as grpc
runs them): the gRPC server at `addr` built with the chain `[il, im, iu]` (`v3rpc.Server`'s:
`newLogUnaryInterceptor(s)`'s, grpc-prometheus's, `newUnaryInterceptor(s)`'s) with the KV
service registered on the `*quotaKVServer` `q` (`RegisterKVServer(gs, NewQuotaKVServer(s))`:
`etcdKVRegs q` among the registered methods), that hands the runtime `N` run slots
(`etcdGrpcSlot`), registers etcd's `Put`, `Range` and `DeleteRange` specs at `addr` (`isGrpcRpc`).
Premises: the server's (`isServerReq`, `isServerRead`, its `*kvServer` `p`, the id budget
`□ |==> idCred ρ.ids 1` of `srvStarted`), the quota wrapper over `p` (`quotaKVServerAt`: what
`NewQuotaKVServer(s)` returns), the interceptors' contracts (`srvInterceptorOk`: what
`newLogUnaryInterceptor(s)` and `newUnaryInterceptor(s)` return, proved; grpc-prometheus's,
assumed), the method-set fact `QuotaKVServerIsKVServer`, the packages'. -/
theorem etcd_kv_served [v3rpc.QuotaKVServerIsKVServer] (addr : GoString) (p q s : Loc)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (cid mid n : w64) (il im iu : GoFunc)
    (regs : List (GoString × val × GoInterface)) (N : Nat)
    (hregs : ∀ x ∈ etcdKVRegs (GF := GF) q, x ∈ regs) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗
        v3rpc.kvServerAt p s (v3rpc.srvKVAns s E ρ γr (W64 0) [] .none) cid mid n ∗
        □ (|==> idCred ρ.ids 1) ∗
        v3rpc.quotaKVServerAt q
          ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩ s ∗
        srvInterceptorOk il (srvLgReader s) v3rpc.learnerReqOk ∗
        srvInterceptorOk im iprop(True) v3rpc.learnerReqOk ∗
        srvInterceptorOk iu iprop(True) v3rpc.learnerReqOk ∗
        grpcServerAt addr [il, im, iu] regs ∗
        ([∗list] _x ∈ List.replicate N (), etcdGrpcSlot s E γr) ⊢
      |={⊤}=> isGrpcRpc addr go!"/etcdserverpb.KV/Put" (etcdPutSpec E ρ.rd cid mid) ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/Range" (etcdRangeSpec E γr cid mid) ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/DeleteRange" (etcdDeleteSpec E ρ.rd cid mid) ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/Txn" (etcdTxnSpec E ρ.rd γr cid mid) := by
  iintro ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hat, #HNR, #Hq, #Hil, #Him, #Hiu, Hl, Hslots⟩
  ihave #Hp := etcd_putHandlerOk p s E ρ γr cid mid n $$ []
  · iframe #
  ihave #Hr := etcd_rangeHandlerOk p s E ρ γr cid mid n $$ []
  · iframe #
  ihave #Hd := etcd_deleteHandlerOk p s E ρ γr cid mid n $$ []
  · iframe #
  ihave #Ht := etcd_txnHandlerOk p s E ρ γr cid mid n $$ []
  · iframe #
  ihave #Hqt := v3rpc.quotaKV_txnHandlerOk_of v3rpc.quotaKVServer.wp_Txn (etcdTxnSpec E ρ.rd γr cid mid) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩ E ρ
    (etcdRunSlot s E γr) $$ []
  · iframe #
  ihave #Hqp := v3rpc.quotaKV_putHandlerOk_of v3rpc.quotaKVServer.wp_Put (etcdPutSpec E ρ.rd cid mid) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩ E ρ
    (etcdRunSlot s E γr) $$ []
  · iframe #
  ihave #Hr' := grpcHandlerOk_frame _ _ iprop(srvLeadTimeReader s ∗ E.RD) (etcdRangeSpec E γr cid mid) $$ Hr
  ihave #Hd' := grpcHandlerOk_frame _ _ iprop(srvLeadTimeReader s ∗ E.RD) (etcdDeleteSpec E ρ.rd cid mid) $$ Hd
  ihave #Hqr := v3rpc.quotaKV_promotedHandlerOk (etcdRangeSpec E γr cid mid) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩
    iprop(etcdRunSlot s E γr ∗ srvLeadTimeReader s ∗ E.RD) go!"Range" inferInstance $$ [Hq Hr']
  · iframe #
  ihave #Hqd := v3rpc.quotaKV_promotedHandlerOk (etcdDeleteSpec E ρ.rd cid mid) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩
    iprop(etcdRunSlot s E γr ∗ srvLeadTimeReader s ∗ E.RD) go!"DeleteRange" inferInstance $$ [Hq Hd']
  · iframe #
  ihave #Hics : srvInterceptorsOk (GF := GF) v3rpc.learnerReqOk [il, im, iu] (etcdIcRs s) $$ []
  · unfold etcdIcRs srvInterceptorsOk srvInterceptorsOk srvInterceptorsOk srvInterceptorsOk
    iframe #
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  ihave #Hmp := etcd_putMethodOk q E ρ.rd cid mid _ _ _ $$ [Hqp Ppb Hics]
  · iframe #
  ihave #Hmr := etcd_rangeMethodOk q E γr cid mid _ _ _ $$ [Hqr Ppb Hics]
  · iframe #
  ihave #Hmd := etcd_deleteMethodOk q E ρ.rd cid mid _ _ _ $$ [Hqd Ppb Hics]
  · iframe #
  ihave #Hmt := etcd_txnMethodOk q E ρ.rd γr cid mid _ _ _ $$ [Hqt Ppb Hics]
  · iframe #
  imod (grpc_serve_rpcs addr [il, im, iu] regs (etcdKVMethods q E ρ.rd γr cid mid)
    (etcdGrpcSlot s E γr) N (by simp only [etcdKVMethods, List.map]; decide)
    (by
      intro x hx
      apply hregs
      simp only [etcdKVMethods, List.mem_cons, List.mem_nil_iff, _root_.or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> simp [etcdKVRegs])) $$ [Hl Hslots] with Hrpcs
  · iframe
    imodintro
    simp only [etcdKVMethods]
    unfold etcdGrpcSlot
    iframe #
    iapply BigSepL.bigSepL_nil.2
    itrivial
  simp only [etcdKVMethods]
  icases Hrpcs with ⟨#H1, #H2, #H3, #H4, -⟩
  imodintro
  iframe #

end proofs

end v3rpc
end EtcdGrove
end Perennial
