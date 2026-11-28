/-
**etcd's KV methods at the view: the member quantified away** (stage S1 of the defined `etcdSvc`,
2026-11-27). Lean-first (no Rocq counterpart).

The view specs (`etcdPutSpecV`, ...: heap-free, at the cluster's KV names `γk` alone, in the
client's own terms) are `KVService.lean`'s, where the client's `isKv` registers them; with the
conversions from the member's auth-off specs (`etcdPutSpecV_plain`, ...). Here:

* **The messages' wire parts** (heap-free, `putReqWire`, ...; `pbPutRequest_wire`, ... at a machine's
  heap, `rfl`), as `grpcdriver/SvcG.lean`'s.
* **A member serving its specs over the mode serves the view** (`etcdPutSpecV_M`, ...: the view's
  caller meets the member's spec over the mode, after an update): `Range` in either mode; `DeleteRange`
  in either; `Compact` with auth
  off (the only mode its spec covers); `Put` and `Txn` with auth off (with auth on the member's spec
  gives no revision bound for a write's reply yet).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.KVServiceOn

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

/-! ## The messages' wire parts (no heap) -/

section wire
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]

/-- A `PutRequest`'s wire part (`pbPutRequest.wire`). -/
abbrev putReqWire : ProtoWire := ⟨etcdserverpb.PutRequest.ty, OpFull, putReqTree, inferInstance⟩

/-- A `PutResponse`'s wire part (`pbPutResponse.wire`). -/
abbrev putRespWire : ProtoWire :=
  ⟨etcdserverpb.PutResponse.ty, PutRespM, putRespTree, inferInstance⟩

/-- A `RangeRequest`'s wire part (`pbRangeRequest.wire`). -/
abbrev rangeReqWire : ProtoWire :=
  ⟨etcdserverpb.RangeRequest.ty, OpFull, rangeReqTree, inferInstance⟩

/-- A `RangeResponse`'s wire part (`pbRangeResponse.wire`). -/
abbrev rangeRespWire : ProtoWire :=
  ⟨etcdserverpb.RangeResponse.ty, RangeRespM, rangeRespTree, inferInstance⟩

/-- A `DeleteRangeRequest`'s wire part (`pbDeleteRangeRequest.wire`). -/
abbrev delReqWire : ProtoWire :=
  ⟨etcdserverpb.DeleteRangeRequest.ty, OpFull, delReqTree, inferInstance⟩

/-- A `DeleteRangeResponse`'s wire part (`pbDeleteRangeResponse.wire`). -/
abbrev delRespWire : ProtoWire :=
  ⟨etcdserverpb.DeleteRangeResponse.ty, DelRespM, delRespTree, inferInstance⟩

/-- A `TxnRequest`'s wire part (`pbTxnRequest.wire`). -/
abbrev txnReqWire : ProtoWire :=
  ⟨etcdserverpb.TxnRequest.ty, TxnModel, txnReqTree, inferInstance⟩

/-- A `TxnResponse`'s wire part (`pbTxnResponse.wire`). -/
abbrev txnRespWire : ProtoWire :=
  ⟨etcdserverpb.TxnResponse.ty, TxnRespM, txnRespTree, inferInstance⟩

/-- A `CompactionRequest`'s wire part (`pbCompactionRequest.wire`). -/
abbrev compactReqWire : ProtoWire :=
  ⟨etcdserverpb.CompactionRequest.ty, CompactReqM, compactReqTree, inferInstance⟩

/-- A `CompactionResponse`'s wire part (`pbCompactionResponse.wire`). -/
abbrev compactRespWire : ProtoWire :=
  ⟨etcdserverpb.CompactionResponse.ty, CompactRespM, compactRespTree, inferInstance⟩

end wire

/-! ## At a machine's heap -/

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem pbPutRequest_wire : (pbPutRequest (GF := GF)).wire = putReqWire := rfl
theorem pbPutResponse_wire : (pbPutResponse (GF := GF)).wire = putRespWire := rfl
theorem pbRangeRequest_wire : (pbRangeRequest (GF := GF)).wire = rangeReqWire := rfl
theorem pbRangeResponse_wire : (pbRangeResponse (GF := GF)).wire = rangeRespWire := rfl
theorem pbDeleteRangeRequest_wire : (pbDeleteRangeRequest (GF := GF)).wire = delReqWire := rfl
theorem pbDeleteRangeResponse_wire : (pbDeleteRangeResponse (GF := GF)).wire = delRespWire := rfl
theorem pbTxnRequest_wire : (pbTxnRequest (GF := GF)).wire = txnReqWire := rfl
theorem pbTxnResponse_wire : (pbTxnResponse (GF := GF)).wire = txnRespWire := rfl
theorem pbCompactionRequest_wire : (pbCompactionRequest (GF := GF)).wire = compactReqWire := rfl
theorem pbCompactionResponse_wire :
    (pbCompactionResponse (GF := GF)).wire = compactRespWire := rfl

end heap

section members
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The view's `Put` meets a member's auth-off spec over the mode** (after an update; through
`etcdPutSpecV_plain`): at names of the same KV (`kvSame`), with the store's receipts bounded. -/
theorem etcdPutSpecV_M (T : IProp GF) [Persistent T] (E : apply.AEnv GF) (ρ : ReqNames)
    (cid mid : w64) (γk : KVNames) (hk : kvSame ρ.rd.kv γk) (hrb : receiptBound GF ≤ 2 ^ 62) :
    ∀ md o Φ Ψe, etcdPutSpecV (GF := GF) γk md o Φ Ψe ⊢
      |==> etcdPutSpecM false T E ρ cid mid md o Φ Ψe := by
  intro md o Φ Ψe
  iintro H
  imod (etcdPutSpecV_plain E ρ.rd cid mid γk hk hrb md o Φ Ψe) $$ H with H
  iapply (etcdPutSpecM_false T E ρ cid mid md o Φ Ψe) $$ H

/-- **The view's `Range` meets a member's spec in either auth mode** (after an update): at names
of the same KV, with the store's receipts bounded; the auth index's lower bound `0`
(`authPubLbM_zero`), the reply's auth facts unused. -/
theorem etcdRangeSpecV_M (on : Bool) (T : IProp GF) [Persistent T] (E : apply.AEnv GF)
    (γr : ReadNames) (cid mid : w64) (γk : KVNames) (hk : kvSame γr.kv γk)
    (hrb : receiptBound GF ≤ 2 ^ 62) :
    ∀ md o Φ Ψe, etcdRangeSpecV (GF := GF) γk md o Φ Ψe ⊢
      |==> etcdRangeSpecM on T E γr cid mid md o Φ Ψe := by
  intro md o Φ Ψe
  unfold etcdRangeSpecV etcdRangeSpecM etcdRangeSpecMW
  iintro ⟨#HΨe, %Q, #Hq, Hk⟩
  imod (srvStart_free (GF := GF) E γr) with ⟨#Hc, #HF⟩
  imod (authPubLbM_zero (GF := GF) E.authMode) with #Hn
  imodintro
  iexists (W64 0), [], Q, 0
  isplitr
  · iexact Hc
  isplitr
  · iexact HF
  isplitr
  · iexact Hn
  isplitr
  · iunfold rangeUpdKV at Hq
    icases Hq with (%h | ⟨%h, #Ha⟩)
    · ileft; ipureintro; exact h
    · iright
      isplitr
      · ipureintro; exact h
      rw [kvReadAu_names γr.kv γk hk.1]; iexact Ha
  isplitr
  · iintro -; iexact HΨe
  isplitr
  · isplit
    · iintro -; iapply HΨe
    · iintro -; iapply HΨe
  iintro %m #Hm -
  iapply Hk
  iapply (rangeStOk_V o Q m)
  iapply (rangeAns_st hrb [srvV E γr cid mid] (W64 0) [] o Q m)
  iunfold rangeAns
  iexists srvV E γr cid mid
  simp only [srvV]
  isplitr
  · ipureintro; exact List.mem_singleton_self _
  iexact Hm

/-- **The view's `DeleteRange` meets a member's spec in the mode `on`** (after an update): in either
mode (N1b-1: until then, with auth on, only for requests of the shape `auth.reqShape`); the reply's
grant unused. -/
theorem etcdDeleteSpecV_M (on : Bool) (T : IProp GF) [Persistent T] (E : apply.AEnv GF)
    (ρ : ReqNames) (cid mid : w64) (γk : KVNames) (hk : kvSame ρ.rd.kv γk)
    (hrb : receiptBound GF ≤ 2 ^ 62) :
    ∀ md o Φ Ψe, etcdDeleteSpecV (GF := GF) γk md o Φ Ψe ⊢
      |==> etcdDeleteSpecM on T E ρ cid mid md o Φ Ψe := by
  intro md o Φ Ψe
  unfold etcdDeleteSpecV etcdDeleteSpecM etcdDeleteSpecMW
  iintro ⟨#HΨe, %Q, %Hz, Hau, Hk⟩
  imod (srvStart_free (GF := GF) E ρ.rd) with ⟨-, #HF⟩
  ihave Hau : kvOpAu1 ρ.rd.kv (.deleteRange o) Q $$ [Hau]
  · rw [kvOpAu1_names ρ.rd.kv γk hk.1]; iexact Hau
  imod (kvOpAuM_of_au1 on T E ρ (auth.mdTokenOf md) (.deleteRange o) Q) $$ Hau with Hau
  imodintro
  isplitr
  · iexact HΨe
  iexists []
  isplitr
  · iexact HF
  iexists Q
  isplitr
  · ipureintro; exact Hz
  isplitl [Hau]
  · iexact Hau
  iintro %m Hm -
  iapply Hk
  iapply (delStOk_V o Q m)
  iapply (delAns_st hrb [srvV E ρ.rd cid mid] [] o Q m Hz)
  iunfold delAns
  iexists srvV E ρ.rd cid mid
  simp only [srvV]
  isplitr
  · ipureintro; exact List.mem_singleton_self _
  iexact Hm

/-- **The view's `Txn` meets a member's auth-off spec over the mode** (after an update; through
`etcdTxnSpecV_plain`): its write and read names one (`ρ.rd = γr`, as an auth-off server's), of the
same KV. -/
theorem etcdTxnSpecV_M (T : IProp GF) [Persistent T] (E : apply.AEnv GF) (ρ : ReqNames)
    (γr : ReadNames) (cid mid : w64) (γk : KVNames) (hρ : ρ.rd = γr) (hk : kvSame γr.kv γk)
    (hrb : receiptBound GF ≤ 2 ^ 62) :
    ∀ md t Φ Ψe, etcdTxnSpecV (GF := GF) γk md t Φ Ψe ⊢
      |==> etcdTxnSpecM false T E ρ γr cid mid md t Φ Ψe := by
  intro md t Φ Ψe
  subst hρ
  iintro H
  imod (etcdTxnSpecV_plain E ρ.rd cid mid γk hk hrb md t Φ Ψe) $$ H with H
  iapply (etcdTxnSpecM_false T E ρ ρ.rd cid mid md t Φ Ψe) $$ H

/-- **The view's `Compact` meets a member's spec in the mode `on`**, which specifies `Compact` with
auth off only (`etcdCompactSpecMW`'s `⌜on = false⌝`): at names of the same KV. -/
theorem etcdCompactSpecV_M (on : Bool) (E : apply.AEnv GF) (ρ : ReqNames) (cid mid : w64)
    (γk : KVNames) (hk : kvSame ρ.rd.kv γk) (hon : on = false) :
    ∀ md o Φ Ψe, etcdCompactSpecV (GF := GF) γk md o Φ Ψe ⊢
      |==> GrpcSpec.md (etcdCompactSpecM on E ρ cid mid) md o Φ Ψe := by
  intro md o Φ Ψe
  subst hon
  iintro H
  imod (etcdCompactSpecV_plain E ρ.rd cid mid γk hk md o Φ Ψe) $$ H with H
  iapply (etcdCompactSpecM_false E ρ cid mid md o Φ Ψe) $$ H

end members

end client
end EtcdGrove
end Perennial
