/-
**etcd's KV methods at the view: the member quantified away** (stage S1 of the defined `etcdSvc`,
2026-11-27). Lean-first (no Rocq counterpart).

A service table (`GrpcSvc`) holds no heap and every machine holds the same one, so the specs of its
entries cannot name a member (its apply environment, read names, ids, TLS identity): they are written
at the cluster's KV names `γk` alone, in the client's own terms (`KVService.lean`'s last section): the
caller's atomic update at `γk` and the reply's fields as functions of the state it fired at
(`putStOk`, `rangeStOk`, `delStOk`, `txnStOk`), the error outcome at every description.

* **The view specs** (heap-free, `etcdPutSpecV`, `etcdRangeSpecV`, `etcdDeleteSpecV`, `etcdTxnSpecV`,
  `etcdCompactSpecV`), over the heap-free forms of the client's reply facts (`putStOkV`, ...: the same
  definitions restated over the global ghost state, `putStOk_eq_V`, ... at a machine's heap, `rfl`).
  They ignore the metadata: one spec serves every endpoint.
* **The messages' wire parts** (heap-free, `putReqWire`, ...; `pbPutRequest_wire`, ... at a machine's
  heap, `rfl`), as `grpcdriver/SvcG.lean`'s.
* **A member serving its auth-off specs serves the view** (`etcdPutSpecV_M`, ...: the view's caller
  meets the member's spec over the mode at `false`, after an update): the floor `[]` and the committed
  index `0` are free (`srvStart_alloc`), the update at `γk` is the member's at names of the same KV
  (`kvSame`), and the member's reply is some member's answer (`putAns`, ...), which says what the
  client's reply facts say (`putAns_st`, ...), with the store's receipts bounded
  (`receiptBound GF ≤ 2 ^ 62`).
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

/-! ## The client's reply facts and the view specs (no heap) -/

section defsHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- `putStOk` over the global ghost state (`putStOk_eq_V`). -/
def putStOkV (γ : KVNames) (o : OpFull) (Q : KVState → IProp GF) (m : PutRespM) : IProp GF :=
  iprop(∃ σ : KVState, Q σ ∗ ⌜m.hdr.revision = W64 ((σ.rev + 1 : Nat) : Int) ∧
    m.prev = (if o.base.prevKV then (σ.store.lookup o.key).map (KVRec.toKv o.key) else none) ∧
    kvRevFits (σ.rev + 1) ∧ kvLogOk σ ∧ kvLogOk (kvOpStep (.put o) σ)⌝ ∗
    kvRevLb γ m.hdr.revision)

/-- `rangeStOk` over the global ghost state (`rangeStOk_eq_V`). -/
def rangeStOkV (o : OpFull) (Q : KVState → IProp GF) (m : RangeRespM) : IProp GF :=
  iprop(∃ σ : KVState, (if o.base.serializable then iprop(True) else iprop(□ Q σ)) ∗
    ⌜sint.Z o.base.rev ≤ (σ.rev : Int) ∧
      txn.srvRangeOk o (σ.at (σ.readRev o.base.rev)).kvs m.kvs m.more ∧
      m.count = txn.srvCount o (σ.at (σ.readRev o.base.rev)).kvs true ∧
      m.hdr.revision = W64 (σ.rev : Int) ∧ kvRevFits σ.rev ∧ kvLogOk σ⌝)

/-- `delStOk` over the global ghost state (`delStOk_eq_V`). -/
def delStOkV (o : OpFull) (Q : KVState → IProp GF) (m : DelRespM) : IProp GF :=
  iprop(∃ σ : KVState, Q σ ∗ ⌜m.deleted = W64 ((rangeIn σ.kvs o).length : Int) ∧
    m.prevs = (if o.base.prevKV then rangeIn σ.kvs o else []) ∧
    m.hdr.revision = W64 ((kvOpStep (.deleteRange o) σ).rev : Int) ∧ kvRevFits (σ.rev + 1) ∧
    kvLogOk σ ∧ kvLogOk (kvOpStep (.deleteRange o) σ)⌝)

/-- `txnStOk` over the global ghost state (`txnStOk_eq_V`). -/
def txnStOkV (γ : KVNames) (t : TxnModel) (Q : KVState → IProp GF) (m : TxnRespM) : IProp GF :=
  iprop(∃ σ : KVState,
    (if txn.txnReadonly t then
      (if txn.txnSerializable t then iprop(True) else iprop(□ Q σ)) else Q σ) ∗
    ⌜m.succeeded = (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs t).1 ∧
      opRespsRel false (t.branch m.succeeded)
        (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs t).2.2 m.resps ∧
      m.hdr.revision = W64 ((if txn.txnReadonly t then σ.rev else
        (σ.commit (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs t).2.1).rev : Nat) : Int) ∧
      kvRevFits σ.rev ∧ kvLogOk σ ∧
      (txn.txnReadonly t = false → kvLogOk (σ.commit (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs t).2.1))⌝ ∗
    txnRevLb γ t m)

/-- `rangeUpdK` over the global ghost state (`rangeUpdK_eq_V`). -/
def rangeUpdKV (γ : KVNames) (o : OpFull) (Q : KVState → IProp GF) : IProp GF :=
  iprop(⌜Q = fun _ => iprop(True)⌝ ∨ (⌜o.base.serializable = false⌝ ∗ kvReadAu γ Q))

instance rangeUpdKV_persistent (γ : KVNames) (o : OpFull) (Q : KVState → IProp GF) :
    Persistent (rangeUpdKV γ o Q) := by
  unfold rangeUpdKV; infer_instance

/-- `txnUpdK` over the global ghost state (`txnUpdK_eq_V`). -/
def txnUpdKV (γ : KVNames) (t : TxnModel) (Q : KVState → IProp GF) : IProp GF :=
  iprop(⌜txn.txnReadonly t = true ∧ Q = fun _ => iprop(True)⌝ ∨
    (⌜txn.txnReadonly t = true ∧ txn.txnSerializable t = false⌝ ∗ kvReadAu γ Q) ∨
    (⌜txn.txnReadonly t = false ∧ txn.txnPlain t ∧ txnNoZeroEnd t⌝ ∗ kvOpAu1 γ (.txn t) Q))

/-- **etcd's `Put` at the view** (the KV names `γk`; any metadata): a caller asking a put with no
lease, with its update at `γk` fired at most once (`kvOpAu1`), gets a reply `m` with `putStOkV`;
the error outcome at every description. -/
def etcdPutSpecV (γk : KVNames) :
    GrpcMd → OpFull → (PutRespM → IProp GF) → (GoString → IProp GF) → IProp GF :=
  fun _ (o : OpFull) (Φ : PutRespM → IProp GF) (Ψe : GoString → IProp GF) =>
    iprop((□ ∀ d, Ψe d) ∗ ∃ Q : KVState → IProp GF, ⌜o.leaseID = W64 0⌝ ∗
      kvOpAu1 γk (.put o) Q ∗ ∀ m : PutRespM, putStOkV γk o Q m -∗ Φ m)

/-- **etcd's `Range` at the view**: a caller with a read update at `γk` or none (`rangeUpdKV`)
gets a reply `m` with `rangeStOkV`; the error outcome at every description. -/
def etcdRangeSpecV (γk : KVNames) :
    GrpcMd → OpFull → (RangeRespM → IProp GF) → (GoString → IProp GF) → IProp GF :=
  fun _ (o : OpFull) (Φ : RangeRespM → IProp GF) (Ψe : GoString → IProp GF) =>
    iprop((□ ∀ d, Ψe d) ∗ ∃ Q : KVState → IProp GF, rangeUpdKV γk o Q ∗
      ∀ m : RangeRespM, rangeStOkV o Q m -∗ Φ m)

/-- **etcd's `DeleteRange` at the view**: a caller asking a delete whose range end is not `[0]`,
with its update at `γk` fired at most once, gets a reply `m` with `delStOkV`; the error outcome at
every description. -/
def etcdDeleteSpecV (γk : KVNames) :
    GrpcMd → OpFull → (DelRespM → IProp GF) → (GoString → IProp GF) → IProp GF :=
  fun _ (o : OpFull) (Φ : DelRespM → IProp GF) (Ψe : GoString → IProp GF) =>
    iprop((□ ∀ d, Ψe d) ∗ ∃ Q : KVState → IProp GF, ⌜o.base.rangeEnd ≠ [W8 0]⌝ ∗
      kvOpAu1 γk (.deleteRange o) Q ∗ ∀ m : DelRespM, delStOkV o Q m -∗ Φ m)

/-- **etcd's `Txn` at the view**: a caller asking a transaction of plain operations within the
txn package's model, with its update at `γk` (`txnUpdKV`), gets a reply `m` with `txnStOkV`; the
error outcome at every description. -/
def etcdTxnSpecV (γk : KVNames) :
    GrpcMd → TxnModel → (TxnRespM → IProp GF) → (GoString → IProp GF) → IProp GF :=
  fun _ (t : TxnModel) (Φ : TxnRespM → IProp GF) (Ψe : GoString → IProp GF) =>
    iprop((□ ∀ d, Ψe d) ∗ ⌜TxnModel.plain t ∧ txnModelIn t⌝ ∗ ∃ Q : KVState → IProp GF,
      txnUpdKV γk t Q ∗ ∀ m : TxnRespM, txnStOkV γk t Q m -∗ Φ m)

/-- **etcd's `Compact` at the view**: a caller asking a compaction, not physical, at a revision
past `0` at least the cluster's retention behind one the KV has reached, on a compacting cluster,
gets a reply; the error outcome at every description. -/
def etcdCompactSpecV (γk : KVNames) :
    GrpcMd → CompactReqM → (CompactRespM → IProp GF) → (GoString → IProp GF) → IProp GF :=
  fun _ (o : CompactReqM) (Φ : CompactRespM → IProp GF) (Ψe : GoString → IProp GF) =>
    iprop((□ ∀ d, Ψe d) ∗ ⌜1 ≤ sint.Z o.revision ∧ o.physical = false ∧ γk.cmp = true⌝ ∗
      kvRevLbZ γk (sint.Z o.revision + γk.cret) ∗ ∀ m : CompactRespM, Φ m)

end defsHF

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

theorem putStOk_eq_V (γ : KVNames) (o : OpFull) (Q : KVState → IProp GF) (m : PutRespM) :
    putStOk γ o Q m = putStOkV γ o Q m := rfl

theorem rangeStOk_eq_V (o : OpFull) (Q : KVState → IProp GF) (m : RangeRespM) :
    rangeStOk o Q m = rangeStOkV o Q m := rfl

theorem delStOk_eq_V (o : OpFull) (Q : KVState → IProp GF) (m : DelRespM) :
    delStOk o Q m = delStOkV o Q m := rfl

theorem txnStOk_eq_V (γ : KVNames) (t : TxnModel) (Q : KVState → IProp GF) (m : TxnRespM) :
    txnStOk γ t Q m = txnStOkV γ t Q m := rfl

theorem putStOk_V (γ : KVNames) (o : OpFull) (Q : KVState → IProp GF) (m : PutRespM) :
    putStOk γ o Q m ⊢ putStOkV γ o Q m := .rfl

theorem rangeStOk_V (o : OpFull) (Q : KVState → IProp GF) (m : RangeRespM) :
    rangeStOk o Q m ⊢ rangeStOkV o Q m := .rfl

theorem delStOk_V (o : OpFull) (Q : KVState → IProp GF) (m : DelRespM) :
    delStOk o Q m ⊢ delStOkV o Q m := .rfl

theorem txnStOk_V (γ : KVNames) (t : TxnModel) (Q : KVState → IProp GF) (m : TxnRespM) :
    txnStOk γ t Q m ⊢ txnStOkV γ t Q m := .rfl

theorem rangeUpdK_eq_V (γ : KVNames) (o : OpFull) (Q : KVState → IProp GF) :
    rangeUpdK γ o Q = rangeUpdKV γ o Q := rfl

theorem txnUpdK_eq_V (γ : KVNames) (t : TxnModel) (Q : KVState → IProp GF) :
    txnUpdK γ t Q = txnUpdKV γ t Q := rfl

theorem txnUpdKV_K (γ : KVNames) (t : TxnModel) (Q : KVState → IProp GF) :
    txnUpdKV γ t Q ⊢ txnUpdK γ t Q := .rfl

/-- **A member's names, as the members' lemmas take them** (its address unused). -/
def srvV (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64) : SrvAt GF := ⟨go!"", E, γr, cid, mid⟩

theorem srvV_same {γr : ReadNames} {γk : KVNames} (hk : kvSame γr.kv γk) (E : apply.AEnv GF)
    (cid mid : w64) : ∀ x ∈ [srvV E γr cid mid], kvSame x.γr.kv γk := by
  intro x hx
  rw [List.mem_singleton] at hx
  subst hx
  exact hk

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

/-- **A call's start at a member is free**: the committed index at least `0` and the floor `[]`
(`srvStart_alloc`). -/
theorem srvStart_free (E : apply.AEnv GF) (γr : ReadNames) :
    ⊢ |==> (committedAtLeast (GF := GF) γr (W64 0) ∗ srvApi.kvLogLb E.γs []) :=
  (srvStart_alloc (GF := GF) [srvV E γr 0 0]).trans
    (BIUpdate.mono (BigSepL.bigSepL_singleton (Φ := fun _ (x : SrvAt GF) => srvStart x)).1)

/-- **The view's `Put` meets a member's auth-off spec** (after an update): at names of the same KV
(`kvSame`), with the store's receipts bounded. -/
theorem etcdPutSpecV_M (T : IProp GF) [Persistent T] (E : apply.AEnv GF) (ρ : ReqNames)
    (cid mid : w64) (γk : KVNames) (hk : kvSame ρ.rd.kv γk) (hrb : receiptBound GF ≤ 2 ^ 62) :
    ∀ md o Φ Ψe, etcdPutSpecV (GF := GF) γk md o Φ Ψe ⊢
      |==> etcdPutSpecM false T E ρ cid mid md o Φ Ψe := by
  intro md o Φ Ψe
  unfold etcdPutSpecV etcdPutSpecM etcdPutSpecMW
  iintro ⟨#HΨe, %Q, %Hl, Hau, Hk⟩
  imod (srvStart_free (GF := GF) E ρ.rd) with ⟨-, #HF⟩
  ihave Hau : kvOpAu1 ρ.rd.kv (.put o) Q $$ [Hau]
  · rw [kvOpAu1_names ρ.rd.kv γk hk.1]; iexact Hau
  imod (kvOpAuM_of_au1 false T E ρ (auth.mdTokenOf md) (.put o) Q) $$ Hau with Hau
  imodintro
  isplitr
  · iexact HΨe
  iexists []
  isplitr
  · iexact HF
  iexists Q
  isplitr
  · ipureintro; exact Or.inl Hl
  isplitl [Hau]
  · iexact Hau
  iintro %m Hm Hr -
  iapply Hk
  iapply (putStOk_V γk o Q m)
  iapply (putAns_st hrb [srvV E ρ.rd cid mid] γk (srvV_same hk E cid mid) [] o Q m)
  iunfold putAns
  iexists srvV E ρ.rd cid mid
  simp only [srvV]
  isplitr
  · ipureintro; exact List.mem_singleton_self _
  isplitl [Hm]
  · iexact Hm
  iapply Hr
  ipureintro; trivial

/-- **The view's `Range` meets a member's auth-off spec** (after an update): at names of the same
KV, with the store's receipts bounded. -/
theorem etcdRangeSpecV_M (T : IProp GF) [Persistent T] (E : apply.AEnv GF) (γr : ReadNames)
    (cid mid : w64) (γk : KVNames) (hk : kvSame γr.kv γk) (hrb : receiptBound GF ≤ 2 ^ 62) :
    ∀ md o Φ Ψe, etcdRangeSpecV (GF := GF) γk md o Φ Ψe ⊢
      |==> etcdRangeSpecM false T E γr cid mid md o Φ Ψe := by
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

/-- **The view's `DeleteRange` meets a member's auth-off spec** (after an update). -/
theorem etcdDeleteSpecV_M (T : IProp GF) [Persistent T] (E : apply.AEnv GF) (ρ : ReqNames)
    (cid mid : w64) (γk : KVNames) (hk : kvSame ρ.rd.kv γk) (hrb : receiptBound GF ≤ 2 ^ 62) :
    ∀ md o Φ Ψe, etcdDeleteSpecV (GF := GF) γk md o Φ Ψe ⊢
      |==> etcdDeleteSpecM false T E ρ cid mid md o Φ Ψe := by
  intro md o Φ Ψe
  unfold etcdDeleteSpecV etcdDeleteSpecM etcdDeleteSpecMW
  iintro ⟨#HΨe, %Q, %Hz, Hau, Hk⟩
  imod (srvStart_free (GF := GF) E ρ.rd) with ⟨-, #HF⟩
  ihave Hau : kvOpAu1 ρ.rd.kv (.deleteRange o) Q $$ [Hau]
  · rw [kvOpAu1_names ρ.rd.kv γk hk.1]; iexact Hau
  imod (kvOpAuM_of_au1 false T E ρ (auth.mdTokenOf md) (.deleteRange o) Q) $$ Hau with Hau
  imodintro
  isplitr
  · iexact HΨe
  isplitr
  · ipureintro; intro h; cases h
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

/-- **The view's `Txn` meets a member's auth-off spec** (after an update): its write and read
names one (`ρ.rd = γr`, as an auth-off server's), of the same KV. -/
theorem etcdTxnSpecV_M (T : IProp GF) [Persistent T] (E : apply.AEnv GF) (ρ : ReqNames)
    (γr : ReadNames) (cid mid : w64) (γk : KVNames) (hρ : ρ.rd = γr) (hk : kvSame γr.kv γk)
    (hrb : receiptBound GF ≤ 2 ^ 62) :
    ∀ md t Φ Ψe, etcdTxnSpecV (GF := GF) γk md t Φ Ψe ⊢
      |==> etcdTxnSpecM false T E ρ γr cid mid md t Φ Ψe := by
  intro md t Φ Ψe
  subst hρ
  unfold etcdTxnSpecV etcdTxnSpecM etcdTxnSpecMW
  iintro ⟨#HΨe, %Hpl, %Q, Hd, Hk⟩
  ihave Hd := txnUpdKV_K γk t Q $$ Hd
  ihave ⟨%Hz, Hd⟩ := txnUpdK_nz γk t Q $$ Hd
  imod (srvStart_free (GF := GF) E ρ.rd) with ⟨#Hc, #HF⟩
  imod (authPubLbM_zero (GF := GF) E.authMode) with #Hn
  iunfold txnUpdK at Hd
  ihave Hd : iprop(|==> ((⌜txn.txnReadonly t = true ∧ Q = fun _ => iprop(True)⌝ ∨
        (⌜txn.txnReadonly t = true ∧ txn.txnSerializable t = false⌝ ∗ kvReadAu ρ.rd.kv Q) ∨
        (⌜txn.txnReadonly t = false ∧
            (txn.txnPlain t ∨ (false = true ∧ ρ.kv.lm = .revocable ∧ txnPlainL t)) ∧
            txnNoZeroEnd t ∧ txnNestOk t⌝ ∗
          v3rpc.kvOpAuM false T E ρ (auth.mdTokenOf md) (.txn t) Q)))) $$ [Hd]
  · icases Hd with (%H | ⟨%H, #Ha⟩ | ⟨%H, Ha⟩)
    · imodintro; ileft; ipureintro; exact H
    · imodintro; iright; ileft; isplitr
      · ipureintro; exact H
      rw [kvReadAu_names ρ.rd.kv γk hk.1]; iexact Ha
    · ihave Ha : kvOpAu1 ρ.rd.kv (.txn t) Q $$ [Ha]
      · rw [kvOpAu1_names ρ.rd.kv γk hk.1]; iexact Ha
      imod (kvOpAuM_of_au1 false T E ρ (auth.mdTokenOf md) (.txn t) Q) $$ Ha with Ha
      imodintro; iright; iright; isplitr
      · ipureintro; exact ⟨H.1, Or.inl H.2.1, H.2.2, txnNestOk_of_plain t Hpl.1 Hpl.2⟩
      iexact Ha
  imod Hd with Hd
  imodintro
  isplitr
  · iexact HΨe
  isplitr
  · ipureintro; exact ⟨fun _ => Hpl.2, fun h => by cases h⟩
  iexists Q
  isplitl [Hd]
  · iexact Hd
  iexists (W64 0), [], 0
  isplitr
  · iexact Hc
  isplitr
  · iexact HF
  isplitr
  · iexact Hn
  iintro %m Hm Hr -
  iapply Hk
  iapply (txnStOk_V γk t Q m)
  iapply (txnAns_st hrb [srvV E ρ.rd cid mid] γk (srvV_same hk E cid mid) (W64 0) [] t Q m Hz)
  iunfold txnAns
  iexists srvV E ρ.rd cid mid
  simp only [srvV]
  isplitr
  · ipureintro; exact List.mem_singleton_self _
  isplitl [Hm]
  · iexact Hm
  iapply Hr
  ipureintro; trivial

/-- **The view's `Compact` meets a member's auth-off spec**: at names of the same KV (the
compaction mode and retention, the revisions reached). -/
theorem etcdCompactSpecV_M (E : apply.AEnv GF) (ρ : ReqNames) (cid mid : w64) (γk : KVNames)
    (hk : kvSame ρ.rd.kv γk) :
    ∀ md o Φ Ψe, etcdCompactSpecV (GF := GF) γk md o Φ Ψe ⊢
      |==> GrpcSpec.md (etcdCompactSpecM false E ρ cid mid) md o Φ Ψe := by
  intro md o Φ Ψe
  unfold etcdCompactSpecV GrpcSpec.md etcdCompactSpecM etcdCompactSpecMW etcdCompactSpecW
  iintro ⟨#HΨe, %Ho, #Hr, Hk⟩
  imodintro
  isplitl [Hk]
  · isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro
      obtain ⟨h1, h2, h3⟩ := Ho
      exact ⟨h1, h2, by rw [hk.2.2.2.2.2.1]; exact h3⟩
    isplitr [Hk]
    · rw [hk.2.2.2.2.2.2]
      iapply (kvRevLbZ_same γk ρ.rd.kv (kvSame_symm hk))
      iexact Hr
    iintro %m -
    iapply Hk
  · iexact HΨe

end members

end client
end EtcdGrove
end Perennial
