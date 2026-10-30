/-
**The client's KV calls to a member started with auth on** (the auth plan's E3zc, step B3,
2026-10-28): `Results.lean`'s `client_*_any`, through a `*kv` over a connection `conn` to one
member at `addr` whose KV methods are registered with etcd's specs with auth on
(`KVServiceOn.lean`: `etcdPutSpecOn`, ..., what `etcd_kv_auth_served_on` gives). They are
instances of the one client KV stack (`KVMembers.lean`'s `kv.Put.specG`, ..., proved once for
any spec registered at the connection; `notes/decisions.md`, "E3zc of the auth plan"), not a
second stack.

A reply carries, besides what it carries with auth off (`putReplied`, ...), the server's auth
facts at the token of the metadata some attempt of the call delivered (`∃ md,
⌜clientAttemptMd conn ctx md⌝ ∗ …`: the attempt's metadata is the context's outgoing metadata with
the client's API version, delivered by grpc on `conn`): a write's grant (`v3rpc.writeGrantOn`), a
read's check (`v3rpc.rangeAuthed`, `txnAuthOn`) at the lower bound `n` of the auth store's
published index the caller gives (`auth.authPubLbM`; `0` is free). What the token is (the
client's, after `Authenticate`) is the auth plan's item 2 (C1–C4, over `clientAttemptMd`). A
write's update is told the same grant when it fires (`clientOpAuOn`, the auth-mode merge's 5a): at
a lower bound of the requested log the caller gives (`srvReqLogLb`; `[]` is free,
`clientOpAuOn_of_au1`).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.Results
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

section on
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **`kv.Put(ctx, key, val)` through a `*kv` over `conn` to a member with auth on** (as
`client_put_any` at one member): etcd's `Put` with auth on registered at `addr`, the floor `F`
and the caller's update told the put's grant (`clientOpAuOn`), persistent or on a client that sends
a write at most once; `nil` and the
reply with `putReplied` and the put's grant at the token of some attempt's metadata, or an
error. -/
theorem client_put_on (api conn : Loc) (addr : GoString) (s : Loc) (E : apply.AEnv GF)
    (ρ : ReqNames) (cid mid : w64) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key val : GoString) (sl : GoSlice) (Q : KVState → IProp GF) (F : mvcc.Log) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        kvObjAtC api conn [addr] ∗
        isGrpcRpcMd addr go!"/etcdserverpb.KV/Put" (etcdPutSpecOn s E ρ cid mid) ∗
        mvcc.idxCert E.γ.idx F ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
        (□ clientOpAuOn s E ρ conn (GoInterface.ok ci) (.put (putKeyOp key val)) Q ∨
          (writeOnce api [addr] ∗
            clientOpAuOn s E ρ conn (GoInterface.ok ci) (.put (putKeyOp key val)) Q)) }}
      (App (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
          go!"Put")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : PutRespM, putRespMsg resp m ∗
            putReplied E ρ.rd F (putKeyOp key val) Q cid mid m ∗
            ∃ md, ⌜clientAttemptMd conn (GoInterface.ok ci) md⌝ ∗
              v3rpc.writeGrantOn s E ρ (auth.mdTokenOf md) (irrPut (putKeyOp key val))) ∨
          (⌜err ≠ GoInterface.nil ∧ resp = null⌝ ∗ kvErr err) }} := by
  iintro %Φ ⟨#Pc, #Hkv, #Hreg, #HF, #Hctx', #Hce, #Hopts, Hau⟩ HΦ
  have Hpm : ¬ (opPutModel key val []).putPanics ∧ (opPutModel key val []).t = W64 2 := by
    refine ⟨?_, rfl⟩
    unfold opPutModel OpFull.putPanics opFold OpFull.putInit OpFull.newOp OpModel.zero
    simp
  iapply (v3.kv.wp_PutG api conn [addr] ci cd key val sl [] (etcdPutSpecOn s E ρ cid mid)
    (fun m => iprop(putReplied E ρ.rd F (putKeyOp key val) Q cid mid m ∗
      ∃ md, ⌜clientAttemptMd conn (GoInterface.ok ci) md⌝ ∗
        v3rpc.writeGrantOn s E ρ (auth.mdTokenOf md) (irrPut (putKeyOp key val))))) $$ [Hau]
  · iframe #
    isplitl []
    · ipureintro; exact Hpm
    rw [show putWireOf (opPutModel key val []) = putKeyOp key val from rfl]
    have h : (mvcc.idxCert E.γ.idx F ∗
          clientOpAuOn s E ρ conn (GoInterface.ok ci) (.put (putKeyOp key val)) Q : IProp GF) ⊢
        attemptPre conn (GoInterface.ok ci) (etcdPutSpecOn s E ρ cid mid)
          (putKeyOp key val)
          (fun (m : PutRespM) => iprop(putReplied E ρ.rd F (putKeyOp key val) Q cid mid m ∗
            ∃ md, ⌜clientAttemptMd conn (GoInterface.ok ci) md⌝ ∗
              v3rpc.writeGrantOn s E ρ (auth.mdTokenOf md) (irrPut (putKeyOp key val)))) := by
      iintro ⟨#HF, Hau⟩
      unfold attemptPre
      iintro %md %Hmd
      unfold etcdPutSpecOn
      iexists F
      iframe HF
      iexists Q
      isplitr
      · ipureintro; rfl
      isplitl [Hau]
      · iapply clientOpAuOn_attempt s E ρ conn (GoInterface.ok ci) md _ Q Hmd $$ Hau
      iintro %m Hm Hg
      simp only []
      iframe Hm
      iexists md
      iframe Hg
      ipureintro; exact Hmd
    iapply (kvReqPre_wand api [addr] (mvcc.idxCert E.γ.idx F) _ _ h)
    iframe HF
    unfold kvReqPre
    icases Hau with (#Hau | ⟨#Ho, Hau⟩)
    · ileft
      imodintro
      inext
      iexact Hau
    · iright
      iunfold writeOnce at Ho
      icases Ho with %Hnr
      isplitl []
      · ipureintro; exact Hnr
      inext
      iexact Hau
  inext
  iintro %resp %err Hout
  iapply HΦ
  iunfold putCallOut at Hout
  icases Hout with (⟨%Herr, %m, Hm, Hq⟩ | ⟨%Herr, #Hse, #Hcl⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m
    iframe Hm Hq
  · iright
    isplitl
    · ipureintro; exact ⟨Herr.1, Herr.2.2⟩
    · iunfold kvErr; iframe #; ipureintro; exact Herr.2.1

/-- **`kv.Get(ctx, key, opts...)` through a `*kv` over `conn` to a member with auth on** (as
`client_range_any` at one member): etcd's `Range` with auth on registered at `addr`, the member's
committed index at least `c`, the floor `F`, a lower bound `n` of the published auth index and the
caller's read update, persistent; `R` back, and `nil` with the reply's `rangeReplyOk` and the
read's check at the token of some attempt's metadata, or an error. -/
theorem client_range_on (api conn : Loc) (addr : GoString) (s : Loc) (E : apply.AEnv GF)
    (γr : ReadNames) (cid mid c : w64) (n : Nat) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key : GoString) (sl : GoSlice)
    (gs : List (OpFull → OpFull)) (R : IProp GF) (Q : KVState → IProp GF) (F : mvcc.Log) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        kvObjAtC api conn [addr] ∗
        isGrpcRpcMd addr go!"/etcdserverpb.KV/Range" (etcdRangeSpecOn s E γr cid mid) ∗
        committedAtLeast γr c ∗ mvcc.idxCert E.γ.idx F ∗ auth.authPubLbM E.authMode n ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAtRes sl gs R ∗ R ∗
        sortNamesIf (opGetModel key gs).base.sortSet ∗
        ⌜¬ opGetPanics gs ∧ (opGetModel key gs).t = W64 1⌝ ∗
        □ (⌜Q = fun _ => iprop(True)⌝ ∨
          (⌜(rangeWireOf (opGetModel key gs)).base.serializable = false⌝ ∗ kvReadAu γr.kv Q)) }}
      (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
          go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); R ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ m : RangeRespM, rangeRespMsg resp m ∗
            rangeReplyOk E γr c F (rangeWireOf (opGetModel key gs)) cid mid Q m ∗
            ∃ md, ⌜clientAttemptMd conn (GoInterface.ok ci) md⌝ ∗
              v3rpc.rangeAuthed s E γr c n (auth.mdTokenOf md) (rangeWireOf (opGetModel key gs))) ∨
          (⌜err ≠ GoInterface.nil ∧ resp = null⌝ ∗ kvErr err)) }} := by
  iintro %Φ ⟨#Pc, #Hkv, #Hreg, #Hc, #HF, #Hn, #Hctx', #Hce, Hopts, HR, Hsn, %Hg, #Hdq⟩ HΦ
  iapply (v3.kv.wp_GetG api conn [addr] ci cd key sl gs R (etcdRangeSpecOn s E γr cid mid)
    (fun m => iprop(rangeReplyOk E γr c F (rangeWireOf (opGetModel key gs)) cid mid Q m ∗
      ∃ md, ⌜clientAttemptMd conn (GoInterface.ok ci) md⌝ ∗
        v3rpc.rangeAuthed s E γr c n (auth.mdTokenOf md) (rangeWireOf (opGetModel key gs)))))
    $$ [Hopts HR Hsn]
  · iframe #
    iframe Hopts HR Hsn
    isplitl []
    · ipureintro; exact Hg
    imodintro
    inext
    unfold attemptPre
    iintro %md %Hmd
    unfold etcdRangeSpecOn
    iexists c, F, Q, n
    iframe Hc HF Hn Hdq
    iintro %m Hm Ha
    simp only []
    iframe Hm
    iexists md
    iframe Ha
    ipureintro; exact Hmd
  inext
  iintro %resp %err ⟨HR, Hout⟩
  iapply HΦ
  iframe HR
  iunfold rangeCallOut at Hout
  icases Hout with (⟨%Herr, %m, Hm, Hq⟩ | ⟨%Herr, #Hse, #Hcl⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m
    iframe Hm Hq
  · iright
    isplitl
    · ipureintro; exact ⟨Herr.1, Herr.2.2⟩
    · iunfold kvErr; iframe #; ipureintro; exact Herr.2.1

/-- **`kv.Delete(ctx, key)` through a `*kv` over `conn` to a member with auth on** (as
`client_put_on`; `client_delete_any` at one member): a non-empty key (the shape the permission
cache decides, `auth.reqShape`); the reply with `deleteReplied` and the delete's grant at the
token of some attempt's metadata. -/
theorem client_delete_on (api conn : Loc) (addr : GoString) (s : Loc) (E : apply.AEnv GF)
    (ρ : ReqNames) (cid mid : w64) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key : GoString) (sl : GoSlice) (Q : KVState → IProp GF) (F : mvcc.Log) (hk : key ≠ []) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        kvObjAtC api conn [addr] ∗
        isGrpcRpcMd addr go!"/etcdserverpb.KV/DeleteRange" (etcdDeleteSpecOn s E ρ cid mid) ∗
        mvcc.idxCert E.γ.idx F ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
        (□ clientOpAuOn s E ρ conn (GoInterface.ok ci) (.deleteRange (txn.deleteOpOf key [] false)) Q ∨
          (writeOnce api [addr] ∗
            clientOpAuOn s E ρ conn (GoInterface.ok ci)
              (.deleteRange (txn.deleteOpOf key [] false)) Q)) }}
      (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
          go!"Delete")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : DelRespM, delRespMsg resp m ∗
            deleteReplied E ρ.rd F (txn.deleteOpOf key [] false) Q cid mid m ∗
            ∃ md, ⌜clientAttemptMd conn (GoInterface.ok ci) md⌝ ∗
              v3rpc.writeGrantOn s E ρ (auth.mdTokenOf md)
                (irrDeleteRange (txn.deleteOpOf key [] false))) ∨
          (⌜err ≠ GoInterface.nil ∧ resp = null⌝ ∗ kvErr err) }} := by
  iintro %Φ ⟨#Pc, #Hkv, #Hreg, #HF, #Hctx', #Hce, #Hopts, Hau⟩ HΦ
  have hw : deleteWireOf (opDeleteModel key []) = txn.deleteOpOf key [] false := by
    simp [op_simps, deleteWireOf, txn.deleteOpOf]
  iapply (v3.kv.wp_DeleteG api conn [addr] ci cd key sl [] (etcdDeleteSpecOn s E ρ cid mid)
    (fun m => iprop(deleteReplied E ρ.rd F (txn.deleteOpOf key [] false) Q cid mid m ∗
      ∃ md, ⌜clientAttemptMd conn (GoInterface.ok ci) md⌝ ∗
        v3rpc.writeGrantOn s E ρ (auth.mdTokenOf md)
          (irrDeleteRange (txn.deleteOpOf key [] false))))) $$ [Hau]
  · iframe #
    isplitl []
    · ipureintro
      refine ⟨?_, rfl⟩
      simp [op_simps, opDeletePanics, opGetPanics, OpFull.deletePanics]
    rw [hw]
    have h : (mvcc.idxCert E.γ.idx F ∗
          clientOpAuOn s E ρ conn (GoInterface.ok ci) (.deleteRange (txn.deleteOpOf key [] false)) Q :
          IProp GF) ⊢
        attemptPre conn (GoInterface.ok ci) (etcdDeleteSpecOn s E ρ cid mid)
          (txn.deleteOpOf key [] false)
          (fun (m : DelRespM) =>
            iprop(deleteReplied E ρ.rd F (txn.deleteOpOf key [] false) Q cid mid m ∗
            ∃ md, ⌜clientAttemptMd conn (GoInterface.ok ci) md⌝ ∗
              v3rpc.writeGrantOn s E ρ (auth.mdTokenOf md)
                (irrDeleteRange (txn.deleteOpOf key [] false)))) := by
      iintro ⟨#HF, Hau⟩
      unfold attemptPre
      iintro %md %Hmd
      unfold etcdDeleteSpecOn
      isplitl []
      · ipureintro; exact ⟨hk, Or.inl rfl⟩
      iexists F
      iframe HF
      iexists Q
      isplitr
      · ipureintro; simp [txn.deleteOpOf]
      isplitl [Hau]
      · iapply clientOpAuOn_attempt s E ρ conn (GoInterface.ok ci) md _ Q Hmd $$ Hau
      iintro %m Hm Hg
      simp only []
      iframe Hm
      iexists md
      iframe Hg
      ipureintro; exact Hmd
    iapply (kvReqPre_wand api [addr] (mvcc.idxCert E.γ.idx F) _ _ h)
    iframe HF
    unfold kvReqPre
    icases Hau with (#Hau | ⟨#Ho, Hau⟩)
    · ileft
      imodintro
      inext
      iexact Hau
    · iright
      iunfold writeOnce at Ho
      icases Ho with %Hnr
      isplitl []
      · ipureintro; exact Hnr
      inext
      iexact Hau
  inext
  iintro %resp %err Hout
  iapply HΦ
  iunfold deleteCallOut at Hout
  icases Hout with (⟨%Herr, %m, Hm, Hq⟩ | ⟨%Herr, #Hse, #Hcl⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m
    iframe Hm Hq
  · iright
    isplitl
    · ipureintro; exact ⟨Herr.1, Herr.2.2⟩
    · iunfold kvErr; iframe #; ipureintro; exact Herr.2.1

/-- **`Commit()` on a builder over a `*kv` over `conn` to a member with auth on** (as
`client_txn_any` at one member): a transaction a writing one of which has every permission of the
shape the permission cache decides (`kvShapeAll`), the member's committed index at least `c`, the
floor `F`, a lower bound `n` of the published auth index and the caller's update
(`txnUpdAtOn`: a writing one's told its grant), persistent or on a builder that sends a write at
most once; `nil` with the reply's `txnReplied` and the transaction's auth facts at the token of
some attempt's metadata (`txnAuthOn`), or an error. -/
theorem client_txn_on (tp api conn : Loc) (addr : GoString) (s : Loc) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (cid mid c : w64) (n : Nat) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (b : TxnBuild) (Q : KVState → IProp GF) (F : mvcc.Log)
    (hp : TxnModel.plain (txnWireOf b.model)) (hin : txnModelIn (txnWireOf b.model))
    (hsh : txn.txnReadonly (txnWireOf b.model) = false →
      ∀ tw : txn.TxnModelW, tw.toModel = txnWireOf b.model → kvShapeAll (irrTxn tw)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        txnObjAt tp [addr] ci cd b ∗ txnKvIs tp api ∗ kvObjAtC api conn [addr] ∗
        isGrpcRpcMd addr go!"/etcdserverpb.KV/Txn" (etcdTxnSpecOn s E ρ γr cid mid) ∗
        committedAtLeast γr c ∗ mvcc.idxCert E.γ.idx F ∗ auth.authPubLbM E.authMode n ∗
        (□ txnUpdAtOn s E ρ conn (GoInterface.ok ci) γr (txnWireOf b.model) Q ∨
          (txnWriteOnce tp [addr] ∗ txnUpdAtOn s E ρ conn (GoInterface.ok ci) γr (txnWireOf b.model) Q)) }}
      (App (Val (tp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"Commit"))
        (Val #()))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : TxnRespM, txnRespMsg resp m ∗
            txnReplied E ρ.rd γr c F (txnWireOf b.model) Q cid mid m ∗
            ∃ md, ⌜clientAttemptMd conn (GoInterface.ok ci) md⌝ ∗
              txnAuthOn s E ρ γr c n (auth.mdTokenOf md) (txnWireOf b.model)) ∨
          (⌜err ≠ GoInterface.nil ∧ resp = null⌝ ∗ kvErr err) }} := by
  iintro %Φ ⟨#Pc, Hobj, #Htk, #Hkv, #Hreg, #Hc, #HF, #Hn, Hnp⟩ HΦ
  have h : (iprop(committedAtLeast γr c ∗ mvcc.idxCert E.γ.idx F ∗ auth.authPubLbM E.authMode n) ∗
        txnUpdAtOn s E ρ conn (GoInterface.ok ci) γr (txnWireOf b.model) Q : IProp GF) ⊢
      attemptPre conn (GoInterface.ok ci) (etcdTxnSpecOn s E ρ γr cid mid) (txnWireOf b.model)
        (fun (m : TxnRespM) => iprop(txnReplied E ρ.rd γr c F (txnWireOf b.model) Q cid mid m ∗
          ∃ md, ⌜clientAttemptMd conn (GoInterface.ok ci) md⌝ ∗
            txnAuthOn s E ρ γr c n (auth.mdTokenOf md) (txnWireOf b.model))) := by
    iintro ⟨⟨#Hc, #HF, #Hn⟩, Hu⟩
    unfold attemptPre
    iintro %md %Hmd
    unfold etcdTxnSpecOn
    isplitl []
    · ipureintro; exact ⟨hp, hin, hsh⟩
    iexists Q
    isplitl [Hu]
    · iunfold txnUpdAtOn at Hu
      icases Hu with (%Hro | ⟨%Hrs, #Hr⟩ | ⟨%Hw, Hau⟩)
      · ileft; ipureintro; exact Hro
      · iright; ileft; iframe Hr; ipureintro; exact Hrs
      · iright; iright
        isplitr
        · ipureintro; exact Hw
        iapply clientOpAuOn_attempt s E ρ conn (GoInterface.ok ci) md _ Q Hmd $$ Hau
    iexists c, F, n
    iframe Hc HF Hn
    iintro %m Hm Ha
    simp only []
    iframe Hm
    iexists md
    iframe Ha
    ipureintro; exact Hmd
  iapply (v3.txn.wp_CommitG tp api conn [addr] ci cd b (etcdTxnSpecOn s E ρ γr cid mid)
    (fun m => iprop(txnReplied E ρ.rd γr c F (txnWireOf b.model) Q cid mid m ∗
      ∃ md, ⌜clientAttemptMd conn (GoInterface.ok ci) md⌝ ∗
        txnAuthOn s E ρ γr c n (auth.mdTokenOf md) (txnWireOf b.model)))) $$ [Hobj Hnp]
  · iframe Hobj
    iframe #
    iapply (txnReqPre_wand tp [addr] _ _ _ h)
    isplitl []
    · iframe #
    unfold txnReqPre
    icases Hnp with (#Hu | ⟨Ho, Hu⟩)
    · ileft
      imodintro
      inext
      iexact Hu
    · iright
      iunfold txnWriteOnce at Ho
      icases Ho with %Hnr
      isplitl []
      · ipureintro; exact Hnr
      inext
      iexact Hu
  inext
  iintro %resp %err Hout
  iapply HΦ
  iunfold txnCallOut at Hout
  icases Hout with (⟨%Herr, %m, Hm, Hq⟩ | ⟨%Herr, #Hse, #Hcl⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m
    iframe Hm Hq
  · iright
    isplitl
    · ipureintro; exact ⟨Herr.1, Herr.2.2⟩
    · iunfold kvErr; iframe #; ipureintro; exact Herr.2.1

end on

end client
end EtcdGrove
end Perennial
