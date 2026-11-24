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
clientAttemptMdI conn om md ∗ …`: the attempt's metadata is the context's outgoing metadata with
the client's API version, delivered by grpc on `conn`): a write's grant (`v3rpc.writeGrantOn`), a
read's check (`v3rpc.rangeAuthed`, `txnAuthOn`) at the lower bound `n` of the auth store's
published index the caller gives (`auth.authPubLbM`; `0` is free). What the token is (the
client's, after `Authenticate`) is the auth plan's item 2 (C1–C4, over `clientAttemptMdI`, a persistent `IProp` since phase 7's switch). A
write's update is told the same grant when it fires (`clientOpAuOn`, the auth-mode merge's 5a): at
a lower bound of the requested log the caller gives (`srvReqLogLb`; `[]` is free,
`clientOpAuOn_of_au1`).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.LeaseSpecs
public import Proof.go_etcd_io.etcd.client.v3.Results
public import Proof.go_etcd_io.etcd.client.v3.KVServiceOn
public import Proof.go_etcd_io.etcd.client.v3.LeaseGrantServed

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

/-- **`kv.Put(ctx, key, val, opts...)` through a `*kv` over `conn` to a member with auth on** (as
`client_put_any` at one member): etcd's `Put` with auth on registered at `addr`, the options `gs`
(auth-lease S4, D-j; the no-option form is `gs := []`) building a request that does not panic, of
lease `0` or at the revocable lease mode (`etcdPutSpecOn`'s filter), the floor `F` and the caller's
update told the put's grant (`clientOpAuOn`), persistent or on a client that sends a write at most
once; `nil` and the reply with `putReplied` and the put's grant at the token of some attempt's
metadata, or an error. -/
theorem client_put_on (api conn : Loc) (addr : GoString) (T : IProp GF) [Persistent T] (E : apply.AEnv GF)
    (ρ : ReqNames) (cid mid : w64) (ci : GoInterfaceOk) (om : GrpcMd) (cd : context.ContextDesc (IProp GF))
    (key val : GoString) (sl : GoSlice) (gs : List (OpFull → OpFull)) (Q : KVState → IProp GF)
    (F : mvcc.Log)
    (hsz : opSizeOk (opPutModel key val gs))
    (hpn : ¬ (opPutModel key val gs).putPanics)
    (ht : (opPutModel key val gs).t = W64 2)
    (hl : (putWireOf (opPutModel key val gs)).leaseID = W64 0 ∨ ρ.kv.lm = .revocable) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        kvObjAtC api conn [addr] ∗
        isGrpcRpcMd addr go!"/etcdserverpb.KV/Put" (etcdPutSpecOn T E ρ cid mid) ∗
        srvApi.kvLogLb E.γs F ∗ metadata.outMD ci om ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl gs ∗
        (□ clientOpAuOn T E ρ conn om (.put (putWireOf (opPutModel key val gs))) Q ∨
          (writeOnce api [addr] ∗
            clientOpAuOn T E ρ conn om (.put (putWireOf (opPutModel key val gs))) Q)) }}
      (App (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
          go!"Put")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : PutRespM, putRespMsg resp m ∗
            putReplied E ρ.rd F (putWireOf (opPutModel key val gs)) Q cid mid m ∗
            ∃ md, clientAttemptMdI conn om md ∗
              v3rpc.writeGrantOn T E ρ (auth.mdTokenOf md) (irrPut (putWireOf (opPutModel key val gs)))) ∨
          (⌜err ≠ GoInterface.nil ∧ resp = null⌝ ∗ kvErr err) }} := by
  iintro %Φ ⟨#Pc, #Hkv, #Hreg, #HF, #Hom, #Hctx', #Hce, #Hopts, Hau⟩ HΦ
  have Hpm : ¬ (opPutModel key val gs).putPanics ∧ (opPutModel key val gs).t = W64 2 := ⟨hpn, ht⟩
  iapply (v3.kv.wp_PutG api conn [addr] ci om cd key val sl gs (etcdPutSpecOn T E ρ cid mid)
    (fun m => iprop(putReplied E ρ.rd F (putWireOf (opPutModel key val gs)) Q cid mid m ∗
      ∃ md, clientAttemptMdI conn om md ∗
        v3rpc.writeGrantOn T E ρ (auth.mdTokenOf md) (irrPut (putWireOf (opPutModel key val gs)))))) $$ [Hau]
  · iframe #
    isplitl []
    · ipureintro; exact Hpm
    have h : (srvApi.kvLogLb E.γs F ∗
          clientOpAuOn T E ρ conn om (.put (putWireOf (opPutModel key val gs))) Q : IProp GF) ⊢
        attemptPre conn om (etcdPutSpecOn T E ρ cid mid)
          (putWireOf (opPutModel key val gs))
          (fun (m : PutRespM) => iprop(putReplied E ρ.rd F (putWireOf (opPutModel key val gs)) Q cid mid m ∗
            ∃ md, clientAttemptMdI conn om md ∗
              v3rpc.writeGrantOn T E ρ (auth.mdTokenOf md) (irrPut (putWireOf (opPutModel key val gs))))) := by
      iintro ⟨#HF, Hau⟩
      unfold attemptPre
      iintro %md #Hmd
      unfold etcdPutSpecOn etcdPutSpecOnW
      isplitr
      · imodintro; iintro %_; itrivial
      iexists F
      iframe HF
      iexists Q
      isplitr
      · ipureintro; exact hl
      isplitl [Hau]
      · iapply clientOpAuOn_attempt T E ρ conn om md _ Q $$ Hmd Hau
      iintro %m Hm Hg
      simp only []
      iframe Hm
      iexists md
      iframe Hg
      iexact Hmd
    isplitl [Hau]; rotate_left
    · ipureintro; exact hsz
    iapply (kvReqPre_wand api [addr] (srvApi.kvLogLb E.γs F) _ _ h)
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

/-- The no-option request: it does not panic, is a put, and is `putKeyOp key val` (lease `0`). -/
theorem opPutModel_nil_ok (key val : GoString) :
    ¬ (opPutModel key val []).putPanics ∧ (opPutModel key val []).t = W64 2 ∧
      putWireOf (opPutModel key val []) = putKeyOp key val := by
  refine ⟨?_, rfl, rfl⟩
  unfold opPutModel OpFull.putPanics opFold OpFull.putInit OpFull.newOp OpModel.zero
  simp

/-- **`client_put_on` with no option** (`gs := []`, lease `0`). -/
theorem client_put_on_nil (api conn : Loc) (addr : GoString) (T : IProp GF) [Persistent T] (E : apply.AEnv GF)
    (ρ : ReqNames) (cid mid : w64) (ci : GoInterfaceOk) (om : GrpcMd) (cd : context.ContextDesc (IProp GF))
    (key val : GoString) (sl : GoSlice) (Q : KVState → IProp GF) (F : mvcc.Log)
    (hsz : opSizeOk (opPutModel key val [])) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        kvObjAtC api conn [addr] ∗
        isGrpcRpcMd addr go!"/etcdserverpb.KV/Put" (etcdPutSpecOn T E ρ cid mid) ∗
        srvApi.kvLogLb E.γs F ∗ metadata.outMD ci om ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
        (□ clientOpAuOn T E ρ conn om (.put (putKeyOp key val)) Q ∨
          (writeOnce api [addr] ∗
            clientOpAuOn T E ρ conn om (.put (putKeyOp key val)) Q)) }}
      (App (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
          go!"Put")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : PutRespM, putRespMsg resp m ∗
            putReplied E ρ.rd F (putKeyOp key val) Q cid mid m ∗
            ∃ md, clientAttemptMdI conn om md ∗
              v3rpc.writeGrantOn T E ρ (auth.mdTokenOf md) (irrPut (putKeyOp key val))) ∨
          (⌜err ≠ GoInterface.nil ∧ resp = null⌝ ∗ kvErr err) }} := by
  obtain ⟨hpn, ht, hw⟩ := opPutModel_nil_ok key val
  rw [← hw]
  exact client_put_on api conn addr T E ρ cid mid ci om cd key val sl [] Q F hsz hpn ht
    (Or.inl (by rw [hw]; rfl))

/-- **`kv.Get(ctx, key, opts...)` through a `*kv` over `conn` to a member with auth on** (as
`client_range_any` at one member): etcd's `Range` with auth on registered at `addr`, the member's
committed index at least `c`, the floor `F`, a lower bound `n` of the published auth index and the
caller's read update, persistent; `R` back, and `nil` with the reply's `rangeReplyOk` and the
read's check at the token of some attempt's metadata, or an error. -/
theorem client_range_on (api conn : Loc) (addr : GoString) (T : IProp GF) [Persistent T] (E : apply.AEnv GF)
    (γr : ReadNames) (cid mid c : w64) (n : Nat) (ci : GoInterfaceOk) (om : GrpcMd)
    (cd : context.ContextDesc (IProp GF)) (key : GoString) (sl : GoSlice)
    (gs : List (OpFull → OpFull)) (R : IProp GF) (Q : KVState → IProp GF) (F : mvcc.Log)
    (hsz : opSizeOk (opGetModel key gs)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        kvObjAtC api conn [addr] ∗
        isGrpcRpcMd addr go!"/etcdserverpb.KV/Range" (etcdRangeSpecOn T E γr cid mid) ∗
        committedAtLeast γr c ∗ srvApi.kvLogLb E.γs F ∗ auth.authPubLbM E.authMode n ∗
        metadata.outMD ci om ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAtRes sl gs R ∗ R ∗
        sortNamesIf (opGetModel key gs).base.sortSet ∗
        ⌜¬ opGetPanics gs ∧ (opGetModel key gs).t = W64 1⌝ ∗
        □ (⌜Q = fun _ => iprop(True)⌝ ∨
          (⌜(rangeWireOf (opGetModel key gs)).base.serializable = false⌝ ∗ kvReadAu γr.kv Q)) }}
      (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
          go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); R ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ m : RangeRespM, rangeRespMsg resp m ∗
            rangeReplyOk E γr c F (rangeWireOf (opGetModel key gs)) cid mid Q m ∗
            ∃ md, clientAttemptMdI conn om md ∗
              v3rpc.rangeAuthed T E γr c n (auth.mdTokenOf md) (rangeWireOf (opGetModel key gs))) ∨
          (⌜err ≠ GoInterface.nil ∧ resp = null⌝ ∗ kvErr err)) }} := by
  iintro %Φ ⟨#Pc, #Hkv, #Hreg, #Hc, #HF, #Hn, #Hom, #Hctx', #Hce, Hopts, HR, Hsn, %Hg, #Hdq⟩ HΦ
  iapply wp_fupd
  iapply (v3.kv.wp_GetG api conn [addr] ci om cd key sl gs R (etcdRangeSpecOn T E γr cid mid)
    (fun m => iprop(rangeReplyOk E γr c F (rangeWireOf (opGetModel key gs)) cid mid Q m ∗
      ∃ md, clientAttemptMdI conn om md ∗
        v3rpc.rangeAuthed T E γr c n (auth.mdTokenOf md) (rangeWireOf (opGetModel key gs))))
    (fun _ => iprop(True)))
    $$ [Hopts HR Hsn]
  · iframe #
    iframe Hopts HR Hsn
    isplitl []
    · ipureintro; exact Hg
    isplitl []; rotate_left
    · ipureintro; exact hsz
    imodintro
    inext
    unfold attemptPre
    iintro %md #Hmd
    unfold etcdRangeSpecOn etcdRangeSpecOnW
    isplitr
    · imodintro; iintro %_; itrivial
    iexists c, F, Q, n
    iframe Hc HF Hn Hdq
    iintro %m Hm Ha
    simp only []
    iframe Hm
    iexists md
    iframe Ha
    iexact Hmd
  inext
  iintro %resp %err ⟨-, HR, Hout⟩
  imod rangeCallOut_persist _ _ _ $$ Hout with Hout
  imodintro
  iapply HΦ
  iframe HR
  iunfold rangeCallOutP at Hout
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
theorem client_delete_on (api conn : Loc) (addr : GoString) (T : IProp GF) [Persistent T] (E : apply.AEnv GF)
    (ρ : ReqNames) (cid mid : w64) (ci : GoInterfaceOk) (om : GrpcMd) (cd : context.ContextDesc (IProp GF))
    (key : GoString) (sl : GoSlice) (Q : KVState → IProp GF) (F : mvcc.Log) (hk : key ≠ [])
    (hsz : opSizeOk (opDeleteModel key [])) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        kvObjAtC api conn [addr] ∗
        isGrpcRpcMd addr go!"/etcdserverpb.KV/DeleteRange" (etcdDeleteSpecOn T E ρ cid mid) ∗
        srvApi.kvLogLb E.γs F ∗ metadata.outMD ci om ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
        (□ clientOpAuOn T E ρ conn om (.deleteRange (txn.deleteOpOf key [] false)) Q ∨
          (writeOnce api [addr] ∗
            clientOpAuOn T E ρ conn om
              (.deleteRange (txn.deleteOpOf key [] false)) Q)) }}
      (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
          go!"Delete")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : DelRespM, delRespMsg resp m ∗
            deleteReplied E ρ.rd F (txn.deleteOpOf key [] false) Q cid mid m ∗
            ∃ md, clientAttemptMdI conn om md ∗
              v3rpc.writeGrantOn T E ρ (auth.mdTokenOf md)
                (irrDeleteRange (txn.deleteOpOf key [] false))) ∨
          (⌜err ≠ GoInterface.nil ∧ resp = null⌝ ∗ kvErr err) }} := by
  iintro %Φ ⟨#Pc, #Hkv, #Hreg, #HF, #Hom, #Hctx', #Hce, #Hopts, Hau⟩ HΦ
  have hw : deleteWireOf (opDeleteModel key []) = txn.deleteOpOf key [] false := by
    simp [op_simps, deleteWireOf, txn.deleteOpOf]
  iapply (v3.kv.wp_DeleteG api conn [addr] ci om cd key sl [] (etcdDeleteSpecOn T E ρ cid mid)
    (fun m => iprop(deleteReplied E ρ.rd F (txn.deleteOpOf key [] false) Q cid mid m ∗
      ∃ md, clientAttemptMdI conn om md ∗
        v3rpc.writeGrantOn T E ρ (auth.mdTokenOf md)
          (irrDeleteRange (txn.deleteOpOf key [] false))))) $$ [Hau]
  · iframe #
    isplitl []
    · ipureintro
      refine ⟨?_, rfl⟩
      simp [op_simps, opDeletePanics, opGetPanics, OpFull.deletePanics]
    rw [hw]
    have h : (srvApi.kvLogLb E.γs F ∗
          clientOpAuOn T E ρ conn om (.deleteRange (txn.deleteOpOf key [] false)) Q :
          IProp GF) ⊢
        attemptPre conn om (etcdDeleteSpecOn T E ρ cid mid)
          (txn.deleteOpOf key [] false)
          (fun (m : DelRespM) =>
            iprop(deleteReplied E ρ.rd F (txn.deleteOpOf key [] false) Q cid mid m ∗
            ∃ md, clientAttemptMdI conn om md ∗
              v3rpc.writeGrantOn T E ρ (auth.mdTokenOf md)
                (irrDeleteRange (txn.deleteOpOf key [] false)))) := by
      iintro ⟨#HF, Hau⟩
      unfold attemptPre
      iintro %md #Hmd
      unfold etcdDeleteSpecOn etcdDeleteSpecOnW
      isplitr
      · imodintro; iintro %_; itrivial
      isplitl []
      · ipureintro; exact ⟨hk, Or.inl rfl⟩
      iexists F
      iframe HF
      iexists Q
      isplitr
      · ipureintro; simp [txn.deleteOpOf]
      isplitl [Hau]
      · iapply clientOpAuOn_attempt T E ρ conn om md _ Q $$ Hmd Hau
      iintro %m Hm Hg
      simp only []
      iframe Hm
      iexists md
      iframe Hg
      iexact Hmd
    isplitl [Hau]; rotate_left
    · ipureintro; exact hsz
    iapply (kvReqPre_wand api [addr] (srvApi.kvLogLb E.γs F) _ _ h)
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
`client_txn_any` at one member, nested transactions included: `notes/txn-nested.md`): a
transaction, read-only within the model (`txnModelIn`), a writing one with every permission of the
shape the permission cache decides (`kvShapeAll`), the member's committed index at least `c`, the
floor `F`, a lower bound `n` of the published auth index and the caller's update
(`txnUpdAtOn`: a writing one's told its grant), persistent or on a builder that sends a write at
most once; `nil` with the reply's `txnReplied` and the transaction's auth facts at the token of
some attempt's metadata (`txnAuthOn`), or an error. -/
theorem client_txn_on (tp api conn : Loc) (addr : GoString) (T : IProp GF) [Persistent T] (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (cid mid c : w64) (n : Nat) (ci : GoInterfaceOk) (om : GrpcMd)
    (cd : context.ContextDesc (IProp GF)) (b : TxnBuild) (Q : KVState → IProp GF) (F : mvcc.Log)
    (hin : txn.txnReadonly (txnWireOf b.model) = true → txnModelIn (txnWireOf b.model))
    (hsz : txnSizeOk (txnWireOf b.model))
    (hsh : txn.txnReadonly (txnWireOf b.model) = false →
      ∀ tw : txn.TxnModelW, tw.toModel = txnWireOf b.model → kvShapeAll (irrTxn tw)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        txnObjAt tp [addr] ci cd b ∗ metadata.outMD ci om ∗ txnKvIs tp api ∗ kvObjAtC api conn [addr] ∗
        isGrpcRpcMd addr go!"/etcdserverpb.KV/Txn" (etcdTxnSpecOn T E ρ γr cid mid) ∗
        committedAtLeast γr c ∗ srvApi.kvLogLb E.γs F ∗ auth.authPubLbM E.authMode n ∗
        (□ txnUpdAtOn T E ρ conn om γr (txnWireOf b.model) Q ∨
          (txnWriteOnce tp [addr] ∗ txnUpdAtOn T E ρ conn om γr (txnWireOf b.model) Q)) }}
      (App (Val (tp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"Commit"))
        (Val #()))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : TxnRespM, txnRespMsg resp m ∗
            txnReplied E ρ.rd γr c F (txnWireOf b.model) Q cid mid m ∗
            ∃ md, clientAttemptMdI conn om md ∗
              txnAuthOn T E ρ γr c n (auth.mdTokenOf md) (txnWireOf b.model)) ∨
          (⌜err ≠ GoInterface.nil ∧ resp = null⌝ ∗ kvErr err) }} := by
  iintro %Φ ⟨#Pc, Hobj, #Hom, #Htk, #Hkv, #Hreg, #Hc, #HF, #Hn, Hnp⟩ HΦ
  have h : (iprop(committedAtLeast γr c ∗ srvApi.kvLogLb E.γs F ∗ auth.authPubLbM E.authMode n) ∗
        txnUpdAtOn T E ρ conn om γr (txnWireOf b.model) Q : IProp GF) ⊢
      attemptPre conn om (etcdTxnSpecOn T E ρ γr cid mid) (txnWireOf b.model)
        (fun (m : TxnRespM) => iprop(txnReplied E ρ.rd γr c F (txnWireOf b.model) Q cid mid m ∗
          ∃ md, clientAttemptMdI conn om md ∗
            txnAuthOn T E ρ γr c n (auth.mdTokenOf md) (txnWireOf b.model))) := by
    iintro ⟨⟨#Hc, #HF, #Hn⟩, Hu⟩
    unfold attemptPre
    iintro %md #Hmd
    unfold etcdTxnSpecOn etcdTxnSpecOnW
    isplitr
    · imodintro; iintro %_; itrivial
    isplitl []
    · ipureintro; exact ⟨hin, hsh⟩
    iexists Q
    isplitl [Hu]
    · iunfold txnUpdAtOn at Hu
      icases Hu with (%Hro | ⟨%Hrs, #Hr⟩ | ⟨%Hw, Hau⟩)
      · ileft; ipureintro; exact Hro
      · iright; ileft; iframe Hr; ipureintro; exact Hrs
      · iright; iright
        isplitr
        · ipureintro; exact Hw
        iapply clientOpAuOn_attempt T E ρ conn om md _ Q $$ Hmd Hau
    iexists c, F, n
    iframe Hc HF Hn
    iintro %m Hm Ha
    simp only []
    iframe Hm
    iexists md
    iframe Ha
    iexact Hmd
  iapply (v3.txn.wp_CommitG tp api conn [addr] ci om cd b (etcdTxnSpecOn T E ρ γr cid mid)
    (fun m => iprop(txnReplied E ρ.rd γr c F (txnWireOf b.model) Q cid mid m ∗
      ∃ md, clientAttemptMdI conn om md ∗
        txnAuthOn T E ρ γr c n (auth.mdTokenOf md) (txnWireOf b.model)))) $$ [Hobj Hnp]
  · iframe Hobj
    iframe #
    isplitl [Hnp]; rotate_left
    · ipureintro; exact hsz
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

section leaseOn
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **`l.Grant(ctx, ttl)` on the client's `*lessor` over `conn` to a member with auth on** (auth-lease S4,
Freeze §3.1, F3; `client_put_on`'s shape): etcd's `LeaseGrant` with auth on registered at `addr`, the
caller's lower bound `n` of the published auth index, and, for every id the lease may get, the caller's
update told the grant (`clientOpAuOn`, persistent: the call may be retried); `nil` with the response's
fields, its lease id not `NoLease`, its revision reached, the lease live in the lessor's history with the
request's TTL, and at the token of some attempt's metadata the caller's result (`leaseGrantResT`) and
`requireAuthInfo`'s check relative to `n` (`leaseCheckFrom`); or an error. -/
theorem client_lease_grant_on (l conn : Loc) (addr : GoString) (T : IProp GF) [Persistent T] (E : apply.AEnv GF) (ρ : ReqNames) (γl : GName)
    (ci : GoInterfaceOk) (om : GrpcMd) (cd : context.ContextDesc (IProp GF)) (n : Nat) (ttl : w64)
    (Q : w64 → KVState → IProp GF) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ lessorRemoteAtC l conn [addr] ∗ auth.authPubLbM E.authMode n ∗
      isGrpcRpcMd addr go!"/etcdserverpb.Lease/LeaseGrant" (etcdLeaseGrantSpecOn T E ρ γl) ∗
      metadata.outMD ci om ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗
      □ (∀ id : w64, clientOpAuOn T E ρ conn om (.leaseGrant id ttl) (Q id)) }}
    (App (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"Grant"))
      (Val #(GoInterface.ok ci))) (Val #ttl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (m : LeaseGrantRespM) (h : Loc),
        structFieldRef go_etcd_io.etcd.client.v3.LeaseGrantResponse go!"ResponseHeader" resp ↦□ h ∗
        hdrFull h m.hdr ∗
        structFieldRef go_etcd_io.etcd.client.v3.LeaseGrantResponse go!"ID" resp ↦□ m.id ∗
        structFieldRef go_etcd_io.etcd.client.v3.LeaseGrantResponse go!"TTL" resp ↦□ m.ttl ∗
        ⌜m.id ≠ W64 0⌝ ∗
        etcdReached (EM := v3rpc.etcdModelOfServer E ρ.rd E.authOn) m.hdr.revision ∗
        (∃ (i : Nat) (lo : Loc), lease.leaseLiveFrom γl i m.id lo ∗ lease.leaseReqIs γl m.id ttl) ∗
        ∃ md, clientAttemptMdI conn om md ∗
          v3rpc.leaseGrantResT E.authOn T E ρ (auth.mdTokenOf md) ttl m.id Q ∗
          leaseCheckFrom T E (auth.mdTokenOf md) n (fun _ => iprop(True))) ∨
      (⌜err ≠ GoInterface.nil ∧ clientErr err ∧ resp = null⌝ ∗
        go_etcd_io.etcd.cache.v3.statusErrOk err) }} := by
  iintro %Φ ⟨#Pc, #Hrem, #Hn, #Hreg, #Hom, #Hctx, #Hce, #Hau⟩ HΦ
  iapply (v3.lessor.wp_Grant l conn [addr] (etcdLeaseGrantSpecOn T E ρ γl)
    (fun m => iprop(⌜m.id ≠ W64 0⌝ ∗
        etcdReached (EM := v3rpc.etcdModelOfServer E ρ.rd E.authOn) m.hdr.revision ∗
        (∃ (i : Nat) (lo : Loc), lease.leaseLiveFrom γl i m.id lo ∗ lease.leaseReqIs γl m.id ttl) ∗
        ∃ md, clientAttemptMdI conn om md ∗
          v3rpc.leaseGrantResT E.authOn T E ρ (auth.mdTokenOf md) ttl m.id Q ∗
          leaseCheckFrom T E (auth.mdTokenOf md) n (fun _ => iprop(True))))
    ci om cd ttl) $$ [] HΦ
  iframe Pc Hrem Hreg Hom Hctx Hce
  iintro !>
  inext
  unfold attemptPre
  iintro %md #Hmd
  unfold etcdLeaseGrantSpecOn etcdLeaseGrantSpecOnW
  isplitr
  · iintro !> %_; itrivial
  isplitr
  · ipureintro; rfl
  iexists n
  iframe Hn
  iexists Q
  isplitr
  · cases hon : E.authOn
    · iapply leaseGrantPermitM_false
    · simp only [leaseGrantPermitM]
      iintro %id
      ihave Hau1 := Hau $$ %id
      ihave H := clientOpAuOn_attempt T E ρ conn om md _ (Q id) $$ Hmd Hau1
      iapply kvOpAuOn_leaseGrant $$ H
  iintro %m %Hid #Hre Hlive Hres #Hck
  isplitr
  · ipureintro; exact Hid
  iframe Hre
  isplitl [Hlive]
  · iexact Hlive
  iexists md
  iframe Hres Hck
  iexact Hmd

/-- **`l.Revoke(ctx, id)` on the client's `*lessor` over `conn` to a member with auth on** (auth-lease
S4, Freeze §3.2; as `client_lease_grant_on`). -/
theorem client_lease_revoke_on (l conn : Loc) (addr : GoString) (T : IProp GF) [Persistent T] (E : apply.AEnv GF) (ρ : ReqNames)
    (ci : GoInterfaceOk) (om : GrpcMd) (cd : context.ContextDesc (IProp GF)) (n : Nat) (id : w64)
    (Q : KVState → IProp GF) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ lessorRemoteAtC l conn [addr] ∗ auth.authPubLbM E.authMode n ∗
      isGrpcRpcMd addr go!"/etcdserverpb.Lease/LeaseRevoke" (etcdLeaseRevokeSpecOn T E ρ) ∗
      metadata.outMD ci om ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗
      □ clientOpAuOn T E ρ conn om (.leaseRevoke id) Q }}
    (App (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"Revoke"))
      (Val #(GoInterface.ok ci))) (Val #id))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ m : LeaseRevokeRespM, leaseRevokeRespMsg resp m ∗
        etcdReached (EM := v3rpc.etcdModelOfServer E ρ.rd E.authOn) m.hdr.revision ∗
        ∃ md, clientAttemptMdI conn om md ∗
          v3rpc.leaseRevokeResT E.authOn T E ρ (auth.mdTokenOf md) id Q ∗
          leaseCheckFrom T E (auth.mdTokenOf md) n (fun _ => iprop(True))) ∨
      (⌜err ≠ GoInterface.nil ∧ clientErr err ∧ resp = null⌝ ∗
        go_etcd_io.etcd.cache.v3.statusErrOk err) }} := by
  iintro %Φ ⟨#Pc, #Hrem, #Hn, #Hreg, #Hom, #Hctx, #Hce, #Hau⟩ HΦ
  iapply (v3.lessor.wp_Revoke l conn [addr] (etcdLeaseRevokeSpecOn T E ρ)
    (fun m => iprop(etcdReached (EM := v3rpc.etcdModelOfServer E ρ.rd E.authOn) m.hdr.revision ∗
        ∃ md, clientAttemptMdI conn om md ∗
          v3rpc.leaseRevokeResT E.authOn T E ρ (auth.mdTokenOf md) id Q ∗
          leaseCheckFrom T E (auth.mdTokenOf md) n (fun _ => iprop(True))))
    ci om cd id) $$ [] HΦ
  iframe Pc Hrem Hreg Hom Hctx Hce
  iintro !>
  inext
  unfold attemptPre
  iintro %md #Hmd
  unfold etcdLeaseRevokeSpecOn etcdLeaseRevokeSpecOnW
  isplitr
  · iintro !> %_; itrivial
  iexists n
  iframe Hn
  iexists Q
  isplitr
  · cases hon : E.authOn
    · iapply leaseRevokePermitM_false
    · simp only [leaseRevokePermitM]
      ihave H := clientOpAuOn_attempt T E ρ conn om md _ Q $$ Hmd Hau
      iapply kvOpAuOn_leaseRevoke $$ H
  iintro %m #Hre Hres #Hck
  isplitr
  · iexact Hre
  iexists md
  iframe Hres Hck
  iexact Hmd

end leaseOn

end client
end EtcdGrove
end Perennial
