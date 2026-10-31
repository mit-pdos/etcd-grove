/-
**`cli.Put` through a `New`'s client to authkv's member, auth on** (`notes/authkv-main-plan.md`,
S5; 2026-10-29). Lean-first (no Rocq counterpart).

`(*Client).Put` calls its `KV` field's `Put`. With the field a `*kv` over the client's connection
(`clientTokAt`, what `New` gives), that is `client.client_put_on` at the member's `Put` registered
with etcd's spec with auth on. E3zc left the `*Client` wrappers for the auth-on calls undone
(`notes/decisions.md`, "E3zc of the auth plan", "Not yet"). This is the one `SetUp` needs, kept
in authkv until the client package has them.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.ResultsOn
public import Proof.go_etcd_io.etcd.client.v3.InvClientAuth
public import Proof.go_etcd_io.etcd.client.v3.InvClientNewResult

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver client

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **`cli.Put(ctx, key, val)` through a client whose `KV` is a `*kv` over `conn`** (`clientTokAt`'s
parts) to a member with auth on: `client_put_on` through the `*Client` method. -/
theorem client_Put_on (cl api conn : Loc) (addr : GoString) (s : Loc) (E : apply.AEnv GF)
    (ρ : ReqNames) (cid mid : w64) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key val : GoString) (sl : GoSlice) (Q : KVState → IProp GF) (F : mvcc.Log)
    (hsz : opSizeOk (opPutModel key val [])) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        structFieldRef go_etcd_io.etcd.client.v3.Client go!"KV" cl ↦□
          (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty) #api :
            GoInterface) ∗
        kvObjAtC api conn [addr] ∗
        isGrpcRpcMd addr go!"/etcdserverpb.KV/Put" (etcdPutSpecOn s E ρ cid mid) ∗
        mvcc.idxCert E.γ.idx F ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
        □ kvOpAu1 ρ.rd.kv (.put (putKeyOp key val)) Q }}
      (App (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Put")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : PutRespM, putRespMsg resp m ∗
            putReplied E ρ.rd F (putKeyOp key val) Q cid mid m ∗
            ∃ md, ⌜clientAttemptMd conn (GoInterface.ok ci) md⌝ ∗
              v3rpc.writeGrantOn s E ρ (auth.mdTokenOf md) (irrPut (putKeyOp key val))) ∨
          (⌜err ≠ GoInterface.nil⌝ ∗ kvErr err) }} := by
  iintro %Φ ⟨#Pc, #Hkvf, #Hkv, #Hreg, #HF, #Hctx, #Hce, #Hopts, #Hau⟩ HΦ
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Put_unfold.method_unfold]
  wp_pures
  wp_auto
  imod srvReqLogLb_nil (GF := GF) ρ.raft with #H0
  wp_apply (client_put_on api conn addr s E ρ cid mid ci cd key val sl Q F hsz) $$ [] as %resp %err Hout
  · iframe #
    ileft
    imodintro
    unfold clientOpAuOn
    iexists []
    iframe H0
    unfold kvOpAu1
    iapply kvAu1_G $$ Hau
  iapply HΦ
  icases Hout with (⟨%Herr, Hr⟩ | ⟨%Herr, #Hke⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexact Hr
  · iright
    isplitl
    · ipureintro; exact Herr.1
    · iexact Hke

/-- **`cli.Put(ctx, key, val)` with the update told the put's grant** (Work's puts, F-C1's second
`Put` spec): `client_put_on`'s persistent update through the `*Client` method, so that the caller's
update (`akHist_writeAu`) sees the grant. -/
theorem client_Put_onG (cl api conn : Loc) (addr : GoString) (s : Loc) (E : apply.AEnv GF)
    (ρ : ReqNames) (cid mid : w64) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key val : GoString) (sl : GoSlice) (Q : KVState → IProp GF) (F : mvcc.Log)
    (hsz : opSizeOk (opPutModel key val [])) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        structFieldRef go_etcd_io.etcd.client.v3.Client go!"KV" cl ↦□
          (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty) #api :
            GoInterface) ∗
        kvObjAtC api conn [addr] ∗
        isGrpcRpcMd addr go!"/etcdserverpb.KV/Put" (etcdPutSpecOn s E ρ cid mid) ∗
        mvcc.idxCert E.γ.idx F ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
        □ clientOpAuOn s E ρ conn (GoInterface.ok ci) (.put (putKeyOp key val)) Q }}
      (App (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Put")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : PutRespM, putRespMsg resp m ∗
            putReplied E ρ.rd F (putKeyOp key val) Q cid mid m ∗
            ∃ md, ⌜clientAttemptMd conn (GoInterface.ok ci) md⌝ ∗
              v3rpc.writeGrantOn s E ρ (auth.mdTokenOf md) (irrPut (putKeyOp key val))) ∨
          (⌜err ≠ GoInterface.nil⌝ ∗ kvErr err) }} := by
  iintro %Φ ⟨#Pc, #Hkvf, #Hkv, #Hreg, #HF, #Hctx, #Hce, #Hopts, #Hau⟩ HΦ
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Put_unfold.method_unfold]
  wp_pures
  wp_auto
  wp_apply (client_put_on api conn addr s E ρ cid mid ci cd key val sl Q F hsz) $$ [] as %resp %err Hout
  · iframe #
  iapply HΦ
  icases Hout with (⟨%Herr, Hr⟩ | ⟨%Herr, #Hke⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexact Hr
  · iright
    isplitl
    · ipureintro; exact Herr.1
    · iexact Hke

/-- **`cli.Get(ctx, key, opts...)` through a client whose `KV` is a `*kv` over `conn`** to a
member with auth on: `client_range_on` through the `*Client` method. -/
theorem client_Get_on (cl api conn : Loc) (addr : GoString) (s : Loc) (E : apply.AEnv GF)
    (γr : ReadNames) (cid mid c : w64) (n : Nat) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key : GoString) (sl : GoSlice)
    (gs : List (OpFull → OpFull)) (R : IProp GF) (Q : KVState → IProp GF) (F : mvcc.Log)
    (hsz : opSizeOk (opGetModel key gs)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        structFieldRef go_etcd_io.etcd.client.v3.Client go!"KV" cl ↦□
          (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty) #api :
            GoInterface) ∗
        kvObjAtC api conn [addr] ∗
        isGrpcRpcMd addr go!"/etcdserverpb.KV/Range" (etcdRangeSpecOn s E γr cid mid) ∗
        committedAtLeast γr c ∗ mvcc.idxCert E.γ.idx F ∗ auth.authPubLbM E.authMode n ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAtRes sl gs R ∗ R ∗
        sortNamesIf (opGetModel key gs).base.sortSet ∗
        ⌜¬ opGetPanics gs ∧ (opGetModel key gs).t = W64 1⌝ ∗
        □ (⌜Q = fun _ => iprop(True)⌝ ∨
          (⌜(rangeWireOf (opGetModel key gs)).base.serializable = false⌝ ∗ kvReadAu γr.kv Q)) }}
      (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); R ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ m : RangeRespM, rangeRespMsg resp m ∗
            rangeReplyOk E γr c F (rangeWireOf (opGetModel key gs)) cid mid Q m ∗
            ∃ md, ⌜clientAttemptMd conn (GoInterface.ok ci) md⌝ ∗
              v3rpc.rangeAuthed s E γr c n (auth.mdTokenOf md) (rangeWireOf (opGetModel key gs))) ∨
          (⌜err ≠ GoInterface.nil ∧ resp = null⌝ ∗ kvErr err)) }} := by
  iintro %Φ ⟨#Pc, #Hkvf, #Hkv, #Hreg, #Hc, #HF, #Hn, #Hctx, #Hce, Hopts, HR, Hsn, %Hg, #Hdq⟩ HΦ
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Get_unfold.method_unfold]
  wp_pures
  wp_auto
  wp_apply (client_range_on api conn addr s E γr cid mid c n ci cd key sl gs R Q F hsz)
    $$ [Hopts HR Hsn] as %resp %err Hout
  · iframe #
    iframe Hopts HR Hsn
    ipureintro; exact Hg
  iapply HΦ
  iexact Hout

/-- **`cli.Delete(ctx, key)` through a client whose `KV` is a `*kv` over `conn`** to a member with
auth on, the update persistent and told the delete's grant: `client_delete_on` through the
`*Client` method. -/
theorem client_Delete_on (cl api conn : Loc) (addr : GoString) (s : Loc) (E : apply.AEnv GF)
    (ρ : ReqNames) (cid mid : w64) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key : GoString) (sl : GoSlice) (Q : KVState → IProp GF) (F : mvcc.Log) (hk : key ≠ [])
    (hsz : opSizeOk (opDeleteModel key [])) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        structFieldRef go_etcd_io.etcd.client.v3.Client go!"KV" cl ↦□
          (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty) #api :
            GoInterface) ∗
        kvObjAtC api conn [addr] ∗
        isGrpcRpcMd addr go!"/etcdserverpb.KV/DeleteRange" (etcdDeleteSpecOn s E ρ cid mid) ∗
        mvcc.idxCert E.γ.idx F ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
        □ clientOpAuOn s E ρ conn (GoInterface.ok ci) (.deleteRange (txn.deleteOpOf key [] false)) Q }}
      (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Delete")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : DelRespM, delRespMsg resp m ∗
            deleteReplied E ρ.rd F (txn.deleteOpOf key [] false) Q cid mid m ∗
            ∃ md, ⌜clientAttemptMd conn (GoInterface.ok ci) md⌝ ∗
              v3rpc.writeGrantOn s E ρ (auth.mdTokenOf md)
                (irrDeleteRange (txn.deleteOpOf key [] false))) ∨
          (⌜err ≠ GoInterface.nil ∧ resp = null⌝ ∗ kvErr err) }} := by
  iintro %Φ ⟨#Pc, #Hkvf, #Hkv, #Hreg, #HF, #Hctx, #Hce, #Hopts, #Hau⟩ HΦ
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Delete_unfold.method_unfold]
  wp_pures
  wp_auto
  wp_apply (client_delete_on api conn addr s E ρ cid mid ci cd key sl Q F hk hsz) $$ []
    as %resp %err Hout
  · iframe #
  iapply HΦ
  iexact Hout

/-- **`cli.Txn(ctx)` through a client whose `KV` is a `*kv` over `conn`**: the empty builder over
that `*kv` (`txnKvIs`), what `client_txn_on` takes. -/
theorem client_Txn_on (cl api conn : Loc) (addr : GoString) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        structFieldRef go_etcd_io.etcd.client.v3.Client go!"KV" cl ↦□
          (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty) #api :
            GoInterface) ∗
        kvObjAtC api conn [addr] ∗ ctxOk ci cd ∗ ctxErrClient ci cd }}
      (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Txn")) (Val #(GoInterface.ok ci)))
    {{ (t : GoInterface), RET #t; ∃ tp : Loc,
        ⌜t = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty) #tp⌝ ∗
        txnObjAt tp [addr] ci cd TxnBuild.empty ∗ txnKvIs tp api }} := by
  iintro %Φ ⟨#Pc, #Hkvf, #Hkv, #Hctx, #Hce⟩ HΦ
  ihave #Hkv' : kvObjAt api [addr] $$ []
  · iapply (kvObjAt_conn api [addr]).2
    iexists conn
    iexact Hkv
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Txn_unfold.method_unfold]
  wp_pures
  wp_auto
  wp_apply (v3.kv.wp_Txn api [addr] ci cd) as %t ⟨%tp, %Ht, Hobj, #Hkt⟩
  · iframe #
  iapply HΦ
  iexists tp
  iframe Hobj Hkt
  ipureintro; exact Ht

end proof

end authkv
end EtcdGrove
end Perennial
