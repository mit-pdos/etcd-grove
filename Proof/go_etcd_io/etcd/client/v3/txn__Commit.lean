/-
Proof of `Spec/go_etcd_io/etcd/client/v3/txn__Commit.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.txn__Commit
public import Spec.go_etcd_io.etcd.client.v3.retryKVClient__Txn
public import Spec.go_etcd_io.etcd.client.v3.ContextError
public import Perennial.Proof.sync.Link
public import Proof.go_etcd_io.etcd.client.v3.KVMembers

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 client

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `t.Commit()` for any spec `Spec` registered for `Txn` at the connection (the transport's terms,
as the retry client's spec takes them; `txn.Commit.wp_proof` instantiates it with the members'
spec, `kvTxnSpec`): `txnCallOut`. -/
theorem txn.Commit.wp_generic (wp_retry_Txn : retryKVClient.Txn.spec (GF := GF) (hG := hG))
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG)) :
    ∀ (tp : Loc) (addr : List GoString) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
      (b : TxnBuild) (Spec : GrpcSpec (GF := GF) pbTxnRequest pbTxnResponse)
      (Q : TxnRespM → IProp GF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ txnObjAt tp addr ci cd b ∗
        isGrpcRpcs addr go!"/etcdserverpb.KV/Txn" Spec ∗
        txnReqPre tp addr (Spec (txnWireOf b.model) Q) }}
      (App (Val (tp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"Commit"))
        (Val #()))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); txnCallOut Q resp err }} := by
  intro tp addr ci cd b Spec Q
  wp_start as ⟨Htx, #Hrpc, Hrun⟩
  iunfold txnObjAt at Htx
  icases Htx with ⟨%Htpn, %api, %cosl, %csl, %ssl, %fsl, %cps, %sps, %fps, %iw, #Hkvf, #Hkv, #Hctxf,
    #Hctx, #Hce, #Hmu, Hcif, Hcthen, Hcelse, Hiw, Hcmps, Hcsl, Hccap, #Hcpa, Hsus, Hssl, Hscap,
    #Hspa, Hfas, Hfsl, Hfcap, #Hfpa, #Hcof, #Hco⟩
  ihave #Hkv' := Hkv
  iunfold kvObjAt at Hkv'
  icases Hkv' with ⟨%rkv, %conn, %sl, #Hremote, #Hrkv, #Hconn, #Hcopts, #Hco'⟩
  iunfold callOptsAt at Hco
  icases Hco with ⟨%vs, #Hvs, %Hcap, #Hok, %Hsc⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, -⟩
  ipersist Hcsl; ipersist Hssl; ipersist Hfsl
  ihave Hrun' : reqPre conn go!"/etcdserverpb.KV/Txn" addr vs (Spec (txnWireOf b.model) Q) $$ [Hrun]
  · iapply kvReqPre_conn api rkv conn go!"/etcdserverpb.KV/Txn" ⟨go!"Txn", rfl⟩ addr vs _ Hsc $$ [Hrun]
    iframe Hremote Hrkv
    iapply txnReqPre_kv tp api addr $$ [Hrun]
    iframe Hrun
    unfold txnKvIs; iexact Hkvf
  wp_apply wp_retry_Txn rkv conn addr Spec Q ci cd _ _ (txnWireOf b.model) cosl vs $$ [«$r0» Hrun']
    as %resp %err ⟨-, Hres⟩
  · iframe #
    iframe
    unfold txnReqAt txnWireOf
    iexists cps, sps, fps
    iframe #
  iunfold txnCallOut at Hres
  icases Hres with (⟨%Herr, Hm⟩ | ⟨%Herr, #Hse, #Hcl⟩)
  · subst Herr
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked]
    · inext; itrivial
    iapply HΦ
    unfold txnCallOut
    ileft
    iframe Hm
    ipureintro; rfl
  · obtain ⟨Hne, Hce', Hnull⟩ := Herr
    cases err with
    | nil => exact absurd rfl Hne
    | ok ei =>
      wp_auto
      wp_apply wp_ContextError ci cd (GoInterface.ok ei) $$ [$Hse] as %err' ⟨%Herr', #Hse', #Hclw⟩
      · iframe #; ipureintro; exact fun _ => Hce'
      ihave #Hcl' := Hclw $$ Hcl
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked]
      · inext; itrivial
      iapply HΦ
      unfold txnCallOut
      iright
      iframe #
      ipureintro
      exact ⟨(Herr'.2 (by simp)).1, (Herr'.2 (by simp)).2, rfl⟩

/-- `t.Commit()` over a `*kv` of the members (D43): `txn.Commit.wp_generic` at the members' spec,
registered by their registrations (`kvRegs_rpcTxn`) and met by the caller's side (`txnSpec_of`). -/
theorem txn.Commit.wp_members (wp_retry_Txn : retryKVClient.Txn.spec (GF := GF) (hG := hG))
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG)) :
    txn.Commit.specM (GF := GF) (hG := hG) := by
  intro tp ms ci cd b c F Q
  iintro %Φ ⟨#Pc, Hobj, #Hregs, %Hp, #Hk, Hu⟩ HΦ
  iapply (txn.Commit.wp_generic wp_retry_Txn wp_ContextError tp (ms.map SrvAt.addr) ci cd b
    (kvTxnSpec ms) (txnAns ms c F (txnWireOf b.model) Q)) $$ [Hobj Hu] HΦ
  iframe #
  iframe Hobj
  isplitl []
  · iapply (kvRegs_rpcTxn ms) $$ Hregs
  iapply (txnReqPre_wand tp (ms.map SrvAt.addr) (knownAt ms c F) _ _
    (txnSpec_of ms c F (txnWireOf b.model) Q (txnWireOf_plain _ Hp.1) Hp.2))
  iframe Hk Hu

/-- `t.Commit()` on a builder over a `*kv` of etcd's KV `γ` (D43): `txn.Commit.wp_members` at its
hidden members (the builder's connection the `*kv`'s, `txnObjAt_conn`), from the floor `[]` and
the committed index `0` (`isKv`'s `srvStart`) and the caller's update at each member's names
(`txnUpd_of`); the reply's fields as the state's (`txnAns_st`). -/
theorem txn.Commit.wp_proof (wp_retry_Txn : retryKVClient.Txn.spec (GF := GF) (hG := hG))
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG)) :
    txn.Commit.spec (GF := GF) (hG := hG) := by
  intro tp addr api γ dup ci cd b Q
  iintro %Φ ⟨#Pc, Hobj, #Hkt, #Hkv, %Hp, Hu⟩ HΦ
  ihave Hu := txnAu_upd dup γ (txnWireOf b.model) Q $$ Hu
  ihave ⟨%Hz, Hu⟩ := writeUpd_txn_nz (!dup) γ (txnWireOf b.model) Q $$ Hu
  iunfold isKv at Hkv
  icases Hkv with ⟨%ms, #Hkv⟩
  iunfold isKvOf at Hkv
  icases Hkv with ⟨#Hko, #Hregs, #Hst, %Hm⟩
  obtain ⟨Hn, Hr⟩ := Hm
  ihave Hobj := txnObjAt_conn tp api addr (ms.map SrvAt.addr) ci cd b $$ [Hobj]
  · iframe Hobj; iframe #
  ihave #HK := srvStart_both ms $$ Hst
  iapply (txn.Commit.wp_members wp_retry_Txn wp_ContextError tp ms ci cd b (W64 0) [] Q)
    $$ [Hobj Hu]
  · iframe Hobj
    iframe #
    isplitl []
    · ipureintro; exact Hp
    isplitl []
    · iunfold knownAt; iexact HK
    iapply (txnReqPre_of_upd tp ms (!dup) (noRefusal_of_dup ms dup Hr) _ _
      (txnUpd_of ms γ Hn (txnWireOf b.model) Q)) $$ Hu
  inext
  iintro %resp %err Hout
  iapply HΦ
  iapply (txnCallOut_mono _ _ resp err
    (fun m => txnAns_st ms (W64 0) [] (txnWireOf b.model) Q m Hz)) $$ Hout

end proof

end EtcdGrove
end Perennial
