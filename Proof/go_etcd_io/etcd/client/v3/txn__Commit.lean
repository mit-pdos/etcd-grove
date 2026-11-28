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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `t.Commit()` for any spec `Spec` registered for `Txn` at the connection (the transport's terms,
as the retry client's spec takes them; `txn.Commit.wp_proof` instantiates it with the members'
spec, `kvTxnSpec`): `txnCallOut`. Since 2026-10-28 (the auth plan's E3zc) the spec is
metadata-indexed (`GrpcSpecMd`; a plain one is `GrpcSpec.md`), its precondition at every metadata
an attempt on the connection `conn` of the builder's `*kv` `api` may deliver (`attemptPre`). -/
theorem txn.Commit.wp_generic (wp_retry_Txn : retryKVClient.Txn.spec (GF := GF) (hG := hG))
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG)) :
    txn.Commit.specG (GF := GF) (hG := hG) := by
  intro tp api0 conn0 addr ci om cd b Spec Q
  wp_start as ⟨Hlt, Htx, #Hom, #Hkv0, #Hobj0, #Hrpc, Hrun, %Hsz⟩
  iunfold txnObjAt at Htx
  icases Htx with ⟨%Htpn, %api, %cosl, %csl, %ssl, %fsl, %cps, %sps, %fps, %iw, #Hkvf, #Hkv, #Hctxf,
    #Hctx, #Hce, #Hmu, Hcif, Hcthen, Hcelse, Hiw, Hcmps, Hcsl, Hccap, #Hcpa, Hsus, Hssl, Hscap,
    #Hspa, Hfas, Hfsl, Hfcap, #Hfpa, #Hcof, #Hco⟩
  -- the builder's `*kv` is `api0`, over `conn0`
  ihave %Hapi : ⌜api = api0⌝ $$ []
  · iunfold txnKvIs at Hkv0
    icombine Hkvf Hkv0 gives %Heq
    ipureintro; exact Heq
  subst Hapi
  ihave #Hkv' := Hkv
  iunfold kvObjAt at Hkv'
  icases Hkv' with ⟨%rkv, %conn, %sl, #Hremote, #Hrkv, #Hconn, #Hcopts, #Hco'⟩
  ihave %Hconn0 : ⌜conn0 = conn⌝ $$ []
  · iapply (kvObjAtC_agree api conn0 conn addr addr)
    iframe Hobj0
    unfold kvObjAtC
    iexists rkv, sl
    iframe #
  subst Hconn0
  iunfold callOptsAt at Hco
  icases Hco with ⟨%vs, #Hvs, %Hcap, #Hok, %Hsc⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, -⟩
  ipersist Hcsl; ipersist Hssl; ipersist Hfsl
  ihave Hrun' : reqPre conn0 go!"/etcdserverpb.KV/Txn" addr vs
      (attemptPre conn0 om Spec (txnWireOf b.model) Q) $$ [Hrun]
  · iapply kvReqPre_conn api rkv conn0 go!"/etcdserverpb.KV/Txn" (.inr (.inr rfl)) addr vs _ Hsc $$ [Hrun]
    iframe Hremote Hrkv
    iapply txnReqPre_kv tp api addr $$ [Hrun]
    iframe Hrun
    unfold txnKvIs; iexact Hkvf
  wp_apply wp_retry_Txn rkv conn0 addr Spec Q ci om cd _ _ (txnWireOf b.model) cosl vs $$ [Hlt «$r0» Hrun']
    as %resp %err ⟨Hlt, -, Hres⟩
  · iframe #
    iframe
    isplitl []; rotate_left
    · ipureintro; exact ⟨rfl, Hsz.wire_lt⟩
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
    iframe Hlt
    unfold txnCallOut
    ileft
    iframe Hm
    ipureintro; rfl
  · obtain ⟨Hne, Hce', Hnull⟩ := Herr
    cases err with
    | nil => exact absurd rfl Hne
    | ok ei =>
      wp_auto
      ihave ⟨%mC, #HmC⟩ := go_etcd_io.etcd.cache.v3.statusErrOk_descIs _ $$ Hse
      wp_apply wp_ContextError ci cd (GoInterface.ok ei) mC $$ [$Hse $HmC] as %err' ⟨%Herr', #Hse', #Hclw, -⟩
      · iframe #; ipureintro; exact fun _ => Hce'
      ihave #Hcl' := Hclw $$ Hcl
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked]
      · inext; itrivial
      iapply HΦ
      iframe Hlt
      unfold txnCallOut
      iright
      iframe #
      ipureintro
      exact ⟨(Herr'.2 (by simp)).1, (Herr'.2 (by simp)).2, rfl⟩

/-- `t.Commit()` over a `*kv` of the members (D44): `txn.Commit.wp_generic` at the members' spec,
registered by their registrations (`kvRegs_rpcTxn`) and met by the caller's side (`txnSpec_of`). -/
theorem txn.Commit.wp_members (wp_retry_Txn : retryKVClient.Txn.spec (GF := GF) (hG := hG))
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG)) :
    txn.Commit.specM (GF := GF) (hG := hG) := by
  intro tp ms ci cd b c F Q
  iintro %Φ ⟨#Pc, Hlt, Hobj, #Hregs, %Hp, #Hk, Hu, %Hsz⟩ HΦ
  icases txnObjAt_kv tp (ms.map SrvAt.addr) ci cd b $$ Hobj with ⟨%api, %conn, #Hkv, #Hkc, Hobj⟩
  icases txnObjAt_outMD tp (ms.map SrvAt.addr) ci cd b $$ Hobj with ⟨Hobj, %om, #Hom⟩
  -- the plain spec at every metadata (`GrpcSpec.md`)
  iapply (txn.Commit.wp_generic wp_retry_Txn wp_ContextError tp api conn (ms.map SrvAt.addr) ci om cd b
    (GrpcSpec.md (kvTxnSpec ms)) (txnAns ms c F (txnWireOf b.model) Q)) $$ [Hlt Hobj Hu] HΦ
  iframe #
  iframe Hlt Hobj
  isplitl []
  · iapply (isGrpcRpcs_md _ _ _).1; iapply (kvRegs_rpcTxn ms) $$ Hregs
  isplitl [Hu]; rotate_left
  · ipureintro; exact Hsz
  iapply (txnReqPre_wand tp (ms.map SrvAt.addr) (knownAt ms c F) _ _
    ((txnSpec_of ms c F (txnWireOf b.model) Q (txnWireOf_plain _ Hp.1) Hp.2).trans
      (attemptPre_md conn om (kvTxnSpec ms) _ _)))
  iframe Hk Hu

/-- `t.Commit()` on a builder over a `*kv` of etcd's KV `γ` (D44; stage A, 2026-11-27):
`txn.Commit.wp_generic` at the view spec the `*kv`'s endpoints register (`isKv`,
`kvRegsV_rpcTxn`; the builder's connection the `*kv`'s, `txnObjAt_conn`), met by the caller's update
at `γ` (`txnPre_V`); the reply facts are the spec's (`txnStOk`). -/
theorem txn.Commit.wp_proof (wp_retry_Txn : retryKVClient.Txn.spec (GF := GF) (hG := hG))
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG)) :
    txn.Commit.spec (GF := GF) (hG := hG) := by
  intro tp addr api γ dup ci cd b Q
  iintro %Φ ⟨#Pc, Hlt, Hobj, #Hkt, #Hkv, %Hp, Hu, %Hsz⟩ HΦ
  ihave Hu := txnAu_upd dup γ (txnWireOf b.model) Q $$ Hu
  iunfold isKv at Hkv
  icases Hkv with ⟨%addrs, #Hko, #Hregs, #Hnr⟩
  ihave Hobj := txnObjAt_conn tp api addr addrs ci cd b $$ [Hobj]
  · iframe Hobj; iframe #
  icases txnObjAt_kv tp addrs ci cd b $$ Hobj with ⟨%api', %conn, #Hkv', #Hkc, Hobj⟩
  icases txnObjAt_outMD tp addrs ci cd b $$ Hobj with ⟨Hobj, %om, #Hom⟩
  iapply (txn.Commit.wp_generic wp_retry_Txn wp_ContextError tp api' conn addrs ci om cd b
    (etcdTxnSpecV γ) (txnStOk γ (txnWireOf b.model) Q)) $$ [Hlt Hobj Hu]
  · iframe #
    iframe Hlt Hobj
    isplitl []
    · iapply (kvRegsV_rpcTxn addrs γ) $$ Hregs
    isplitl [Hu]; rotate_left
    · ipureintro; exact Hsz
    iapply (txnReqPre_of_upd tp addrs dup _ _
      (txnPre_V conn om γ (txnWireOf b.model) Q (txnWireOf_plain _ Hp.1) Hp.2))
    isplitl []
    · iexact Hnr
    · iexact Hu
  inext
  iintro %resp %err ⟨Hlt, Hout⟩
  iapply HΦ
  iframe Hlt
  iapply (txnCallOut_st γ) $$ Hout

end proof

end EtcdGrove
end Perennial
