/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer__Txn
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.checkTxnRequest
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.checkIntervals
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.togRPCError
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.header__fill

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

omit [FfiSyntax] [GoGlobalContext] in
theorem v3rpc.txnAllCheck_ts {n : Int} {cs : List CmpModel} {ts es : List v3rpc.ReqOp}
    (h1 : v3rpc.txnCheck n cs ts es = none) (h2 : v3rpc.ivCheck ts = none) :
    v3rpc.txnAllCheck n cs ts es = some .duplicateKey := by
  unfold v3rpc.txnAllCheck; rw [h1, h2]

omit [FfiSyntax] [GoGlobalContext] in
theorem v3rpc.txnAllCheck_es {n : Int} {cs : List CmpModel} {ts es : List v3rpc.ReqOp} {pd}
    (h1 : v3rpc.txnCheck n cs ts es = none) (h2 : v3rpc.ivCheck ts = some pd)
    (h3 : v3rpc.ivCheck es = none) :
    v3rpc.txnAllCheck n cs ts es = some .duplicateKey := by
  unfold v3rpc.txnAllCheck; rw [h1, h2, h3]

omit [FfiSyntax] [GoGlobalContext] in
theorem v3rpc.txnAllCheck_ok {n : Int} {cs : List CmpModel} {ts es : List v3rpc.ReqOp} {pd pd'}
    (h1 : v3rpc.txnCheck n cs ts es = none) (h2 : v3rpc.ivCheck ts = some pd)
    (h3 : v3rpc.ivCheck es = some pd') :
    v3rpc.txnAllCheck n cs ts es = none := by
  unfold v3rpc.txnAllCheck; rw [h1, h2, h3]

theorem v3rpc.kvServer.Txn.wp_proof
    (hChk : v3rpc.checkTxnRequest.spec (GF := GF) (hG := hG))
    (hIv : v3rpc.checkIntervals.spec (GF := GF) (hG := hG))
    (hTog : v3rpc.togRPCError.spec (GF := GF) (hG := hG))
    (hFill : v3rpc.header.fill.spec (GF := GF) (hG := hG)) :
    v3rpc.kvServer.Txn.spec (GF := GF) (hG := hG) := by
  intro p s A cid mid n ctx r cs ts es
  wp_start as ⟨#Hsrv, Hcall, #Hr, #Hwire⟩
  ihave #Hsrv' := Hsrv
  iunfold v3rpc.kvServerIs at Hsrv'
  icases Hsrv' with ⟨%Hpn, #Hhdr, #Hkv, #Hn, #HKV⟩
  iunfold v3rpc.raftKV at HKV
  icases HKV with ⟨-, -, -, #HTxn, -⟩
  iunfold v3rpc.kvTxnOk at HTxn
  ihave #Hr' := Hr
  iunfold v3rpc.txnReqIs at Hr'
  icases Hr' with ⟨%Hrn, %csl, %ssl, %fsl, %cps, %sps, %fps, -, -, -, #Hs, #Hssl, #Hss, #Hf, #Hfsl, #Hfs⟩
  iunfold v3rpc.txnReqWire at Hwire
  ihave ⟨#Hsw, #Hfw⟩ := Hwire $$ %ssl %fsl %sps %fps Hs Hssl Hf Hfsl
  wp_auto
  wp_apply hChk $$ [] as %err #Herr
  · iframe #
  cases hc : v3rpc.txnCheck (sint.Z n) cs ts es with
  | some e =>
    simp only [v3rpc.checkRes]
    iunfold txn.errVarIs at Herr
    icases Herr with ⟨%ee, #Hee, %Herr⟩
    subst Herr
    wp_auto
    iapply HΦ
    rw [show v3rpc.txnAllCheck (sint.Z n) cs ts es = some e by unfold v3rpc.txnAllCheck; rw [hc]]
    dsimp only
    iframe Hcall
    iunfold v3rpc.checkOut
    iunfold txn.errVarIs
    iframe #
    ipureintro; exact ⟨rfl, rfl⟩
  | none =>
    try simp only [v3rpc.checkRes]
    icases Herr with %Herr
    subst Herr
    wp_auto
    wp_apply (hIv ssl sps ts) $$ [] as %m1 %t1 %e1 Hiv1
    · iframe #
    cases hts : v3rpc.ivCheck ts with
    | none =>
      iunfold txn.errVarIs at Hiv1
      icases Hiv1 with ⟨%ee, #Hee, %He1⟩
      subst He1
      wp_auto
      iapply HΦ
      rw [v3rpc.txnAllCheck_ts hc hts]
      dsimp only
      iframe Hcall
      iunfold v3rpc.checkOut
      iunfold txn.errVarIs
      iframe #
      ipureintro; exact ⟨rfl, rfl⟩
    | some pd =>
      icases Hiv1 with ⟨%He1, -⟩
      subst He1
      wp_auto
      wp_apply (hIv fsl fps es) $$ [] as %m2 %t2 %e2 Hiv2
      · iframe #
      cases hes : v3rpc.ivCheck es with
      | none =>
        iunfold txn.errVarIs at Hiv2
        icases Hiv2 with ⟨%ee, #Hee, %He2⟩
        subst He2
        wp_auto
        iapply HΦ
        rw [v3rpc.txnAllCheck_es hc hts hes]
        dsimp only
        iframe Hcall
        iunfold v3rpc.checkOut
        iunfold txn.errVarIs
        iframe #
        ipureintro; exact ⟨rfl, rfl⟩
      | some pd' =>
        icases Hiv2 with ⟨%He2, -⟩
        subst He2
        wp_auto
        wp_apply HTxn $$ [Hcall] as %resp %err' Hans
        · iframe; iframe #
          ipureintro
          exact ⟨hc, by simp [v3rpc.intervalsOk, hts], by simp [v3rpc.intervalsOk, hes]⟩
        iunfold v3rpc.kvAnswer at Hans
        icases Hans with (⟨%Hok, %h, %rv, #Hhf, Hw, Hrev, HA⟩ | ⟨%Hrn, #Hse, HA⟩)
        · obtain ⟨He, Hrn⟩ := Hok
          subst He
          wp_auto
          wp_apply hFill $$ [Hw Hrev] as ⟨Hf, %rv', Hrev'⟩
          · iframe; iframe #
          wp_auto
          iapply HΦ
          rw [v3rpc.txnAllCheck_ok hc hts hes]
          dsimp only
          iunfold v3rpc.kvOut
          ileft
          isplitr
          · ipureintro; exact ⟨rfl, Hrn⟩
          iexists h, rv, rv'
          iframe
          iframe #
        · ihave #Hse' := Hse
          iunfold v3rpc.srvErrIs at Hse'
          icases Hse' with ⟨%Hen, -⟩
          subst Hrn
          cases err' with
          | nil => exact absurd rfl Hen
          | ok ei =>
            wp_auto
            wp_apply hTog $$ [] as %e %He
            · iframe #
            iapply HΦ
            rw [v3rpc.txnAllCheck_ok hc hts hes]
            dsimp only
            iunfold v3rpc.kvOut
            iright
            isplitr
            · ipureintro; exact ⟨rfl, He⟩
            iexists _
            iexact HA

end proof

end EtcdGrove
end Perennial
