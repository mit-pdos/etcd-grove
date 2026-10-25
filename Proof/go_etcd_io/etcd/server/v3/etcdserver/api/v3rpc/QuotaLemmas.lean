/-
**The quota wrapper's methods as service methods** (unit P3b; `InvQuota.lean`, updated for PR
etcd#21401): `quotaKVServer`'s `Put` (from its spec, `quotaKV_putHandlerOk_of`), `Txn`
(`quotaKV_txnHandlerOk_of`), `Range` and `DeleteRange` (the embedded service's, promoted:
method-set wrappers, not functions of the package) meet a spec the embedded service's meet
(`grpcHandlerOk`); and what the learner check and `requestLogFields` read of the decoded put,
range, delete, and txn requests (`learnerReqOk`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer__Put
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer__Txn

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`quotaKVServer.Put` meets the embedded service's spec**, with the quota check's
reader slots (`quotaRd`, from its spec). -/
theorem v3rpc.quotaKV_putHandlerOk_of
    (wp_Put : v3rpc.quotaKVServer.Put.spec (GF := GF) (hG := hG))
    {Req Rep : ProtoMsg GF} (Spec : GrpcSpec Req Rep) (q s : Loc) (kv : GoInterfaceOk)
    (S : IProp GF) (C : GoInterfaceOk → IProp GF := fun _ => iprop(True)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        v3rpc.quotaKVServerAt q kv s ∗ grpcHandlerOk #(methods kv.ty go!"Put" kv.v) S Spec C ⊢
      grpcHandlerOk (q @!! go.GoType.PointerType v3rpc.quotaKVServer.ty @!! go!"Put")
        iprop(S ∗ v3rpc.quotaRd s) Spec C := by
  iintro ⟨#Hp1, #Hp2, #Hq, #Hh⟩
  unfold grpcHandlerOk
  iintro %m %Φ %ci %cd %r !> %Ψ ⟨⟨HS, Hqr⟩, #Hctx, #Hrc, HC, #Hr, HSpec⟩ HΨ
  iapply (wp_Put Req Rep Spec q s kv S C m Φ ci cd r) $$ [HS Hqr HC HSpec]
  · iframe; iframe #
    unfold grpcHandlerOk
    iexact Hh
  inext
  iintro %resp %err ⟨HS, Hqr, Hres⟩
  iapply HΨ
  iframe

/-- **`quotaKVServer.Txn` meets (the vertical slice's unit V2; as `Put`'s) the embedded service's
spec**, with the quota check's reader slots (`quotaRd`, from its spec). -/
theorem v3rpc.quotaKV_txnHandlerOk_of
    (wp_Txn : v3rpc.quotaKVServer.Txn.spec (GF := GF) (hG := hG))
    {Req Rep : ProtoMsg GF} (Spec : GrpcSpec Req Rep) (q s : Loc) (kv : GoInterfaceOk)
    (S : IProp GF) (C : GoInterfaceOk → IProp GF := fun _ => iprop(True)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        v3rpc.quotaKVServerAt q kv s ∗ grpcHandlerOk #(methods kv.ty go!"Txn" kv.v) S Spec C ⊢
      grpcHandlerOk (q @!! go.GoType.PointerType v3rpc.quotaKVServer.ty @!! go!"Txn")
        iprop(S ∗ v3rpc.quotaRd s) Spec C := by
  iintro ⟨#Hp1, #Hp2, #Hq, #Hh⟩
  unfold grpcHandlerOk
  iintro %m %Φ %ci %cd %r !> %Ψ ⟨⟨HS, Hqr⟩, #Hctx, #Hrc, HC, #Hr, HSpec⟩ HΨ
  iapply (wp_Txn Req Rep Spec q s kv S C m Φ ci cd r) $$ [HS Hqr HC HSpec]
  · iframe; iframe #
    unfold grpcHandlerOk
    iexact Hh
  inext
  iintro %resp %err ⟨HS, Hqr, Hres⟩
  iapply HΨ
  iframe

/-- **A promoted method of `quotaKVServer`** (`Range`, `DeleteRange`: the embedded service's)
meets what the embedded service's meets. -/
theorem v3rpc.quotaKV_promotedHandlerOk {Req Rep : ProtoMsg GF} (Spec : GrpcSpec Req Rep)
    (q s : Loc) (kv : GoInterfaceOk) (S : IProp GF) (mn : GoString)
    (hm : MethodUnfold (go.GoType.PointerType v3rpc.quotaKVServer.ty) mn (LamV "$r"
      (App (Val (GoInstruction (MethodResolve etcdserverpb.KVServer.ty mn)))
        (App (Val (GoInstruction (GoLoad etcdserverpb.KVServer.ty)))
          (App (Val (GoInstruction (StructFieldRef v3rpc.quotaKVServer.ty go!"KVServer")))
            (Var "$r"))))))
    (C : GoInterfaceOk → IProp GF := fun _ => iprop(True)) :
    v3rpc.quotaKVServerAt (GF := GF) q kv s ∗ grpcHandlerOk #(methods kv.ty mn kv.v) S Spec C ⊢
      grpcHandlerOk (q @!! go.GoType.PointerType v3rpc.quotaKVServer.ty @!! mn) S Spec C := by
  iintro ⟨#Hq, #Hh⟩
  iunfold v3rpc.quotaKVServerAt at Hq
  icases Hq with ⟨%Hqn, #Hkv, -⟩
  unfold grpcHandlerOk
  iintro %m %Φ %ci %cd %r !> %Ψ Hpre HΨ
  rw [hm.method_unfold]
  wp_pures
  wp_auto
  iapply Hh $$ %m %Φ %ci %cd %r Hpre
  inext
  iexact HΨ

/-- The learner check and `requestLogFields` read nothing of a non-KV request held at a pointer. -/
theorem v3rpc.learnerReqOk_ptr (T : go.GoType) (l : Loc)
    (hT1 : T ≠ etcdserverpb.RangeRequest.ty)
    (hT2 : T ≠ etcdserverpb.PutRequest.ty)
    (hT3 : T ≠ etcdserverpb.DeleteRangeRequest.ty)
    (hT4 : T ≠ etcdserverpb.TxnRequest.ty) :
    ⊢ v3rpc.learnerReqOk (GF := GF) (interface.mkOk (go.GoType.PointerType T) #l) := by
  unfold v3rpc.learnerReqOk
  isplitr
  · ipureintro; right; exact ⟨_, l, rfl⟩
  isplitr
  · iintro %r %Hr; exfalso
    simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq,
      go.GoType.PointerType.injEq] at Hr
    exact hT1 Hr.1
  isplitr
  · iintro %r %Hr; exfalso
    simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq,
      go.GoType.PointerType.injEq] at Hr
    exact hT2 Hr.1
  isplitr
  · iintro %r %Hr; exfalso
    simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq,
      go.GoType.PointerType.injEq] at Hr
    exact hT3 Hr.1
  · iintro %r %Hr; exfalso
    simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq,
      go.GoType.PointerType.injEq] at Hr
    exact hT4 Hr.1

/-- What the learner check and `requestLogFields` read of a decoded range request. -/
theorem v3rpc.learnerReqOk_range (l : Loc) (o : OpFull) :
    txn.rangeRequestIs (GF := GF) l o ⊢
      v3rpc.learnerReqOk (interface.mkOk (go.GoType.PointerType etcdserverpb.RangeRequest.ty) #l) := by
  iintro #Hr
  unfold v3rpc.learnerReqOk
  isplitr
  · ipureintro; right; exact ⟨_, l, rfl⟩
  isplitr
  · iintro %r %Heq
    simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at Heq
    have hl : l = r := Perennial.go.IntoValInj.intoVal_inj Heq
    subst hl
    iunfold txn.rangeRequestIs at Hr
    icases Hr with ⟨%Hnn, %ksl, %esl, %k, %e, %rev, %limit, %order, %target, %ser, %ko, %co, %minM,
      %maxM, %minC, %maxC, #Hk, #Hks, #He, #Hes, #Hlim, #Hrev, -, -, #Hser, #Hko, #Hco, -⟩
    isplitr
    · ipureintro; exact Hnn
    iexists ksl, esl, k, e, rev, limit, ser, ko, co
    iframe #
  isplitr
  · iintro %r %Hr'; exfalso
    simp [interface.mkOk, etcdserverpb.RangeRequest.ty, etcdserverpb.PutRequest.ty] at Hr'
  isplitr
  · iintro %r %Hr'; exfalso
    simp [interface.mkOk, etcdserverpb.RangeRequest.ty, etcdserverpb.DeleteRangeRequest.ty] at Hr'
  · iintro %r %Hr'; exfalso
    simp [interface.mkOk, etcdserverpb.RangeRequest.ty, etcdserverpb.TxnRequest.ty] at Hr'

/-- What `requestLogFields` reads of a decoded put request. -/
theorem v3rpc.learnerReqOk_put (l : Loc) (o : OpFull) :
    txn.putRequestIs (GF := GF) l o ⊢
      v3rpc.learnerReqOk (interface.mkOk (go.GoType.PointerType etcdserverpb.PutRequest.ty) #l) := by
  iintro #Hr
  unfold v3rpc.learnerReqOk
  isplitr
  · ipureintro; right; exact ⟨_, l, rfl⟩
  isplitr
  · iintro %r %Hr'; exfalso
    simp [interface.mkOk, etcdserverpb.PutRequest.ty, etcdserverpb.RangeRequest.ty] at Hr'
  isplitr
  · iintro %r %Heq
    simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at Heq
    have hl : l = r := Perennial.go.IntoValInj.intoVal_inj Heq
    subst hl
    iunfold txn.putRequestIs at Hr
    icases Hr with ⟨%Hnn, %ksl, %vsl, %k, %v, %lease, %pk, %iv, %il, #Hk, #Hks, -⟩
    isplitr
    · ipureintro; exact Hnn
    iexists ksl, k
    iframe #
  isplitr
  · iintro %r %Hr'; exfalso
    simp [interface.mkOk, etcdserverpb.PutRequest.ty, etcdserverpb.DeleteRangeRequest.ty] at Hr'
  · iintro %r %Hr'; exfalso
    simp [interface.mkOk, etcdserverpb.PutRequest.ty, etcdserverpb.TxnRequest.ty] at Hr'

/-- What `requestLogFields` reads of a decoded delete request. -/
theorem v3rpc.learnerReqOk_delete (l : Loc) (o : OpFull) :
    txn.deleteRangeRequestIs (GF := GF) l o ⊢
      v3rpc.learnerReqOk (interface.mkOk (go.GoType.PointerType etcdserverpb.DeleteRangeRequest.ty) #l) := by
  iintro #Hr
  unfold v3rpc.learnerReqOk
  isplitr
  · ipureintro; right; exact ⟨_, l, rfl⟩
  isplitr
  · iintro %r %Hr'; exfalso
    simp [interface.mkOk, etcdserverpb.DeleteRangeRequest.ty, etcdserverpb.RangeRequest.ty] at Hr'
  isplitr
  · iintro %r %Hr'; exfalso
    simp [interface.mkOk, etcdserverpb.DeleteRangeRequest.ty, etcdserverpb.PutRequest.ty] at Hr'
  isplitr
  · iintro %r %Heq
    simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at Heq
    have hl : l = r := Perennial.go.IntoValInj.intoVal_inj Heq
    subst hl
    iunfold txn.deleteRangeRequestIs at Hr
    icases Hr with ⟨%Hnn, %ksl, %esl, %k, %e, %pk, #Hk, #Hks, #He, #Hes, -⟩
    isplitr
    · ipureintro; exact Hnn
    iexists ksl, esl, k, e
    iframe #
  · iintro %r %Hr'; exfalso
    simp [interface.mkOk, etcdserverpb.DeleteRangeRequest.ty, etcdserverpb.TxnRequest.ty] at Hr'

/-- What `requestLogFields` reads of a decoded txn request. -/
theorem v3rpc.learnerReqOk_txn (l : Loc) (t : TxnModel) :
    txn.txnRequestIs (GF := GF) l t ⊢
      v3rpc.learnerReqOk (interface.mkOk (go.GoType.PointerType etcdserverpb.TxnRequest.ty) #l) := by
  iintro #Hr
  unfold v3rpc.learnerReqOk
  isplitr
  · ipureintro; right; exact ⟨_, l, rfl⟩
  isplitr
  · iintro %r %Hr'; exfalso
    simp [interface.mkOk, etcdserverpb.TxnRequest.ty, etcdserverpb.RangeRequest.ty] at Hr'
  isplitr
  · iintro %r %Hr'; exfalso
    simp [interface.mkOk, etcdserverpb.TxnRequest.ty, etcdserverpb.PutRequest.ty] at Hr'
  isplitr
  · iintro %r %Hr'; exfalso
    simp [interface.mkOk, etcdserverpb.TxnRequest.ty, etcdserverpb.DeleteRangeRequest.ty] at Hr'
  · iintro %r %Heq
    simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at Heq
    have hl : l = r := Perennial.go.IntoValInj.intoVal_inj Heq
    subst hl
    iunfold txn.txnRequestIs at Hr
    icases Hr with ⟨%Hnn, Htf⟩
    iunfold txn.txnFieldsIs at Htf
    icases Htf with ⟨%csl, %ssl, %fsl, %cps, %sps, %fps, #Hc, -, -, #Hs, -, -, #Hf, -⟩
    isplitr
    · ipureintro; exact Hnn
    iexists csl, ssl, fsl
    iframe #

end lemmas

end EtcdGrove
end Perennial
