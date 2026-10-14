/-
**The quota wrapper's methods as service methods** (unit P3b; `InvQuota.lean`): `quotaKVServer`'s
`Put` (from its spec, `quotaKV_putHandlerOk_of`), `Range` and `DeleteRange` (the embedded
service's, promoted: method-set wrappers, not functions of the package) meet a spec the
embedded service's meet (`grpcHandlerOk`); and what the learner check reads of the decoded put,
range and delete requests (`learnerReqOk`). Lean-first (no Rocq counterpart).
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

/-- **`quotaKVServer.Put` meets the embedded service's spec**, with the reader slot of
`leadTimeMu` the alarm needs (from its spec). -/
theorem v3rpc.quotaKV_putHandlerOk_of
    (wp_Put : v3rpc.quotaKVServer.Put.spec (GF := GF) (hG := hG))
    {Req Rep : ProtoMsg GF} (Spec : GrpcSpec Req Rep) (q s : Loc) (kv : GoInterfaceOk)
    (E : apply.AEnv GF) (ρ : ReqNames) (S : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        v3rpc.quotaKVServerAt q kv s ∗ grpcHandlerOk #(methods kv.ty go!"Put" kv.v) S Spec ∗
        isServerReq s E ρ ∗ □ (|==> idCred ρ.ids 1) ⊢
      grpcHandlerOk (q @!! go.GoType.PointerType v3rpc.quotaKVServer.ty @!! go!"Put")
        iprop(S ∗ srvLeadTimeReader s) Spec := by
  iintro ⟨#Hp1, #Hp2, #Hq, #Hh, #Hsrv, #HNR⟩
  unfold grpcHandlerOk
  iintro %m %Φ %ci %cd %r !> %Ψ ⟨⟨HS, Hlt⟩, #Hctx, #Hrc, #Hr, HSpec⟩ HΨ
  iapply (wp_Put Req Rep Spec q s kv E ρ S m Φ ci cd r) $$ [HS Hlt HSpec]
  · iframe; iframe #
    unfold grpcHandlerOk
    iexact Hh
  inext
  iintro %resp %err ⟨HS, Hlt, Hres⟩
  iapply HΨ
  iframe

/-- **`quotaKVServer.Txn` meets (the vertical slice's unit V2; as `Put`'s) the embedded service's spec**, with the reader slot of
`leadTimeMu` the alarm needs (from its spec). -/
theorem v3rpc.quotaKV_txnHandlerOk_of
    (wp_Txn : v3rpc.quotaKVServer.Txn.spec (GF := GF) (hG := hG))
    {Req Rep : ProtoMsg GF} (Spec : GrpcSpec Req Rep) (q s : Loc) (kv : GoInterfaceOk)
    (E : apply.AEnv GF) (ρ : ReqNames) (S : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        v3rpc.quotaKVServerAt q kv s ∗ grpcHandlerOk #(methods kv.ty go!"Txn" kv.v) S Spec ∗
        isServerReq s E ρ ∗ □ (|==> idCred ρ.ids 1) ⊢
      grpcHandlerOk (q @!! go.GoType.PointerType v3rpc.quotaKVServer.ty @!! go!"Txn")
        iprop(S ∗ srvLeadTimeReader s) Spec := by
  iintro ⟨#Hp1, #Hp2, #Hq, #Hh, #Hsrv, #HNR⟩
  unfold grpcHandlerOk
  iintro %m %Φ %ci %cd %r !> %Ψ ⟨⟨HS, Hlt⟩, #Hctx, #Hrc, #Hr, HSpec⟩ HΨ
  iapply (wp_Txn Req Rep Spec q s kv E ρ S m Φ ci cd r) $$ [HS Hlt HSpec]
  · iframe; iframe #
    unfold grpcHandlerOk
    iexact Hh
  inext
  iintro %resp %err ⟨HS, Hlt, Hres⟩
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
            (Var "$r")))))) :
    v3rpc.quotaKVServerAt (GF := GF) q kv s ∗ grpcHandlerOk #(methods kv.ty mn kv.v) S Spec ⊢
      grpcHandlerOk (q @!! go.GoType.PointerType v3rpc.quotaKVServer.ty @!! mn) S Spec := by
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

/-- The learner check reads nothing of a non-range request held at a pointer. -/
theorem v3rpc.learnerReqOk_ptr (T : go.GoType) (l : Loc)
    (hT : T ≠ etcdserverpb.RangeRequest.ty) :
    ⊢ v3rpc.learnerReqOk (GF := GF) (interface.mkOk (go.GoType.PointerType T) #l) := by
  unfold v3rpc.learnerReqOk
  isplitr
  · ipureintro; right; exact ⟨_, l, rfl⟩
  iintro %r %Hr
  exfalso
  simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq,
    go.GoType.PointerType.injEq] at Hr
  exact hT Hr.1

/-- What the learner check reads of a decoded range request: its `Serializable`. -/
theorem v3rpc.learnerReqOk_range (l : Loc) (o : OpFull) :
    txn.rangeRequestIs (GF := GF) l o ⊢
      v3rpc.learnerReqOk (interface.mkOk (go.GoType.PointerType etcdserverpb.RangeRequest.ty) #l) := by
  iintro #Hr
  unfold v3rpc.learnerReqOk
  isplitr
  · ipureintro; right; exact ⟨_, l, rfl⟩
  iintro %r %Heq
  simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at Heq
  have hl : l = r := Perennial.go.IntoValInj.intoVal_inj Heq
  subst hl
  iunfold txn.rangeRequestIs at Hr
  icases Hr with ⟨-, %ksl, %esl, %k, %e, %rev, %limit, %order, %target, %ser, %ko, %co, %minM,
    %maxM, %minC, %maxC, -, -, -, -, -, -, -, -, #Hser, -⟩
  iexists ser
  iexact Hser

end lemmas

end EtcdGrove
end Perennial
