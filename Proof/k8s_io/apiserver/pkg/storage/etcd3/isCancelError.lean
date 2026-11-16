/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/isCancelError.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.isCancelError

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

-- The `grpcError` half of `isCancelError` (reached from two branches).
set_option hygiene false in
local macro "grpc_part" : tactic => `(tactic| (
  cases hcg : go.typeSetContains e.ty k8s_io.apiserver.pkg.storage.etcd3.grpcError.ty
  case true =>
    simp only [↓reduceIte]
    wp_auto
    ihave H2 := Hgrpc $$ %trivial
    icases H2 with ⟨%s, #Hgs, #Hsc⟩
    wp_bind (App (Val #(methods e.ty go!"GRPCStatus" e.v)) (Val #()))
    iapply Hgs
    inext
    wp_auto
    wp_bind (App (Val #(methods (go.GoType.PointerType google_golang_org.grpc.status.Status.ty)
      go!"Code" #s)) (Val #()))
    iapply Hsc
    inext
    iintro %c2
    wp_auto
    cases decide (c2 = W32 1) <;> (wp_auto; iapply HΦ; itrivial)
  simp only [Bool.false_eq_true, ↓reduceIte]
  wp_auto
  iapply HΦ; itrivial))

theorem isCancelError.wp_proof : isCancelError.spec (GF := GF) (hG := hG) := by
  intro err
  unfold kErrOk
  wp_start as ⟨%e, %He, %Heq, #Hstr, %Hfmt, #Hcode, #Hgrpc, #Has, #Hst⟩
  subst He
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Hci := context.isInit_access $$ Pctx
  icases Hci with ⟨-, -, -, -, -, ⟨%cx, #Hcx, -⟩, -⟩
  wp_auto
  wp_bind (ite _ _ _)
  iapply wp_kErrOk_eq_ptr e cx _ Heq.1
  iintro %b1
  wp_auto
  cases b1
  case true =>
    wp_auto
    iapply HΦ; itrivial
  wp_auto
  cases hce : go.typeSetContains e.ty k8s_io.apiserver.pkg.storage.etcd3.etcdError.ty
  case true =>
    simp only [↓reduceIte]
    wp_auto
    wp_bind (App (Val #(methods e.ty go!"Code" e.v)) (Val #()))
    ihave Hc := Hcode $$ %trivial
    iapply Hc
    inext
    iintro %c
    wp_auto
    cases hd : decide (c = W32 1)
    case true =>
      wp_auto
      iapply HΦ; itrivial
    wp_auto
    grpc_part
  simp only [Bool.false_eq_true, ↓reduceIte]
  wp_auto
  grpc_part

end proof

end k8s
end EtcdGrove
end Perennial
