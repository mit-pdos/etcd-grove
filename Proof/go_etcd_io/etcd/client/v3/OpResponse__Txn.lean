/-
Proof of `Spec/go_etcd_io/etcd/client/v3/OpResponse__Txn.lean`. Lean-first (no Rocq counterpart).
`OpResponse.Txn` (`func (op OpResponse) Txn() *TxnResponse { return op.txn }`, `client/v3/op.go:467`)
is given a trusted unfolding (`OpResponseTxnBody`, following `DialWithBalancerBody.lean`) so that
`Code/go_etcd_io/etcd/client/v3.lean` does not need to be regenerated.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.OpResponse__Txn

@[expose] public section

noncomputable section

namespace Perennial
namespace go_etcd_io.etcd.client.v3

/-- `func (op OpResponse) Txn() *TxnResponse { return op.txn }` (`client/v3/op.go:467`). -/
noncomputable def OpResponse.Txn.trustedImpl [FfiSyntax] [GoGlobalContext] : val :=
  (LamV "op"
  (Lam BAnon
  (App (Val exceptionDo)
  (Let "op" (App (Val (GoInstruction (GoAlloc OpResponse.ty))) (Var "op"))
  (App (Val doReturn)
  (App (Val (GoInstruction (GoLoad (go.GoType.PointerType TxnResponse.ty))))
    (App (Val (GoInstruction (StructFieldRef OpResponse.ty go!"txn"))) (Var "op"))))))))

/-- Trusted method unfolding for `OpResponse.Txn` and `(*OpResponse).Txn`. -/
class OpResponseTxnBody [FfiSyntax] [GoGlobalContext] [GoLocalContext]
    [GoSemanticsFunctions] : Prop where
  Txn_unfold : MethodUnfold OpResponse.ty go!"Txn" OpResponse.Txn.trustedImpl
  ptr_Txn_unfold : MethodUnfold (go.GoType.PointerType OpResponse.ty) go!"Txn" (LamV "$r"
    (App (Val (GoInstruction (MethodResolve OpResponse.ty go!"Txn")))
      (App (Val (GoInstruction (GoLoad OpResponse.ty))) (Var "$r"))))

attribute [instance] OpResponseTxnBody.Txn_unfold OpResponseTxnBody.ptr_Txn_unfold

end go_etcd_io.etcd.client.v3

namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [OpResponseTxnBody]

theorem OpResponse.Txn.wp_proof : OpResponse.Txn.spec (GF := GF) (hG := hG) := by
  intro rp r dq
  wp_start as Hr
  wp_auto
  wp_method_call
  unfold OpResponse.Txn.trustedImpl
  wp_auto
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
