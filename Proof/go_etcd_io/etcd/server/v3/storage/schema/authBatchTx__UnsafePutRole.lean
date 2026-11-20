/-
Proof of `Spec/.../schema/authBatchTx__UnsafePutRole.lean`: `proto.Marshal`, one call of the transaction. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBatchTx__UnsafePutRole
public import Spec.google_golang_org.protobuf.proto.MarshalRole

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

theorem schema.authBatchTx.UnsafePutRole.wp_proof
    (hM : proto.MarshalRole.spec (GF := GF) (hG := hG)) :
    schema.authBatchTx.UnsafePutRole.spec (GF := GF) (hG := hG) := by
  intro atx t lg p x R Q
  wp_start_folded as ⟨#Htx, #Hlg, Hu, HR, #HP⟩
  rw [MethodUnfold.method_unfold (t := go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.ty) (m := go!"UnsafePutRole")]
  wp_call
  ihave Hsi : (schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hsi with ⟨-, -, -, -, -, -, -, -, -, ⟨%ub, #HB, -⟩, -⟩
  wp_auto
  wp_apply (hM p x) $$ [$Hu] as %d ⟨Hu, Hd, -⟩
  imod ownSlice_persist $$ Hd with #Hd
  (try wp_auto)
  iunfold auth.ownRole at Hu
  icases Hu with ⟨%st, %name, %kp, %ps, %sc, Hp, #Hn, #Hkp, %Hlen, #Hps⟩
  wp_auto
  wp_bind (App (App (App (Val #(methods t.ty _ t.v)) _) _) _)
  iapply HP $$ %ub %name %d [$HB $Hn $Hd $HR]
  inext
  iintro HQ
  (try wp_auto)
  iapply HΦ
  iframe HQ
  iunfold auth.ownRole
  iexists st, name, kp, ps, sc
  iframe Hp
  iframe #
  ipureintro; exact Hlen

end proof

end EtcdGrove
end Perennial
