/-
Proof of `Spec/.../schema/authBatchTx__UnsafePutUser.lean`: `proto.Marshal`, one call of the transaction. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBatchTx__UnsafePutUser
public import Spec.google_golang_org.protobuf.proto.MarshalUser

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

theorem schema.authBatchTx.UnsafePutUser.wp_proof
    (hM : proto.MarshalUser.spec (GF := GF) (hG := hG)) :
    schema.authBatchTx.UnsafePutUser.spec (GF := GF) (hG := hG) := by
  intro atx t lg p x R Q hutf
  wp_start_folded as ⟨#Htx, #Hlg, Hu, HR, #HP⟩
  rw [MethodUnfold.method_unfold (t := go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.ty) (m := go!"UnsafePutUser")]
  wp_call
  ihave Hsi : (schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hsi with ⟨-, -, -, -, -, -, -, -, ⟨%ub, #HB, -⟩, -⟩
  wp_auto
  wp_apply (hM p x hutf) $$ [$Hu] as %d ⟨Hu, Hd, -⟩
  imod ownSlice_persist $$ Hd with #Hd
  (try wp_auto)
  iunfold auth.ownUser at Hu
  icases Hu with ⟨%st, %name, %pw, %roles, %o, %sc, Hp, #Hn, #Hpw, #Hr, #Ho⟩
  wp_auto
  wp_bind (App (App (App (Val #(methods t.ty _ t.v)) _) _) _)
  iapply HP $$ %ub %name %d [$HB $Hn $Hd $HR]
  inext
  iintro HQ
  (try wp_auto)
  iapply HΦ
  iframe HQ
  iunfold auth.ownUser
  iexists st, name, pw, roles, o, sc
  iframe Hp
  iframe #

end proof

end EtcdGrove
end Perennial
