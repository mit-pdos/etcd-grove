/-
Proof of `Spec/.../schema/authReadTx__RLock.lean`: the transaction's `RLock` (its contract). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authReadTx__RLock

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

theorem schema.authReadTx.RLock.wp_proof :
    schema.authReadTx.RLock.spec (GF := GF) (hG := hG) := by
  intro atx rt R Held ι L i
  wp_start as ⟨#Htx, #Hrtx, HR, HL⟩
  iunfold schema.authRTx at Hrtx
  icases Hrtx with ⟨#HRL, -⟩
  wp_auto
  wp_bind (App (Val #(methods rt.ty go!"RLock" rt.v)) (Val #()))
  iapply HRL $$ %i [$HR $HL]
  inext
  iintro ⟨%x, %D, %Hwf, HD, HL, #Hrd⟩
  (try wp_auto)
  iapply HΦ
  iexists x, D
  iframe HD HL Hrd
  ipureintro; exact Hwf

end proof

end EtcdGrove
end Perennial
