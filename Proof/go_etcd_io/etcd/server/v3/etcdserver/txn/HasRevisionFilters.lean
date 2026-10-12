/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.HasRevisionFilters

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem txn.HasRevisionFilters.wp_proof : txn.HasRevisionFilters.spec (GF := GF) (hG := hG) := by
  intro r o
  wp_start as #Hr
  iunfold txn.rangeRequestIs at Hr
  icases Hr with ⟨%Hnn, %ksl, %esl, %k, %e, %rev, %limit, %order, %target, %ser, %ko, %co, %minM, %maxM, %minC, %maxC, #Hk, #Hks, #He, #Hes, #Hlim, #Hrev, #Hord, #Htgt, #Hser, #Hko, #Hco, #HminM, #HmaxM, #HminC, #HmaxC, %Ho⟩
  wp_auto
  wp_if_destruct <;> (try wp_auto) <;> (try wp_if_destruct) <;> (try wp_auto) <;>
    (try wp_if_destruct) <;> (try wp_auto) <;> (try wp_if_destruct) <;> (try wp_auto)
  all_goals
    ihave H := HΦ $$ []
    · itrivial
    iExactEq H
    subst Ho
    simp_all [txn.hasRevFilters, txn.rangeOpOf]



end proof

end EtcdGrove
end Perennial
