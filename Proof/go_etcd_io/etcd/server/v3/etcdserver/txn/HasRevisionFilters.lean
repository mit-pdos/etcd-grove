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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem txn.HasRevisionFilters.wp_proof : txn.HasRevisionFilters.spec (GF := GF) (hG := hG) := by
  intro r dq o
  wp_start as Hr
  iunfold txn.rangeRequestAt at Hr
  icases Hr with ⟨%Hnn, %ksl, %esl, %k, %e, %rev, %limit, %order, %target, %ser, %ko, %co, %minM, %maxM, %minC, %maxC, Hk, #Hks, #He, #Hes, Hlim, Hrev, #Hord, #Htgt, #Hser, #Hko, #Hco, #HminM, #HmaxM, #HminC, #HmaxC, %Ho, %Hkb⟩
  -- (auth-mediation M3) the three fields at `dq` are not read: put the request back together
  ihave Hr : txn.rangeRequestAt r dq o $$ [Hk Hlim Hrev]
  · iunfold txn.rangeRequestAt
    isplitr
    · ipureintro; exact Hnn
    iexists ksl, esl, k, e, rev, limit, order, target, ser, ko, co, minM, maxM, minC, maxC
    iframe Hk Hlim Hrev
    iframe #
    ipureintro; exact ⟨Ho, Hkb⟩
  wp_auto
  wp_if_destruct <;> (try wp_auto) <;> (try wp_if_destruct) <;> (try wp_auto) <;>
    (try wp_if_destruct) <;> (try wp_auto) <;> (try wp_if_destruct) <;> (try wp_auto)
  all_goals
    ihave H := HΦ $$ [Hr]
    · iexact Hr
    iExactEq H
    subst Ho
    simp_all [txn.hasRevFilters, txn.rangeOpOf]



end proof

end EtcdGrove
end Perennial
