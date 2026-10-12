/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.rangeLimit
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.IsDefaultOrdering
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

theorem txn.rangeLimit.wp_proof
    (hIsDef : txn.IsDefaultOrdering.spec (GF := GF) (hG := hG))
    (hHas : txn.HasRevisionFilters.spec (GF := GF) (hG := hG)) :
    txn.rangeLimit.spec (GF := GF) (hG := hG) := by
  intro r o
  wp_start as #Hr
  ihave #Hr2 := Hr
  iunfold txn.rangeRequestIs at Hr2
  icases Hr2 with ⟨%Hnn, %ksl, %esl, %k, %e, %rev, %limit, %order, %target, %ser, %ko, %co, %minM, %maxM, %minC, %maxC, #Hk, #Hks, #He, #Hes, #Hlim, #Hrev, #Hord, #Htgt, #Hser, #Hko, #Hco, #HminM, #HmaxM, #HminC, #HmaxC, %Ho⟩
  wp_auto
  wp_apply hIsDef
  have hdef : txn.isDefaultOrd o.sortTarget o.sortOrder =
      decide (order = W32 0 ∨ (target = W32 0 ∧ order = W32 1)) := by
    subst Ho; exact txn.isDefaultOrd_sext target order
  have hlimo : o.base.limit = limit := by subst Ho; rfl
  wp_if_destruct
  · rename_i Hdef
    wp_apply (hHas r o) $$ [$Hr]
    cases hh : txn.hasRevFilters o
    · wp_auto
      wp_if_destruct <;> (try wp_auto) <;> (try wp_if_destruct) <;> (try wp_auto)
      all_goals
        ihave H := HΦ $$ []
        · itrivial
        iExactEq H
        congr 2
        unfold txn.rangeLimitOf
        simp only [hdef, hlimo, hh]
        split <;> simp_all <;> word
    · wp_auto
      ihave H := HΦ $$ []
      · itrivial
      iExactEq H
      congr 2
      unfold txn.rangeLimitOf
      simp only [hh, _root_.or_true, ↓reduceIte]
      rfl
  · ihave H := HΦ $$ []
    · itrivial
    iExactEq H
    congr 2
    unfold txn.rangeLimitOf
    simp only [hdef, Hif, decide_false, _root_.true_or, ↓reduceIte]
    rfl

end proof

end EtcdGrove
end Perennial
