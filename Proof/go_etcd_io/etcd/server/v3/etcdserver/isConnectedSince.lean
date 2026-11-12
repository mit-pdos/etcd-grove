/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/isConnectedSince.lean`. Lean-first (no Rocq counterpart); unit P1b (2026-10-14).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.isConnectedSince
public import Spec.time.Time__IsZero

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem isConnectedSince.wp_proof
    (hZ : time.Time.IsZero.spec (GF := GF) (hG := hG)) :
    isConnectedSince.spec (GF := GF) (hG := hG) := by
  intro tr since remote
  wp_start as #Htr
  iunfold rafthttp.isTransporter at Htr
  icases Htr with ⟨%ti, %Hti, #HAS⟩
  subst Hti
  ihave #Ptime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  wp_auto
  wp_apply HAS $$ %remote as %t -
  (try wp_auto)
  wp_apply hZ $$ [$t] as %bz t
  cases bz
  · (try wp_auto)
    wp_apply time.Time.wp_ptr_Before $$ [$t] as %bb t
    iapply HΦ
    itrivial
  · (try wp_auto)
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
