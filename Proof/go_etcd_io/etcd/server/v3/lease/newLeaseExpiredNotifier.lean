/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/newLeaseExpiredNotifier.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.newLeaseExpiredNotifier

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.newLeaseExpiredNotifier.wp_proof :
    lease.newLeaseExpiredNotifier.spec (GF := GF) (hG := hG) := by
  wp_start as -
  wp_auto
  wp_apply (wp_map_make1 (V := Loc) LeaseID.ty (go.GoType.PointerType LeaseWithTime.ty))
    as %mp Hm
  (try wp_auto)
  wp_apply (wp_slice_make2 (V := Loc) (t := go.GoType.PointerType LeaseWithTime.ty)) as %s ⟨Hs, Hcap⟩
  · ipureintro; decide
  (try wp_auto)
  iStructNamed «$r0»
  (try wp_auto)
  iapply HΦ
  iunfold notifierAt
  iexists mp, s, ∅, []
  iframe
  iunfold queueAt
  iframe
  isplitl []
  · iapply BigSepL.bigSepL_nil.2; itrivial
  ipureintro
  simp

end proof

end EtcdGrove
end Perennial
