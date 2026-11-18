/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/lessor__clearScheduledLeasesCheckpoints.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__clearScheduledLeasesCheckpoints

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

theorem lease.lessor.clearScheduledLeasesCheckpoints.wp_proof :
    lease.lessor.clearScheduledLeasesCheckpoints.spec (GF := GF) (hG := hG) := by
  intro lp h
  wp_start as Hf
  wp_auto
  wp_apply (wp_slice_make2 (V := Loc) (t := go.GoType.PointerType LeaseWithTime.ty)) as %s ⟨Hs, Hcap⟩
  · ipureintro; decide
  (try wp_auto)
  iapply HΦ
  iexists s
  iframe
  iunfold queueAt
  iframe
  iapply BigSepL.bigSepL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial
