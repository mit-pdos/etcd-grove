/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/lessor__clearScheduledLeasesCheckpoints.lean`. Lean-first (no Rocq counterpart).
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.lessor.clearScheduledLeasesCheckpoints.wp_proof :
    lease.lessor.clearScheduledLeasesCheckpoints.spec (GF := GF) (hG := hG) := by
  intro lp h
  wp_start as Hh
  (try wp_auto)
  wp_apply (wp_slice_make2 (V := Loc) (W64 0)) as %s ⟨Hs, Hcap⟩
  · ipureintro; word
  (try wp_auto)
  iapply HΦ
  iexists s
  iframe
  iunfold queueAt
  simp only [List.map_nil, List.replicate_zero]
  iframe
  iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; itrivial

end proof

end EtcdGrove
end Perennial
