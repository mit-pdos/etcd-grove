module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalNode__successor
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalNode__min

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3.adt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

theorem adt.intervalNode.successor.wp_proof
    (h_min : adt.intervalNode.min.spec (GF := GF) (hG := hG)) :
    adt.intervalNode.successor.spec (GF := GF) (hG := hG) := by
  intro z s rp r hr
  wp_start as ⟨Hzr, Hn⟩
  obtain ⟨c, l, e, r', rfl⟩ : ∃ c l e r', r = .node c l e r' := by
    cases r with
    | leaf => exact absurd rfl hr
    | node c l e r' => exact ⟨c, l, e, r', rfl⟩
  ihave %Hrp := adt.ownNode_node_ne _ _ _ _ _ _ _ _ $$ Hn
  wp_auto
  rw [_root_.decide_eq_false Hrp.1]
  wp_auto
  wp_apply h_min rp s z (.node c l e r') (by simp) $$ [Hn] as %y ⟨%A, %ls, %yp, %cy, %ye, %yr, HA, Hy, %Hy⟩
  · iframe
  iapply HΦ
  iframe
  ipureintro; exact Hy

end proof

end EtcdGrove
end Perennial
