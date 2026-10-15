/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.noSideEffect
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.UberLemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem apply.noSideEffect.wp_proof :
    apply.noSideEffect.spec (GF := GF) (hG := hG) := by
  intro p rq
  wp_start as #Hr
  iunfold apply.internalRaftRequestIs at Hr
  simp only [apply.presentIs]
  icases Hr with ⟨%Hpn, -, -, ⟨%l1, #F1, #H1⟩, -, -, -, -, -, -, -, -, -, -,
    ⟨%l4, #F4, %H4⟩, -, -, -, ⟨%l2, #F2, #H2⟩, -, -, -, -, -, -, -, ⟨%l3, #F3, #H3⟩, -, -,
    -, -, -, -⟩
  ihave %H1 := apply.optReqIs_nil l1 rq.range _ apply.rangeRequestIs_nn $$ H1
  ihave %H2 := apply.optReqIs_nil l2 rq.authUserGet _ apply.authUserGetIs_nn $$ H2
  ihave %H3 := apply.optReqIs_nil l3 rq.authRoleGet _ apply.authRoleGetIs_nn $$ H3
  wp_auto
  by_cases h1 : l1 = null
  case neg =>
    simp only [h1, decide_false, Bool.not_false]
    wp_auto
    iapply HΦ; ipureintro
    have : rq.range ≠ none := fun h => h1 (H1.2 h)
    simp [apply.noSideEffect, Option.isSome_iff_ne_none.mpr this]
  simp only [h1, decide_true, Bool.not_true]
  wp_auto
  by_cases h2 : l2 = null
  case neg =>
    simp only [h2, decide_false, Bool.not_false]
    wp_auto
    iapply HΦ; ipureintro
    have : rq.authUserGet ≠ none := fun h => h2 (H2.2 h)
    simp [apply.noSideEffect, Option.isSome_iff_ne_none.mpr this]
  simp only [h2, decide_true, Bool.not_true]
  wp_auto
  by_cases h3 : l3 = null
  case neg =>
    simp only [h3, decide_false, Bool.not_false]
    wp_auto
    iapply HΦ; ipureintro
    have : rq.authRoleGet ≠ none := fun h => h3 (H3.2 h)
    simp [apply.noSideEffect, Option.isSome_iff_ne_none.mpr this]
  simp only [h3, decide_true, Bool.not_true]
  wp_auto
  iapply HΦ; ipureintro
  have e1 := H1.1 h1
  have e2 := H2.1 h2
  have e3 := H3.1 h3
  by_cases h4 : l4 = null
  · have : rq.authStatus = false := by
      cases hs : rq.authStatus
      · rfl
      · exact absurd (H4.2 hs) (by simp [h4])
    simp [apply.noSideEffect, e1, e2, e3, h4, this]
  · simp [apply.noSideEffect, e1, e2, e3, h4, H4.1 h4]

end proof

end EtcdGrove
end Perennial
