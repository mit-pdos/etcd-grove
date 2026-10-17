/-
Proof of the spec of the same name (unit P3b). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.isRPCSupportedForLearner

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- Distinct request types are distinct, and `learnerServes` unfolds (the types are `Named` by
distinct strings; `irreducible`, unfolded by name). -/
local macro "learner_simp" : tactic => `(tactic| (simp [v3rpc.learnerServes,
  etcdserverpb.DefragmentRequest.ty, etcdserverpb.StatusRequest.ty,
  etcdserverpb.RangeRequest.ty] at *))

theorem v3rpc.isRPCSupportedForLearner.wp_proof :
    v3rpc.isRPCSupportedForLearner.spec (GF := GF) (hG := hG) := by
  intro req
  wp_start as Hl
  iunfold v3rpc.learnerReqOk at Hl
  icases Hl with ⟨%Hreq, #Hser⟩
  rcases Hreq with rfl | ⟨t, l, rfl⟩
  · -- the nil interface: no case matches
    wp_auto
    iapply HΦ
    iexists false
    isplitl
    · iintro %r %hr
      simp at hr
    · ipureintro
      learner_simp
  · wp_auto
    wp_if_destruct
    · -- `*DefragmentRequest` (the case etcd-io/etcd#21862 adds)
      iapply HΦ
      iexists false
      isplitl
      · iintro %r %hr
        learner_simp
      · ipureintro
        learner_simp
        exact ⟨l, rfl⟩
    · wp_if_destruct
      · -- `*StatusRequest`
        iapply HΦ
        iexists false
        isplitl
        · iintro %r %hr
          learner_simp
        · ipureintro
          learner_simp
          exact ⟨l, rfl⟩
      · by_cases ht : t = go.GoType.PointerType etcdserverpb.RangeRequest.ty
        · -- `*RangeRequest`: its `Serializable`
          subst ht
          ihave ⟨%b, #Hb⟩ := Hser $$ %l %rfl
          wp_auto
          iapply HΦ
          iexists b
          isplitl
          · iintro %r %hr
            simp at hr
            have := go.intoVal_inj hr
            subst this
            iexact Hb
          · ipureintro
            learner_simp
            exact fun _ => ⟨l, rfl⟩
        · -- anything else
          simp only [ht, ite_false, decide_false]
          wp_auto
          iapply HΦ
          iexists false
          isplitl
          · iintro %r %hr
            simp at hr
            exact absurd hr.1 ht
          · ipureintro
            learner_simp
            exact ⟨fun h => absurd h (by assumption), fun h => absurd h (by assumption)⟩

/-- **The new spec implies the old** (etcd-io/etcd#21862 is compatible): the old postcondition
was `True`, so callers proved against the old spec (`newUnaryInterceptor`) are unaffected. -/
theorem v3rpc.isRPCSupportedForLearner.spec_implies_old
    (h : v3rpc.isRPCSupportedForLearner.spec (GF := GF) (hG := hG)) :
    v3rpc.isRPCSupportedForLearner.spec_old (GF := GF) (hG := hG) := by
  intro req
  iintro %Φ Hpre HΦ
  iapply h req $$ Hpre
  inext
  iintro %b -
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
