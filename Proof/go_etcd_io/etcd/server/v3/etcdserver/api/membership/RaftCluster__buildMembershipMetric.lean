/-
Proof of `Spec/.../membership/RaftCluster__buildMembershipMetric.lean` (claim #34, stage 2,
2026-11-25): with a non-zero local id, a range over the members map and one over the removed map,
each setting `knownPeers.WithLabelValues(c.localID.String(), p.String())` (as
`updateMembershipMetric`'s proof), over the vector's `WithLabelValues` and the gauge's `Set`.
Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__buildMembershipMetric
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr
public import Spec.github_com.prometheus.client_golang.prometheus.GaugeVec__WithLabelValues
public import Spec.github_com.prometheus.client_golang.prometheus.gauge__Set
public import Proof.go_etcd_io.etcd.client.pkg.v3.types.IDStr

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

theorem membership.RaftCluster.buildMembershipMetric.wp_proof
    (hIDStringPtr : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (hWLV : prometheus.GaugeVec.WithLabelValues.spec (GF := GF) (hG := hG))
    (hSet : prometheus.gauge.Set.spec (GF := GF) (hG := hG)) :
    membership.RaftCluster.buildMembershipMetric.spec (GF := GF) (hG := hG) := by
  intro c lid dq1 dq2 dq3 dq4 dq5 mp rp ms rm
  wp_start as ⟨Hlid, Hmf, Hmp, Hrf, Hrp⟩
  ihave Hmi : (go_etcd_io.etcd.server.v3.etcdserver.api.membership.membershipInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, ⟨%vKP, #HKP, %HKPl⟩⟩
  ihave #Hprom : isPkgInitSome (PROP := IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus $$ []
  · iPkgInit
  ihave #Htpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types $$ []
  · iPkgInit
  wp_auto
  wp_if_destruct
  · iapply HΦ
    iframe
  (try wp_auto)
  -- `for p := range c.members { knownPeers.WithLabelValues(...).Set(1) }`
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (K := w64) (V := Loc) (fun (_keys : List w64) (_i : Int) => iprop(
      ∃ x : w64, "p" ∷ p_ptr ↦ x ∗ "Hlid" ∷ membership.rcLocalIDAddr c ↦{dq1} lid ∗
        "Hcp" ∷ c_ptr ↦ c)) $$ Hmp
  iintro %keys -
  isplitl [p Hlid c]
  · iexists _; iframe p Hlid c
  isplitr
  · imodintro
    iintro %i %key %vv - HP
    icases HP with ⟨%x, p, Hlid, Hcp⟩
    (try wp_auto)
    wp_apply hIDStringPtr _ dq1 lid $$ [$Hlid] as %ls ⟨Hlid, %Hls⟩
    wp_apply hIDStringPtr $$ [$p] as %ps ⟨p, %Hps⟩
    wp_apply wp_slice_literal (V := GoString) [ls, ps]
    isplitr
    · ipureintro; rfl
    iintro %lsl ⟨Hlsl, -⟩
    (try wp_auto)
    wp_apply hWLV vKP _ [go!"Local", go!"Remote"] [ls, ps] _ $$ [$Hlsl] as %g ⟨%gi, %Hgi, -, #HgR, -⟩
    · iframe #
      ipureintro
      refine ⟨HKPl, by simp, fun v hv => ?_⟩
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
      rcases hv with rfl | rfl
      · exact utf8Valid_of_ascii _ (Hls ▸ types.idStr_ascii _)
      · exact utf8Valid_of_ascii _ (Hps ▸ types.idStr_ascii _)
    subst Hgi
    iunfold EtcdGrove.prometheus.metric.isGauge at HgR
    icases HgR with ⟨%l, %Hl, #Hcell⟩
    subst Hl
    (try wp_auto)
    wp_apply hSet $$ [$Hcell]
    (try wp_auto)
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists _; iframe p Hlid Hcp
  iintro HP Hmp
  icases HP with ⟨%x, -, Hlid, Hcp⟩
  (try wp_auto)
  -- `for p := range c.removed { knownPeers.WithLabelValues(...).Set(0) }`
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (K := w64) (V := Bool) (fun (_keys : List w64) (_i : Int) => iprop(
      ∃ x : w64, "p" ∷ p_ptr ↦ x ∗ "Hlid" ∷ membership.rcLocalIDAddr c ↦{dq1} lid ∗
        "Hcp" ∷ c_ptr ↦ c)) $$ Hrp
  iintro %keys -
  isplitl [p Hlid Hcp]
  · iexists _; iframe p Hlid Hcp
  isplitr
  · imodintro
    iintro %i %key %vv - HP
    icases HP with ⟨%x, p, Hlid, Hcp⟩
    (try wp_auto)
    wp_apply hIDStringPtr _ dq1 lid $$ [$Hlid] as %ls ⟨Hlid, %Hls⟩
    wp_apply hIDStringPtr $$ [$p] as %ps ⟨p, %Hps⟩
    wp_apply wp_slice_literal (V := GoString) [ls, ps]
    isplitr
    · ipureintro; rfl
    iintro %lsl ⟨Hlsl, -⟩
    (try wp_auto)
    wp_apply hWLV vKP _ [go!"Local", go!"Remote"] [ls, ps] _ $$ [$Hlsl] as %g ⟨%gi, %Hgi, -, #HgR, -⟩
    · iframe #
      ipureintro
      refine ⟨HKPl, by simp, fun v hv => ?_⟩
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
      rcases hv with rfl | rfl
      · exact utf8Valid_of_ascii _ (Hls ▸ types.idStr_ascii _)
      · exact utf8Valid_of_ascii _ (Hps ▸ types.idStr_ascii _)
    subst Hgi
    iunfold EtcdGrove.prometheus.metric.isGauge at HgR
    icases HgR with ⟨%l, %Hl, #Hcell⟩
    subst Hl
    (try wp_auto)
    wp_apply hSet $$ [$Hcell]
    (try wp_auto)
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists _; iframe p Hlid Hcp
  iintro HP Hrp
  icases HP with ⟨%x, -, Hlid, Hcp⟩
  (try wp_auto)
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
