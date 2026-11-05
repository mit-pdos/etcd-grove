module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.preOk
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.rvString

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg state)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

set_option hygiene false in
/-- `preOk`'s resource-version test, the UID's passed (`hU`). -/
local macro "preok_rest" : tactic => `(tactic| (
  cases hr : x.HasPreRV'
  · (try wp_auto)
    rw [show true = preOkL x o by simp [preOkL, hU, hr]]
    iapply HΦ; itrivial
  · (try wp_auto)
    wp_apply wp_rvString
    (try wp_auto)
    by_cases he2 : x.PreRV' = rvStr o.ResourceVersion'
    · rw [decide_eq_true he2]
      (try wp_auto)
      rw [show true = preOkL x o by simp [preOkL, hU, hr, he2]]
      iapply HΦ; itrivial
    · rw [decide_eq_false he2]
      (try wp_auto)
      rw [show false = preOkL x o by simp [preOkL, hU, hr, he2]]
      iapply HΦ; itrivial))

theorem preOk.wp_proof (wp_rvString : rvString.spec (GF := GF) (hG := hG)) :
    preOk.spec (GF := GF) (hG := hG) := by
  intro x o
  wp_start as -
  wp_auto
  cases hu : x.HasPreUID'
  · have hU : (if x.HasPreUID' then decide (x.PreUID' = o.UID') else true) = true := by simp [hu]
    wp_auto
    preok_rest
  · wp_auto
    by_cases he : x.PreUID' = o.UID'
    · have hU : (if x.HasPreUID' then decide (x.PreUID' = o.UID') else true) = true := by
        simp [hu, he]
      rw [decide_eq_true he]
      wp_auto
      preok_rest
    · rw [decide_eq_false he]
      wp_auto
      rw [show false = preOkL x o by simp [preOkL, hu, he]]
      iapply HΦ; itrivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
