/-
**The driver's DaemonSet meets `dsCreate_step`'s premises** (track C's `newDsOk`, the driver's
`newDaemonSet()`, to `S1Writes.dsCreate_step`). Lean-first; the autoverify run, track B.

`newDsOk_create`: the admin's create of a `newDsOk` DaemonSet into a state with no DaemonSet
stores a well-formed one (`dsWf`: the model's create strategy keeps the namespace, name, selector
and template, sets a revision history limit and a zero status), and no other DaemonSet shares its
revision name (there is none).
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.daemon.S1Writes
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain.Defs

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open apimodel consistency

section pure
variable [GooseExts]

/-- **The driver's DaemonSet create meets `dsCreate_step`'s premises.** -/
theorem newDsOk_create (σ : St) (ns : GoString) (dreq : kd.apps.DaemonSet)
    (t : k8s_io.apimachinery.pkg.apis.«meta».v1.Time) (hd : dsmain.newDsOk dreq)
    (hnone : ∀ o, dsAtOwner σ o = none) :
    ∃ d, (createApply .daemonSets ns (.ds dreq) σ t).1 = .ds d ∧ dsWf d ∧
      ∀ o' d', dsAtOwner σ o' = some d' → d'.ObjectMeta'.Namespace' = d.ObjectMeta'.Namespace' →
        crName d' ≠ crName d := by
  obtain ⟨hns, hnm, hs1, hs2, hsel, hcov, hunb, hfin⟩ := hd
  have hne : dreq.ObjectMeta'.Namespace' ≠ go!"" := by rw [hns]; decide
  have hnn : dreq.ObjectMeta'.Name' ≠ go!"" := by rw [hnm]; decide
  obtain ⟨d, hd⟩ : ∃ d, (createApply .daemonSets ns (.ds dreq) σ t).1 = .ds d := by
    simp [createApply, createNs, Res.namespaced, hne, Obj.modMeta, Obj.setMeta, Obj.meta, prepareD]
  refine ⟨d, hd, ?_, fun o' d' h => by rw [hnone] at h; cases h⟩
  simp [createApply, createNs, Res.namespaced, hne, hnn, Obj.modMeta, Obj.setMeta, Obj.meta,
    prepareD, prepareDaemonSetD] at hd
  subst hd
  constructor
  · exact ⟨hs1, hs2⟩
  · exact hne
  · exact hsel
  · exact hcov
  · exact hunb
  · exact hfin
  · simp
  · simp [kd.apps.DaemonSetStatus.zero]

end pure

end dsctl
end EtcdGrove
end Perennial
