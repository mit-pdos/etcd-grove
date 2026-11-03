/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Cluster__config.lean`. Lean-first
(no Rocq counterpart).

The literal's fields: ticks `10` and `1`, the options' sizes (`OptsOk`: a positive window of at most
256, not both sizes zero), the store's storage and logger, the rest zero.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__config
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.DefsLaws

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

theorem Cluster.config.wp_proof : Cluster.config.spec (GF := GF) (hG := hG) := by
  intro γ vs dir c id st applied Hid0 Hidb
  wp_start as Hc
  iunfold isClusterC at Hc
  iNamed Hc
  icases typedPointsto_split _ _ _ $$ Hopts with Hos
  simp only [TypedPointsto.typedPointstoDef]
  icases Hos with ⟨#oV, #oP, #oC, #oS, #oM, #oMC, #oI, -⟩
  wp_auto
  irename «$r0» => Hp
  generalize «$r0_ptr» = p at *
  iapply HΦ
  iexists _
  iframe Hp
  ipureintro
  obtain ⟨⟨_, _, Hm1, Hm2, Hsz⟩, -⟩ := Ho
  unfold kdCfgOk ConfigValid
  refine ⟨rfl, rfl, rfl, ⟨Hid0, ?_, ?_, ⟨by simp only; decide, by simp only; decide⟩, ?_, Hm1, Or.inl rfl, ?_, Or.inl rfl⟩,
    by word, rfl, rfl, rfl, Hsz, rfl, rfl⟩
  · intro h; simp only at h; rw [h] at Hidb; word
  · intro h; simp only at h; rw [h] at Hidb; word
  · simp [interface.mkOk]
  · simp [interface.mkOk]

end proof

end kvdurable
end EtcdGrove
end Perennial
