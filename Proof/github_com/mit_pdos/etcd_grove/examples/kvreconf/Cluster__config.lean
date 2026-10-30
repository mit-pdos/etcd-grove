/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/Cluster__config.lean`. Lean-first
(no Rocq counterpart).

The literal's fields: ticks `10` and `1`, the options' sizes (`OptsOk`: a positive window of at most
256, not both sizes zero), the store's storage and logger, the rest zero.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__config

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KvrStor GF]

attribute [local instance] kvrStorageModel

theorem Cluster.config.wp_proof : Cluster.config.spec (GF := GF) (hG := hG) := by
  intro γr vs c id st Hid0 Hidb
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
  unfold CfgOk ConfigValid
  refine ⟨rfl, rfl, rfl, ⟨Hid0, ?_, ?_, ⟨by simp only; decide, by simp only; decide⟩, ?_, Hm1, Or.inl rfl, ?_, Or.inl rfl⟩,
    by word, rfl, rfl, rfl, Hsz, rfl, rfl⟩
  · intro h; simp only at h; rw [h] at Hidb; word
  · intro h; simp only at h; rw [h] at Hidb; word
  · simp [interface.mkOk]
  · simp [interface.mkOk]

end proof

end kvreconf
end EtcdGrove
end Perennial
