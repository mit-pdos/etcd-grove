/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__PreTimeout`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__PreTimeout

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

theorem State.PreTimeout.wp_proof : State.PreTimeout.spec (GF := GF) (hG := hG) := by
  intro p st i
  wp_start as ⟨#Hst, %Hi, %Hpv⟩
  read_server
  wp_auto
  lookup_server
  rw [Hrc.2.1, Hpv]
  wp_auto
  have : st.preTimeout (uint.nat i) = none := by
    unfold State.preTimeout; simp [Hpv]
  rw [this]
  iapply HΦ
  ipureintro; rfl

end proof

end Etcdraft
end EtcdGrove
end Perennial
