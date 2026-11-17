/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__commitTo`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__commitTo
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__mut

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

theorem State.commitTo.wp_proof (wp_mut : State.mut.spec (GF := GF) (hG := hG)) :
    State.commitTo.spec (GF := GF) (hG := hG) := by
  intro p st M i c
  wp_start as ⟨Hst, %Hi⟩
  wp_auto
  mut_open p, st, M, i, Hst
  wp_auto
  wp_if_destruct
  · close_copy { gc with CommitIndex' := c },
      (fun v => { v with commitIndex := max v.commitIndex (sint.Z c) }),
      ⟨Hcf.1, Hcf.2.1, Hcf.2.2.1, Hcf.2.2.2.1, by simp only; omega, Hcf.2.2.2.2.2⟩
    iapply HΦ; unfold State.commitTo; iexact Hs
  · close_copy gc,
      (fun v => { v with commitIndex := max v.commitIndex (sint.Z c) }),
      ⟨Hcf.1, Hcf.2.1, Hcf.2.2.1, Hcf.2.2.2.1, by simp only; omega, Hcf.2.2.2.2.2⟩
    iapply HΦ; unfold State.commitTo; iexact Hs

end proof

end Etcdraft
end EtcdGrove
end Perennial
