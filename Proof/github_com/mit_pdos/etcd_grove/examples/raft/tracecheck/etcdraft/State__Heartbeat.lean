/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__Heartbeat`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__Heartbeat
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__AppendEntriesInRangeToPeer

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

theorem State.Heartbeat.wp_proof
    (wp_AEIRP : State.AppendEntriesInRangeToPeer.spec (GF := GF) (hG := hG)) :
    State.Heartbeat.spec (GF := GF) (hG := hG) := by
  intro p st i j o
  wp_start as ⟨#Hst, %Hi, %Hpok, %Ho⟩
  wp_auto
  wp_apply wp_AEIRP p st go!"heartbeat" "heartbeat" i j (W64 1) (W64 1) o $$ [Hst] as %q Hq
  · iframe Hst; ipureintro; exact ⟨strRel_heartbeat, Hi, Hpok, by decide, by decide, by decide, by decide, Ho⟩
  try wp_auto
  iapply HΦ
  iexact Hq

end proof

end Etcdraft
end EtcdGrove
end Perennial
