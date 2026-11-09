/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__AppendEntries`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__AppendEntries
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

theorem State.AppendEntries.wp_proof
    (wp_AEIRP : State.AppendEntriesInRangeToPeer.spec (GF := GF) (hG := hG)) :
    State.AppendEntries.spec (GF := GF) (hG := hG) := by
  intro p st i j b e o
  wp_start as ⟨#Hst, %Hi, %Hpok, %hb1, %hb2, %he1, %he2, %Ho⟩
  wp_auto
  wp_apply wp_AEIRP p st go!"app" "app" i j b e o $$ [Hst] as %q Hq
  · iframe Hst; ipureintro; exact ⟨strRel_app, Hi, Hpok, hb1, hb2, he1, he2, Ho⟩
  try wp_auto
  iapply HΦ
  iexact Hq

end proof

end Etcdraft
end EtcdGrove
end Perennial
