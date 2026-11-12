/-
Lean-first (no Rocq counterpart): the proof of `traceNodeEvent` (`Spec/go_etcd_io/raft/v3/traceNodeEvent.lean`).
-/
module

public import Spec.go_etcd_io.raft.v3.traceNodeEvent
public import Spec.go_etcd_io.raft.v3.traceEvent

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem traceNodeEvent.wp_proof
    (wp_traceEvent : traceEvent.spec (GF := GF) (hG := hG)) :
    traceNodeEvent.spec (GF := GF) (hG := hG) := by
  intro evt c r id s tl Q Hevt
  wp_start as ⟨#Htl, Hown, Hfire⟩
  wp_auto
  wp_apply wp_traceEvent evt r null map.nil tl s.gh.tr (NodeEvOf evt id s c) Q
      (ownRaftPhysCV c c.voters r id s) $$ [$Htl Hown $Hfire] as HR
  · iapply trOwn_wand
    iframe Hown
    iintro Hphys
    iexists c, id, s, ownRaftPhysCV c c.voters r id s, none, noProps
    iframe Hphys
    isplitr
    · iapply raftReadLend_self
    isplitr
    · iapply msgLend_nil
    isplitr
    · iapply tracingPropsRep_nil
    isplitr
    · ipureintro
      exact ⟨Hevt, fun e h hm hc h1 h2 h3 => nodeEvOf_of_hdr h hm hc h1 h2 h3⟩
    iintro H; iexact H
  iapply HΦ $$ HR

end proof

end EtcdGrove
end Perennial
