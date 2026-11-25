-- The copy for the part `KvRaft/` of `RaftNoAx/Proof/github_com/mit_pdos/etcd_grove/examples/raft/kvdurablenoax/withTimeout.lean` (etc/copy-part.py; rerun it, do not edit).
/- Lean-first (no Rocq counterpart); the part's own (raft without hand-written axioms,
`notes/raft-noax-part.md`). Proof of `withTimeout`'s spec.
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.withTimeout
public import Perennial.Proof.context.Results
public import Perennial.Proof.time.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]

/-- Perennial's `wp_WithCancel_Background` (no `Done` proposition) and `time.wp_AfterFunc`, the
timer's function `cancel` itself (which never panics). -/
theorem withTimeout.wp_proof : withTimeout.spec (GF := GF) (hG := hG) := by
  intro d
  wp_start as Hcci
  ihave #Hctxinit : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  wp_auto
  wp_apply context.wp_Background
  try wp_auto
  wp_apply (_root_.Perennial.context.wp_WithCancel_Background iprop(True)) $$ [$Hctxinit $Hcci]
    as %ctx' %γ' %cancel ⟨#Hcancel, #Hctx, -, #Hfrom⟩
  try wp_auto
  wp_apply time.wp_AfterFunc $$ [] as %t -
  · iapply Hcancel
    · imodintro; itrivial
    inext
    iintro -
    ipureintro; exact isPanic_intoVal _
  try wp_auto
  iapply HΦ
  iframe Hctx Hfrom
  imodintro
  iintro %Φ' - HΦ'
  iapply Hcancel
  · imodintro; itrivial
  inext
  iintro -
  iapply HΦ'
  itrivial

end proof

end kvraft
end EtcdGrove
end Perennial
