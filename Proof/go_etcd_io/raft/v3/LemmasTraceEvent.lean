/-
Lean-first (no Rocq counterpart). `traceEvent`'s helper `wp_makeTracingMessage_arg` (`makeTracingMessage`
of the message argument, either case), moved out of the proof file (`traceEvent.lean`) on 2026-11-09
(trace-check Q8 stage 1 slice 6), so that the proof file exposes only its `wp_proof` (CLAUDE.md,
"Package APIs": added by slice 4, a layout violation, `etc/gen-interface.py --layout`).
-/
module

public import Spec.go_etcd_io.raft.v3.makeTracingMessage

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

/-- `makeTracingMessage` of the message argument, either case. -/
theorem wp_makeTracingMessage_arg (h : makeTracingMessage.spec (GF := GF) (hG := hG)) (m : Loc)
    (om : Option MsgArg) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ msgArg m om }}
      (App (Val #(functions makeTracingMessage [])) (Val #m))
    {{ (p : Loc), RET #p; msgArg m om ∗ tracingMsgRep p (msgArgTrace om) }} := by
  cases om with
  | none =>
    iintro %Φ ⟨#Hpkg, Hm⟩ HΦ
    simp only [msgArg]
    icases Hm with %Hm
    subst Hm
    iapply h.1 $$ [$Hpkg]
    inext
    iintro -
    iapply HΦ $$ %null
    simp only [msgArgTrace, tracingMsgRep]
    isplitr <;> ipureintro <;> trivial
  | some a =>
    simp only [msgArg]
    iintro %Φ ⟨#Hpkg, Hm⟩ HΦ
    iapply h.2 m a.dq a.dqe a.cap a.ms $$ [$Hpkg $Hm]
    inext
    iintro %p ⟨Hm, Hrep⟩
    iapply HΦ $$ %p
    simp only [msgArgTrace]
    iframe Hm Hrep

end proof

end EtcdGrove
end Perennial
