/-
The proof of `rpctransport.isHeartbeat`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.isHeartbeat

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Assumptions]
variable [π : Net.NetProtoGS] [net.rpc.Assumptions] [net.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.rpctransport


theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.isHeartbeat.wp_proof :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.isHeartbeat.spec (GF := GF) (hG := hG) := by
  intro a dq rq dq1 ad ld ptrs
  wp_start as ⟨Ha, Had, Hld, Hents⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ha
  ihave %Hel := ownSlice_len _ _ _ $$ Hents
  iStructNamed Ha
  ihave %Hnn2 := typedPointsto_not_null _ _ _ $$ RPCHeader
  iStructNamed RPCHeader
  (try (irename : ("_" ∷ True : IProp GF) => Hjunk; iclear Hjunk))
  (try (irename : ("_" ∷ True : IProp GF) => Hjunk; iclear Hjunk))
  wp_auto
  wp_if_destruct
  all_goals (try wp_auto)
  all_goals (repeat (first | (wp_if_destruct <;> try wp_auto) | wp_auto))
  all_goals (try (simp only [← decide_not]))
  all_goals (repeat (first | (wp_if_destruct <;> try wp_auto) | wp_auto))
  all_goals (try (simp only [← decide_not]))
  all_goals (repeat wp_if_destruct)
  all_goals (try (simp only [← decide_not]))
  all_goals (repeat wp_if_destruct)
  all_goals (try (simp only [← decide_not]))
  all_goals (
    ihave Hh : (a.[github_com.hashicorp.raft.AppendEntriesRequest, go!"RPCHeader"] ↦{dq} rq.RPCHeader' : IProp GF) $$ [ProtocolVersion ID Addr]
    · iapply typedPointsto_combine _ _ _ Hnn2; simp only [TypedPointsto.typedPointstoDef]; iframe
    ihave Ha : (a ↦{dq} rq : IProp GF) $$ [Hh Term Leader PrevLogEntry PrevLogTerm Entries LeaderCommitIndex]
    · iapply typedPointsto_combine _ _ _ Hnn; simp only [TypedPointsto.typedPointstoDef]; iframe
    iapply HΦ; iframe Ha Had Hld Hents; ipureintro)
  all_goals (intro hb; first
    | exact absurd hb (by decide)
    | (refine ⟨‹_›, ?_, ‹_›⟩
       apply List.eq_nil_of_length_eq_zero
       have h1 := Hel.1
       rw [‹rq.Entries'.len = W64 0›] at h1
       have h0 : sint.nat (W64 0) = 0 := rfl
       rw [h1, h0]))

end proof

end Perennial
