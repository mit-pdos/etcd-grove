/-
Lean-first (no Rocq counterpart). **`raft.Step`'s traced bundle on `MsgProp` at a leader**
(2026-11-11, trace-check Q8 stage 1 slice 24a, `notes/decisions.md`, "Q8 stage 1 (slice 24a)").

A leader's proposal runs `appendEntry`'s two gates and `bcastAppend`'s (`leaderGates`' `"Hgprep"`,
`"Hgpack"`, `"#Hgpapp"`); the caller's resources are three families:

- before the lines (`G0`, `G1`, at the outbox of `s` only): a local path's family at `s` (`lineF`);
- after the `Replicate` lines (`Gp1`): raft's ghost state at the proposed state (`ghost_stepProp`, run
  inside `"Hgprep"` with what `Step` lends it, `propLend`), the capability pinned after the last line
  (`RepPin`, `TracedRaftStepPropRep.lean`);
- after the self-acknowledgement (`Gp2`, at an outbox longer than `s`'s): raft's ghost state at the
  proposed state, the traced family at the idle server of the appended state (`propF`).

The close tells the two outcomes apart by the outbox's length (`StepEnd`'s `LeaderProposeResult`):
dropped, the ghost state back at `s` (`CloseAt`: the batch not appended); appended, at the proposed state
(`CloseMid`).

**What the path premises** beyond `stepBundle_traced.on`'s (`PropLead`, a path reading the cluster's
names and the batch: `stepBundle_traced.onG`): a non-empty batch of normal entries (the traced node
proposes no configuration change, and the specification's `ClientRequest` is one `Replicate` line per
entry), and a cluster with a bootstrap log (a leader's term is then `≥ 2`, its log past the bootstrap
entries). The node API supplies them (`raft.Step`'s own premises have the first, `Hp3`; the second is
`stepBundle_traced.on`'s premise for `MsgHeartbeat`/`MsgApp`); they become premises of
`stepBundle_traced.on` when the paths are assembled.
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStepPropRep

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A leader's last entry is of its term, and its term `≥ 2` in a cluster with a bootstrap log**
(raft's campaign record, `campOwn`: the full log extends the campaign log by an entry of the term;
`isCamp_boot`), at an uncompacted log. -/
theorem ownStepGhost_leadLast (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState)
    (hr : s.role = .leader) (hb : s.logst.prev = base0) :
    ownStepGhost (GF := GF) γ md c id s ⊢
      ⌜(∃ x, (toPState s).log.getLast? = some x ∧ x.Term' = s.term) ∧
        (γ.reBoot ≠ [] → 2 ≤ uint.Z s.term)⌝ ∗ ownStepGhost γ md c id s := by
  apply persistent_entails_right
  iintro H
  iunfold ownStepGhost at H
  icases H with ⟨Hg, -⟩
  unfold ownRaftGhost
  icases Hg with ⟨%γs, %V, %πc, %kl, H⟩
  iNamed H
  unfold ownLogGhost
  icases Hlg with ⟨%γm, %terms, %fp, %γw, %wins, Hlg⟩
  iNamed Hlg
  have hrole : (toPState s).role = .leader := by rw [toPState_role, hr]; rfl
  have hco : ∀ (camps : GMap w64 (List EntryM × w64)) (F : List EntryM),
      campOwn (GF := GF) γ id camps (toPState s) F =
        iprop(∃ F0, isCamp γ id (toPState s).term F0 ∗
          ⌜F0 <+: F ∧ plogLastIndexZ base0 F0 < plogLastIndexZ base0 F ∧
            (plogLast base0 F).term' = (toPState s).term⌝) := by
    intro camps F; unfold campOwn; rw [hrole]
  rw [hco]
  icases Hcown with ⟨%F0, #Hc0, %HF0⟩
  icases isCamp_boot γ id (toPState s).term F0 $$ Hc0 with %Hbt
  ipureintro
  obtain ⟨Hfo, -, -⟩ := Hfull
  have hfp : fp = [] := by
    have h := Hfo.1
    have hb' : (toPState s).base = base0 := hb
    rw [hb', base0_index] at h; exact List.eq_nil_of_length_eq_zero (by omega)
  subst hfp
  obtain ⟨-, hlt, hlast⟩ := HF0
  simp only [List.nil_append] at hlt hlast
  refine ⟨?_, Hbt.2⟩
  cases hl : (toPState s).log.getLast? with
  | none =>
    exfalso
    rw [List.getLast?_eq_none_iff] at hl
    rw [hl] at hlt
    simp only [plogLastIndexZ, List.length_nil] at hlt
    have := plogLastIndexZ_nonneg base0 F0
    unfold plogLastIndexZ at this
    omega
  | some x =>
    refine ⟨x, rfl, ?_⟩
    unfold plogLast at hlast
    rw [hl] at hlast
    exact hlast

end ghost

end EtcdGrove
end Perennial
