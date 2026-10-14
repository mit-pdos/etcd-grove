/-
The refinement of the dynamic model (2026-10-14, reconfiguration stage B5): the ghost state, in
its dynamic mode (`RaftNames.reDyn = some (DynCfg.ofFold dec c0 h0)`: the configuration of a
committed prefix is its fold from `c0`), follows `StepR` steps with configurations changing by
applied conf entries (`Adm := AdmFold dec c0`, with the snapshot prefixes' records, below).

* `DynCfg.ofFold dec c0 h0`: the mode's configurations, `cfgFold dec c0`, with `fold_adjacent`
  for the one fact the ghost state uses (`DynCfg.adj`).
* `ownRaftGhostR γ dec c0 id r`: the node's ghost state in the dynamic mode (`ownRaftGhost ... true`)
  over `r.p`, with `RInv dec c0 r` (stage B3's invariant: the configuration is the fold of the
  full log's first `cidx` entries, I1, I3, the campaign guard), the records of `r.fp` (so it is
  the ghost state's full prefix, `FullOk_unique`), and a candidate's campaign record of its full
  log at its commit index.
* `ownRaftGhostR_env`: the step environment (`dynEnv`) the configuration-reading rules take,
  from `RInv`.
* `ownRaftGhostR_stepR`: every `StepR` derivation updates it, given the messages it consumed,
  their read credits, and the records of every snapshot prefix the derivation may restore
  (`S`, see below).

**The snapshot prefixes.** `StepR.snapRestore` takes the restored node's new full prefix `fp'`
from the rule, constrained only by `FullOk` and `Adm fp' cs'` (B3). A run whose `fp'` is not the
committed prefix the snapshot covers is not one of a real system (A3: the snapshot's
`ConfState` is its prefix's configuration, and later decoded conf entries depend on the prefix),
and the ghost state cannot follow it. The refinement therefore takes, for the derivation's
admissible prefixes `S`, their records (`□ ∀ fp, ⌜S fp⌝ -∗ logRecs γ base0 fp`): with records and
`FullOk`, `fp'` is the sender's committed prefix. The code (stage B7) chooses `fp'` from the
message's knowledge and supplies them.
-/
module

public import Proof.go_etcd_io.raft.v3.Protocol.Refinement
public import Proof.go_etcd_io.raft.v3.Protocol.StepRInv

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI GMap go_etcd_io.raft.v3

section dyn
variable [FfiSyntax]

/-- The dynamic configurations of a decoder and an initial configuration with `CfgOk`. -/
def DynCfg.ofFold (dec : CCDec) (c0 : CCState) (h0 : CfgOk c0) : DynCfg where
  fold P := (cfgFold dec c0 P).map (fun s => s.cfg)
  adj := by
    intro P1 P2 c1 c2 hp hc h1 h2
    obtain ⟨M, rfl⟩ := hp
    cases e1 : cfgFold dec c0 P1 with
    | none => rw [e1] at h1; cases h1
    | some s1 =>
      cases e2 : cfgFold dec c0 (P1 ++ M) with
      | none => rw [e2] at h2; cases h2
      | some s2 =>
        rw [e1] at h1; rw [e2] at h2
        simp only [Option.map_some, Option.some.injEq] at h1 h2
        subst h1 h2
        refine fold_adjacent dec (P1 ++ M) P1.length (P1 ++ M).length c0 s1 s2
          (by simp) ?_ h0 ?_ ?_
        · rw [List.take_length, List.take_left']
          · exact hc
          · rfl
        · rw [List.take_left']; exact e1; rfl
        · rw [List.take_length]; exact e2

/-- The configurations the dynamic model admits after a prefix: its fold (A3), among the
prefixes `S` (whose records the refinement takes, see the file header). -/
def AdmS (dec : CCDec) (c0 : CCState) (S : List raftpb.Entry → Prop) (l : List raftpb.Entry)
    (cs : CCState) : Prop :=
  AdmFold dec c0 l cs ∧ S l

theorem toNat_uZ (w : w64) : (uint.Z w).toNat = uint.nat w := by
  have := rUnat_eq w; omega

theorem cfgAt_of_fold {γ : RaftNames} {dec : CCDec} {c0 : CCState} {h0 : CfgOk c0}
    (HD : γ.dyn = some (DynCfg.ofFold dec c0 h0)) {P : List raftpb.Entry} {s : CCState}
    (h : cfgFold dec c0 P = some s) : CfgAt γ P s.cfg :=
  CfgAt.of_dyn HD (by simp [DynCfg.ofFold, h])

theorem reDyn_of {γ : RaftNames} {D : DynCfg} (HD : γ.dyn = some D) : γ.reDyn ≠ none := by
  intro h; rw [RaftNames.dyn_none h] at HD; cases HD

/-- No `MsgApp` received. -/
theorem noApp1 {dec : CCDec} {c0 : CCState} {m : Msg} (h : m.ty ≠ .app) :
    ∀ (r1 : RState) (m' : Msg), m' ∈ [m] → m'.ty = .app → RInv dec c0 r1 → AppKnow r1 m' := by
  intro r1 m' hm hty _
  rw [List.mem_singleton] at hm; subst hm; exact absurd hty h

theorem noApp0 {dec : CCDec} {c0 : CCState} :
    ∀ (r1 : RState) (m' : Msg), m' ∈ ([] : List Msg) → m'.ty = .app → RInv dec c0 r1 →
      AppKnow r1 m' := by
  intro r1 m' hm; cases hm

end dyn

section ghost
variable [FfiSyntax]
variable {GF : BundledGFunctors} [AllG GF] [InvGS GF]

/-- A node's ghost state in the dynamic mode, with its reconfiguration state (see the file
header). -/
def ownRaftGhostR (γ : RaftNames) (dec : CCDec) (c0 : CCState) (id : w64) (r : RState) :
    IProp GF :=
  iprop(ownRaftGhost γ id r.p true ∗ ⌜RInv dec c0 r⌝ ∗ logRecs γ base0 r.fp ∗
    (∀ (_ : r.p.role = .candidate), isCampK γ id r.p.term r.full r.p.commit))

/-- The step environment, from `RInv`: the full prefix, I1, the configuration index (the
commit index at a candidate, `RInv.cand_cfg`), I3 at a leader. -/
theorem ownRaftGhostR_env (γ : RaftNames) (dec : CCDec) (c0 : CCState) (h0 : CfgOk c0)
    (HD : γ.dyn = some (DynCfg.ofFold dec c0 h0)) (id : w64) (r : RState)
    (HI : RInv dec c0 r) :
    ⊢ logRecs (GF := GF) γ base0 r.fp -∗
      (∀ (_ : r.p.role = .candidate), isCampK γ id r.p.term r.full r.p.commit) -∗
      dynEnv γ id r.cfg.cfg r.p := by
  iintro #Hfr #Hc
  unfold dynEnv
  iright
  isplitr
  · ipureintro; exact reDyn_of HD
  have Hcl : r.cidx < 2 ^ 64 := by
    have := HI.cidx_commit; have := rUnat_eq r.p.commit; have := uint_Z_lt r.p.commit; omega
  by_cases hc : r.p.role = .candidate
  · iexists r.fp, r.p.commit
    iframe Hfr
    isplitr
    · ipureintro
      refine ⟨HI.full, ?_, Int.le_refl _, ?_, ?_, fun _ => rfl⟩
      · rw [toNat_uZ]; exact HI.i1
      · rw [toNat_uZ]; exact cfgAt_of_fold HD (HI.cand_cfg hc).1
      · intro hl; rw [hc] at hl; cases hl
    · rw [show r.fp ++ r.p.log = r.full from rfl]; iexact Hc
  · iexists r.fp, (W64 (r.cidx : Int))
    have Hw : (uint.Z (W64 (r.cidx : Int))).toNat = r.cidx := by
      rw [uint_Z_W64 _ (by omega) (by omega)]; simp
    iframe Hfr
    isplitr
    · ipureintro
      refine ⟨HI.full, ?_, ?_, ?_, ?_, fun h => absurd h hc⟩
      · rw [toNat_uZ]; exact HI.i1
      · rw [uint_Z_W64 _ (by omega) (by omega)]
        have := HI.cidx_commit; have := rUnat_eq r.p.commit; omega
      · rw [Hw]; exact cfgAt_of_fold HD HI.cfg
      · intro hl; rw [Hw]; exact HI.leader_drop_cidx hl
    · iintro %h; exact absurd h hc

/-- Closing a step that keeps the full prefix, and a candidate's campaign record. -/
theorem ownRaftGhostR_close (γ : RaftNames) (dec : CCDec) (c0 : CCState) (id : w64)
    (r r' : RState) (HI' : RInv dec c0 r') (Hfp : r'.fp = r.fp)
    (Hcand : r'.p.role = .candidate →
      r.p.role = .candidate ∧ r'.p.term = r.p.term ∧ r'.p.log = r.p.log ∧
        r'.p.commit = r.p.commit) :
    ⊢ ownRaftGhost (GF := GF) γ id r'.p true -∗ logRecs γ base0 r.fp -∗
      (∀ (_ : r.p.role = .candidate), isCampK γ id r.p.term r.full r.p.commit) -∗
      ownRaftGhostR γ dec c0 id r' := by
  iintro Hg #Hfr #Hc
  unfold ownRaftGhostR
  iframe Hg
  isplitr; · ipureintro; exact HI'
  isplitr; · rw [Hfp]; iexact Hfr
  iintro %hc
  obtain ⟨hc0, ht, hl, hcm⟩ := Hcand hc
  ihave #Hk := Hc $$ %hc0
  unfold RState.full
  rw [Hfp, ht, hl, hcm]
  iexact Hk

end ghost

end EtcdGrove
end Perennial
