/-
The protocol-level results of the dynamic model (2026-10-14, reconfiguration stage B5): safety
of raft with configurations changing by applied conf entries (`StepR` at `AdmFold dec c0`),
proved with the ghost argument (`notes/reconfiguration-safety.md`), at the model level.

**A model theorem, not yet reached from Go**: the code produces `Step` witnesses at a static
configuration (`raft__Step.lean`); stage B7 connects it to `StepR` and to this ghost state.

* `raft_dyn_alloc`: the dynamic ghost state allocated for nodes starting from `c0` with an empty
  log (`ownRaftGhostR` of `rinit c0`).
* `ownRaftGhostR_stepR` (`RefinementDyn.lean`): every `StepR` step keeps it, given the messages
  it consumed (each `isMessage`, what every sent message carries) and the records of the
  snapshot prefixes it may restore.
* `raft_dyn_committed_agree` (**log agreement / state machine safety**): the committed prefixes
  of any two nodes are prefixes of one another -- each is a prefix of the one global committed
  log (`isCommitted`).
* `raft_dyn_election_safety`: two leaders of a term are one node.
* `raft_dyn_read_states`, `raft_dyn_read_index` (2026-10-14, stage B6, **the read-index
  guarantee**): every `ReadState` a node holds (hands out at `StepR.takeReads`) is
  `readStateOk`, so the committed prefix of any node whose commit index reaches its index
  extends the committed log the request was created knowing.

Assumptions (model restrictions, `notes/STATUS.md`, "Reconfiguration, stage B5"): A1
(`ApplyConfChange` for every committed conf entry, in order, once, before the `Advance` that
acknowledges it: `StepR.advance`/`applyConf`); A3 (a snapshot's configuration is its prefix's
fold, `AdmFold`, and the restored prefix is the committed one: its records, `S`); fresh nodes
from one `c0` with `CfgOk c0` and an empty log, no crash-restart (so atomic persistence is moot);
no panic (`cfgFold` defined on the applied prefixes: `RInv`); `AppCommitEq` (an `MsgApp` carries the sender's
commit index, as Go's `sendAppend` does). (Until 2026-10-14 also: the single-voter read-index
shortcut not modelled; it is now `StepR.readSingle`/`readReleaseSingle`, the fixed raft's,
`issues/raft-readindex-singleton-stale.md`.)
-/
module

public import Proof.go_etcd_io.raft.v3.Protocol.RefinementDyn
public import Proof.go_etcd_io.raft.v3.Protocol.Facts

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI GMap go_etcd_io.raft.v3

section ghost
variable [FfiSyntax]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]

/-- A fresh node of the dynamic model: the initial protocol state, configuration `c0`, nothing
applied. -/
def rinit (c0 : CCState) : RState :=
  { p := initPState, applied := W64 0, pci := W64 0, snap := false, cidx := 0, cfg := c0, fp := [] }

theorem RInv_rinit (dec : CCDec) (c0 : CCState) : RInv dec c0 (rinit c0) :=
  RInv_init dec c0 (rinit c0) [] rfl rfl rfl (by simp) rfl rfl rfl rfl rfl (by rfl)

/-- The dynamic ghost state of the nodes `ids`, allocated (with the commit invariant). -/
theorem raft_dyn_alloc (E : CoPset) (dec : CCDec) (c0 : CCState) (h0 : CfgOk c0)
    (ids : GSet w64)
    -- (2026-10-15, stage N) the conf-change bytes the cluster admits
    (ccOk : w32 → List w8 → Prop) (C : RaftNames → IProp GF) :
    W64 0 ∉ ids →
    ⊢ allocClient E c0.cfg.incoming (some (DynCfg.all (DynCfg.ofFold dec c0 h0))) C -∗
      |={E}=> ∃ γ : RaftNames,
        ⌜γ.dyn = some (DynCfg.ofFold dec c0 h0) ∧ γ.reCCOk = ccOk ∧ γ.reCfg = c0.cfg.incoming⌝ ∗
        raftCommitInv (GF := GF) γ ∗ C γ ∗
        ([∗map] id ↦ _u ∈ toMap ids, ownRaftGhostR γ dec c0 id (rinit c0)) ∗
        -- (2026-10-15, stage N) as `ownRaftGhost_alloc`: the empty committed log, every read
        -- credit
        isCommitted γ [] ∗ rdCred γ (2 ^ 64 - 2) ∗ rdCredInv γ := by
  intro Hnz
  iintro Hcl
  imod ownRaftGhost_alloc_gen (GF := GF) E c0.cfg.incoming ids
    (some (DynCfg.all (DynCfg.ofFold dec c0 h0))) ccOk C h0.2.1 Hnz $$ Hcl
    with ⟨%γ, %Hγ, #Hinv, #Hc0, Hn, HC, Hcr, #Hcri⟩
  simp only [Option.isSome_some]
  imodintro
  iexists γ
  isplitr
  · ipureintro
    refine ⟨?_, Hγ.2.2, Hγ.1⟩
    unfold RaftNames.dyn; rw [Hγ.2.1]; simp [DynCfg.all_self]
  iframe Hinv HC Hc0 Hcr Hcri
  iapply BigSepM.bigSepM_impl $$ Hn
  imodintro
  iintro %id %u %_ Hg
  unfold ownRaftGhostR
  rw [show (rinit c0).p = initPState from rfl]
  iframe Hg
  isplitr; · ipureintro; exact RInv_rinit dec c0
  isplitr
  · unfold logRecs rinit
    iapply (BigSepL.bigSepL_nil).2; iempintro
  iintro %h
  exfalso; exact absurd h (by simp [initPState])

/-- **Log agreement** (state machine safety) of the dynamic model: the committed prefixes of
any two nodes are prefixes of one another. -/
theorem raft_dyn_committed_agree (γ : RaftNames) (dec : CCDec) (c0 : CCState)
    (id1 id2 : w64) (r1 r2 : RState) :
    ⊢ ownRaftGhostR (GF := GF) γ dec c0 id1 r1 -∗ ownRaftGhostR γ dec c0 id2 r2 -∗
      ⌜r1.full.take (uint.nat r1.p.commit) <+: r2.full.take (uint.nat r2.p.commit) ∨
        r2.full.take (uint.nat r2.p.commit) <+: r1.full.take (uint.nat r1.p.commit)⌝ := by
  iintro H1 H2
  unfold ownRaftGhostR
  icases H1 with ⟨Hg1, %HI1, #Hfr1, -⟩
  icases H2 with ⟨Hg2, %HI2, #Hfr2, -⟩
  iunfold ownRaftGhost at Hg1 Hg2
  icases Hg1 with ⟨%γv1, %voted1, %kl1, Hg1⟩
  icases Hg2 with ⟨%γv2, %voted2, %kl2, Hg2⟩
  iNamed Hg1
  icases ownLogGhost_cmt γ id1 r1.p kl1 $$ Hlg with ⟨%fp1, %Hf1, #Hfrc1, #Hc1⟩
  iNamed Hg2
  icases ownLogGhost_cmt γ id2 r2.p kl2 $$ Hlg with ⟨%fp2, %Hf2, #Hfrc2, #Hc2⟩
  icases FullOk_unique γ r1.p.base fp1 r1.fp Hf1 HI1.full $$ Hfrc1 Hfr1 with %He1
  icases FullOk_unique γ r2.p.base fp2 r2.fp Hf2 HI2.full $$ Hfrc2 Hfr2 with %He2
  subst He1 He2
  icases isCommitted_agree γ _ _ $$ Hc1 Hc2 with %H
  ipureintro
  unfold cprefix at H
  rw [toNat_uZ, toNat_uZ] at H
  exact H

/-- Election safety of the dynamic model: two leaders of a term are one node (the winners
table). -/
theorem raft_dyn_election_safety (γ : RaftNames) (dec : CCDec) (c0 : CCState)
    (id1 id2 : w64) (r1 r2 : RState) :
    r1.p.role = .leader → r2.p.role = .leader → r1.p.term = r2.p.term →
    ⊢ ownRaftGhostR (GF := GF) γ dec c0 id1 r1 -∗ ownRaftGhostR γ dec c0 id2 r2 -∗
      ⌜id1 = id2⌝ := by
  intro Hl1 Hl2 Ht
  iintro H1 H2
  unfold ownRaftGhostR
  icases H1 with ⟨Hg1, -⟩
  icases H2 with ⟨Hg2, -⟩
  ihave #Hle1 : isLeader γ id1 r2.p.term $$ [Hg1]
  · rw [← Ht]; iapply ownRaftGhost_isLeader γ id1 r1.p Hl1 $$ Hg1
  ihave #Hle2 := ownRaftGhost_isLeader γ id2 r2.p Hl2 $$ Hg2
  iapply isLeader_unique γ id1 id2 r2.p.term $$ Hle1 Hle2

/-- The `ReadState`s of a node of the dynamic model (the ones `StepR.takeReads`, i.e.
`acceptReady`, hands out with the `Ready`), each `readStateOk`: persistent facts copied out of
the ghost state's `rdOwn` (as `ownRaftGhost_readStates` in the static mode). -/
theorem raft_dyn_read_states (γ : RaftNames) (dec : CCDec) (c0 : CCState) (id : w64)
    (r : RState) :
    ⊢ ownRaftGhostR (GF := GF) γ dec c0 id r -∗ [∗list] st ∈ r.p.rd.states, readStateOk γ st := by
  iintro H
  unfold ownRaftGhostR
  icases H with ⟨Hg, -⟩
  iunfold ownRaftGhost at Hg
  icases Hg with ⟨%γv, %voted, %kl, Hg⟩
  iNamed Hg
  iunfold rdOwn at Hrd
  icases Hrd with ⟨%γl, %rqm, -, -, -, -, -, #Hst0, -⟩
  iexact Hst0

/-- **The read-index guarantee** of the dynamic model: a `ReadState{Index: i, RequestCtx}` that
a node `id1` holds (and hands out), whose context a client registered when it created the
read knowing the committed log `Lc` (`readReq γ st.RequestCtx' Lc`; D6: the context is its
bytes, until then a slice the client registered with bytes `c`),
promises that the committed prefix of any node `id2` whose commit index is at least `i` extends
`Lc`: applying up to `i` reads a state at least as new as the request. (`readOk_prefix` uses
only the agreement of committed logs, `isCommitted_agree`, which the dynamic mode keeps.) -/
theorem raft_dyn_read_index (γ : RaftNames) (dec : CCDec) (c0 : CCState) (id1 id2 : w64)
    (r1 r2 : RState) (st : ReadStateM) (Lc : List EntryM) :
    st ∈ r1.p.rd.states → uint.Z st.Index' ≤ uint.Z r2.p.commit →
    ⊢ ownRaftGhostR (GF := GF) γ dec c0 id1 r1 -∗ ownRaftGhostR γ dec c0 id2 r2 -∗
      readReq γ st.RequestCtx' Lc -∗
      ⌜Lc <+: r2.full.take (uint.nat r2.p.commit)⌝ := by
  intro Hin Hle
  iintro H1 H2 #Hrq
  ihave #Hsts := raft_dyn_read_states γ dec c0 id1 r1 $$ H1
  ihave #Hst := (BigSepL.bigSepL_mem (Φ := fun st => readStateOk (GF := GF) γ st) Hin) $$ Hsts
  iunfold readStateOk at Hst
  icases Hst with ⟨%c, %Hpd', #Hok⟩
  subst Hpd'
  unfold ownRaftGhostR
  icases H2 with ⟨Hg2, %HI2, #Hfr2, -⟩
  iunfold ownRaftGhost at Hg2
  icases Hg2 with ⟨%γv2, %voted2, %kl2, Hg2⟩
  iNamed Hg2
  icases ownLogGhost_cmt γ id2 r2.p kl2 $$ Hlg with ⟨%fp2, %Hf2, #Hfrc2, #Hc2⟩
  icases FullOk_unique γ r2.p.base fp2 r2.fp Hf2 HI2.full $$ Hfrc2 Hfr2 with %He2
  subst He2
  have Hfl := HI2.full_length
  have Hcl := HI2.commit_last
  unfold RState.full at Hfl
  clear HI2
  have Hlen : uint.Z st.Index' ≤ ((cprefix r2.fp r2.p).length : Int) := by
    unfold cprefix
    rw [List.length_take]
    word
  icases readOk_prefix γ st.RequestCtx' st.Index' Lc (cprefix r2.fp r2.p) Hlen $$ Hok Hrq Hc2 with %H
  ipureintro
  unfold cprefix at H
  rw [toNat_uZ] at H
  exact H

end ghost

end EtcdGrove
end Perennial
