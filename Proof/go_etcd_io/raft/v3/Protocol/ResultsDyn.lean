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

end ghost

end EtcdGrove
end Perennial
