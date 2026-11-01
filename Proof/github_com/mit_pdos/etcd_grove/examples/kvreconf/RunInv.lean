/-
Lean-first (no Rocq counterpart).

# `run`'s loop invariant (2026-10-30, kvreconf's `run`)

At the top of the loop, for the delivered log `D` (`kvreconf-gap-design.md` §2.5):
- the node's driver at `D`, handling no `Ready`, and the loop's whole `nodeRunning` (so the stopped
  answers of `Advance` and `ApplyConfChange` are refuted, `nodeRunning_stopped`);
- `runDone`'s producer token;
- the replicated state at `D` (`repOwn`) and the node's view (`appNode`);
- the storage's hard state (`memStorMeta`);
- a known compaction point `c ≤ snapIndex` (`snapIndex`: the latest snapshot asked for or installed)
  with `D` frozen above it (`frozenTo`);
- the node's applied index (`nodeAppliedLb`, `Advance`'s, what `Compact` needs);
- the pending read states (`rsOk` of each).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.DefsCluster

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section inv
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KvrStor GF]

attribute [local instance] kvrStorageModel

/-- **`run`'s loop invariant** (see the file header), `pp` and `sp` its `pending` and `snapIndex`. -/
def runInv (γr : RNames) (id : w64) (r n st : Loc) (ρ : RepNames) (pp sp : Loc) : IProp GF :=
  iprop(∃ (D : List LogEntry) (hd hs : HardStateM) (csp mA : Loc) (m : Membership)
      (A : GMap (List w8) (List w8)) (snapIndex : w64) (c : Nat)
      (pv : GoSlice) (ps : List ReadState),
    "Hdrv" ∷ nodeDriver n γr.cluster kvrRaftN
      { storage := kvrStorIface st, delivered := D, hardState := hd, handling := none } ∗
    "Hrun" ∷ nodeRunning n γr.cluster kvrRaftN 1 ∗
    "Hprod" ∷ handoffProducer ρ.rd false ∗
    "Hown" ∷ repOwn γr r D (W64 D.length) csp m mA A ∗
    "Hview" ∷ appNode γr n D D.length m ∗
    "Hmeta" ∷ memStorMeta ρ.ms ρ.γs hs ∗
    "snapIndex" ∷ sp ↦ snapIndex ∗
    "#Hcp" ∷ memCompacted ρ.γs c ∗
    "#Hfz" ∷ frozenTo ρ.γs c D ∗
    "%Hsi" ∷ ⌜c ≤ uint.nat snapIndex ∧ c ≤ D.length⌝ ∗
    "#Hal" ∷ nodeAppliedLb γr.cluster id D.length ∗
    "pending" ∷ pp ↦ pv ∗
    "Hpv" ∷ pv ↦* ps ∗
    "Hpcap" ∷ ownSliceCap ReadState pv (DFrac.own 1) ∗
    "#Hps" ∷ [∗list] v ∈ ps, rsOk γr.cluster v)

/-- The invariant at the start (`runStart`, `pending` nil, `snapIndex` zero). -/
theorem runInv_init (γr : RNames) (vs : List w64) (id : w64) (r n st : Loc) (ρ : RepNames)
    (pp sp : Loc) :
    runStart (GF := GF) γr vs id r n st ρ ∗ pp ↦ slice.nil ∗ sp ↦ W64 0 ⊢
      runInv γr id r n st ρ pp sp := by
  iintro ⟨Hs, Hpp, Hsp⟩
  iunfold runStart at Hs
  icases Hs with ⟨%csp, %mA, %hs, Hdrv, Hrun, Hcfg, Hown, Hprod, Hmeta⟩
  ihave ⟨Hdrv, #Hdl⟩ := nodeDriver_deliveredLogLb _ _ _ _ $$ Hdrv
  unfold runInv
  iexists [], hsZero, hs, csp, mA, Membership.simple (GMap.listToSet vs), ∅, W64 0, 0,
    slice.nil, []
  unfold NodeDriverState.init
  iframe Hdrv Hrun Hprod Hown Hmeta Hsp Hpp
  isplitl [Hcfg]
  · unfold appNode
    iexists ⟨0, Membership.simple (GMap.listToSet vs)⟩
    iframe Hcfg Hdl
    isplitl []
    · iapply skippedIn_noConf γr.cluster [] 0 0 (fun _ _ _ h _ => absurd h (Nat.not_lt_zero _))
    ipureintro; exact ⟨rfl, Nat.le_refl _⟩
  isplitl []
  · iapply memCompacted_zero
  isplitl []
  · unfold frozenTo LogEntry.toEntries; simp only [List.mapIdx_nil, List.drop_nil]
    iapply memLog_nil
  isplitl []
  · ipureintro; exact ⟨Nat.zero_le _, Nat.le_refl _⟩
  isplitl []
  · iapply nodeAppliedLb_zero
  isplitl []
  · iapply ownSlice_nil
  isplitl []
  · iapply ownSliceCap_nil
  iapply BigSepL.bigSepL_nil.2
  itrivial

end inv

end kvreconf
end EtcdGrove
end Perennial
