/-
Lean-first (no Rocq counterpart). #33 parity B1: **what `node.start` needs of a fresh node**
(`node__start.lean`'s lemmas):
- the disk after the boot write (`startDur`; `fresh_dur`: a fresh view's disk is it;
  `startDur_boot`/`startDur_noboot`: the write `disk.save` makes in a bootstrapped run, or none);
- the boot log's indices and length (`memoryOf`'s premises);
- the `boot` report as the literal builds it (`evBootM`, no node name; `atNode_evBootM`: as `emit`
  records it, `evBoot`), its numbers, names and weight;
- `boot_hstep`: `report_upd`'s Sim step for the `boot` report, from `antSim_boot`;
- the boot write's hard state and entry, frozen (`bootHs_hsRO`, `bootEnt_entRO`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessReport
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Boot

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **A fresh node's disk once `start` wrote it**: term `1` and the boot entry in a bootstrapped run
(`HardState{Term: 1}`, `{1, 1, bootData()}`), nothing otherwise. -/
def startDur (R : AntSim.RunCfg) : AntSim.DurW :=
  ⟨W64 (if R.boot then 1 else 0), W64 0, W64 0, AntSim.bootLog R⟩

/-- A fresh view's disk is `startDur`. -/
theorem fresh_dur {R : AntSim.RunCfg} {v : AntSim.NodeView} (h : AntSim.FreshView R v) :
    v.dur = startDur R := by
  obtain ⟨⟨hterm, hvote, -, -, -, -, -, hlog, hcommit, -, -, -, -, -, -, hfp, -⟩, -, hdur, -⟩ := h
  rw [hdur]
  simp only [AntSim.durOf, RState.full, startDur, hterm, hvote, hcommit, hlog, hfp, List.nil_append]

/-- The boot write on the empty disk (a bootstrapped run). -/
theorem startDur_boot (R : AntSim.RunCfg) (hb : R.boot = true) :
    saveW ⟨W64 0, W64 0, W64 0, []⟩ (some (HardStateM.mk (W64 1) (W64 0) (W64 0))) [AntSim.bootEnt] =
      startDur R := by
  simp [saveW, startDur, AntSim.bootLog, hb]

/-- No boot write (a run not bootstrapped). -/
theorem startDur_noboot (R : AntSim.RunCfg) (hb : R.boot = false) :
    (⟨W64 0, W64 0, W64 0, []⟩ : AntSim.DurW) = startDur R := by
  simp [startDur, AntSim.bootLog, hb]

/-- The boot log's entries carry their positions from 1 (`memoryOf`'s premise). -/
theorem bootLog_index (R : AntSim.RunCfg) :
    ∀ (i : Nat) (e : EntryM), (AntSim.bootLog R)[i]? = some e → uint.nat e.Index' = 1 + i := by
  intro i e h
  unfold AntSim.bootLog at h
  split at h
  · cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h; rfl
    | succ i => simp at h
  · simp at h

theorem bootLog_length (R : AntSim.RunCfg) : (AntSim.bootLog R).length ≤ 1 := by
  unfold AntSim.bootLog; split <;> simp

/-- **The `boot` report as `start`'s literal builds it**: `evBoot` without the node's name (`emit`
sets it). -/
def evBootM (R : AntSim.RunCfg) : AntCheck.Event := { AntSim.evBoot R (W64 0) with node := [] }

theorem atNode_evBootM (R : AntSim.RunCfg) (id : w64) :
    atNode (AntSim.nameOf id) (evBootM R) = AntSim.evBoot R id := by
  unfold atNode evBootM AntSim.evBoot; rfl

theorem evBoot_nums (R : AntSim.RunCfg) (id : w64) : (AntSim.evBoot R id).NumsOk := by
  rcases Bool.eq_false_or_eq_true R.boot with h | h <;>
    simp [AntCheck.Event.NumsOk, AntSim.evBoot, AntCheck.optNumOk, AntCheck.numOk, AntCheck.numBound, h]

theorem evBoot_chg (R : AntSim.RunCfg) (id : w64) : (AntSim.evBoot R id).ChgOk 0 := by
  simp [AntCheck.Event.ChgOk, AntCheck.Event.entryLists, AntSim.evBoot]

theorem evBoot_weight (R : AntSim.RunCfg) (id : w64) : (AntSim.evBoot R id).weight = R.K + 2 := by
  simp [AntCheck.Event.weight, AntCheck.Event.size, AntSim.evBoot, AntSim.namesL]

/-- **`report_upd`'s Sim step for a fresh node's `boot`** (`antSim_boot`): the view running, nothing
sent, raft's facts unchanged. -/
theorem boot_hstep (R : AntSim.RunCfg) (dec : CCDec) (j : Fin R.N) (v : AntSim.NodeView)
    (hfv : AntSim.FreshView R v) (net₀ : List Msg) (xnet₀ : List XMsg) :
    ∀ (evs : List AntCheck.Event) (S : AntCheck.State) (V : Fin R.N → AntSim.NodeView)
      (net : List Msg) (xnet : List XMsg) (G0 G : AntSim.RaftFacts),
      AntSim.SimPre R dec S V net xnet evs G0 → (∀ i : Fin R.N, (V i).r.full ∈ G0.logs) →
      G = G0 → V j = v → net₀ <+: net → xnet₀ <+: xnet →
      AntSim.SimStep R dec evs G (AntSim.evBoot R (AntSim.nodeId j))
          (AntSim.setV V j { v with alive := true }) (net ++ []) (xnet ++ []) ∧
        AntSim.RaftLaws G ∧ ∀ i : Fin R.N, (AntSim.setV V j { v with alive := true } i).r.full ∈ G.logs := by
  intro evs S V net xnet G0 G hpre hlogs hG hV _ _
  subst hG; subst hV
  refine ⟨?_, hpre.2.2.1, ?_⟩
  · simp only [List.append_nil]
    exact AntSim.antSim_boot R dec S V net xnet evs _ j hpre hfv
  · intro i
    unfold AntSim.setV
    split
    · next h => subst h; exact hlogs _
    · exact hlogs i

end pure

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The boot write's hard state** (`&pb.HardState{Term: u64p(1)}`), frozen. -/
theorem bootHs_hsRO (p lt : Loc) (v : raftpb.HardState) (E : CoPset)
    (HT : v.Term' = lt) (HV : v.Vote' = null) (HC : v.Commit' = null)
    (Hu : v.unknownFields' = slice.nil) :
    (p ↦ v ∗ lt ↦ W64 1 : IProp GF) ⊢ |={E}=> hsRO p (HardStateM.mk (W64 1) (W64 0) (W64 0)) := by
  iintro ⟨Hp, Hlt⟩
  imod cellRO_alloc $$ Hlt with #cT
  ihave #cN : cellRO (GF := GF) null (W64 0) $$ []
  · unfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩
  imod hsRO_of_struct p v (HardStateM.mk (W64 1) (W64 0) (W64 0)) E Hu $$ [Hp] with #H
  · iframe Hp
    rw [HT, HV, HC]
    simp only
    iframe cT
    isplitl []
    · iexact cN
    iexact cN
  imodintro; iexact H

/-- **The boot write's entry** (`{Term: u64p(1), Index: u64p(1), Data: bootData()}`), frozen. -/
theorem bootEnt_entRO (p lt li : Loc) (sl : GoSlice) (v : raftpb.Entry) (E : CoPset)
    (HT : v.Term' = lt) (HI : v.Index' = li) (HY : v.Type' = null) (HD : v.Data' = sl)
    (Hu : v.unknownFields' = slice.nil) :
    (p ↦ v ∗ lt ↦ W64 1 ∗ li ↦ W64 1 ∗ sl ↦* AntSim.bootData : IProp GF) ⊢
      |={E}=> entRO p AntSim.bootEnt := by
  iintro ⟨Hp, Hlt, Hli, Hsl⟩
  imod cellRO_alloc $$ Hlt with #cT
  imod cellRO_alloc $$ Hli with #cI
  imod ownSlice_persist $$ Hsl with #Hd
  ihave #cY : cellRO (GF := GF) null (W32 0 : raftpb.EntryType) $$ []
  · unfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩
  imod entOwn_of_struct p v AntSim.bootEnt E Hu $$ [Hp] with Ho
  · iframe Hp
    rw [HT, HI, HY, HD]
    simp only [AntSim.bootEnt]
    iframe cT cI Hd
    iexact cY
  imod entOwn_freeze $$ Ho with #Ho
  imodintro; iexact Ho

end lemmas

section opt
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-- A read-only hard state as an optional one. -/
theorem hsOptRO_of_hsRO (hp : Loc) (h : HardStateM) :
    hsRO (GF := GF) hp h ⊢ hsOptRO hp (some h) := by
  iintro #H
  ihave #H' := H
  iunfold hsRO at H'
  icases H' with ⟨%pt, %pv, %pc, %uf, %Hnn, -⟩
  iunfold hsOptRO
  iright
  iexists h
  iframe H
  ipureintro; exact ⟨Hnn, rfl⟩

/-- An optional hard state that is set is read-only. -/
theorem hsOptRO_some (hp : Loc) (h : HardStateM) :
    hsOptRO (GF := GF) hp (some h) ⊢ hsRO hp h := by
  iunfold hsOptRO
  iintro (⟨%H⟩ | ⟨%h', ⟨%_, %He⟩, #H⟩)
  · exact absurd H.2 (by simp)
  · cases He; iexact H

/-- Fewer receipts. -/
theorem receipt_le (m k : Nat) (h : m ≤ k) : ⧗ k ⊢ (⧗ m : IProp GF) := by
  iintro H
  rw [show k = m + (k - m) by omega]
  icases (receipt_add (GF := GF) m (k - m)).1 $$ H with ⟨H1, -⟩
  iexact H1

/-- One more receipt. -/
theorem receipt_succ (k : Nat) : (⧗ k ∗ ⧗ 1 : IProp GF) ⊢ ⧗ (k + 1) :=
  (receipt_add (GF := GF) k 1).2

end opt

section names
variable [GooseExts]

/-- The initial voters' names (`idNames` of `storeConf`'s voters). -/
theorem voters_names (K : Nat) :
    ((List.range K).map fun (i : Nat) => W64 ((i : Int) + 1)).map AntSim.nameOf = AntSim.namesL K := by
  unfold AntSim.namesL; rw [List.map_map]; rfl

end names

end AntHarness
end EtcdGrove
end Perennial
