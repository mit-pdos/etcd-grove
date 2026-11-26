/-
Lean-first (no Rocq counterpart). #33 parity B1: **what `node.start` needs of a fresh node**
(`node__start.lean`'s lemmas):
- the disk after the boot write (`startDur`; `fresh_dur`: a fresh view's disk is it;
  `startDur_boot`/`startDur_noboot`: the write `disk.save` makes in a bootstrapped run, or none);
- the boot log's indices and length (`memoryOf`'s premises);
- the `boot` report as the literal builds it (`evBootM`, no node name; `atNode_evBootM`: as `emit`
  records it, `evBoot`), its numbers, names and weight;
- `boot_hstep`: `report_upd`'s Sim step for the `boot` report, from `antSim_boot`;
- the boot write's hard state and entry, frozen (`bootHs_hsRO`, `bootEnt_entRO`);
- `NewRawNode`'s restart premises at the driver's `raft.Config` (`startConfig`; `startConfig_valid`,
  `start_storageHolds`, `start_confStateIs`, `start_restartScope`) and the state it restarts at
  (`restartR_fresh`: a fresh view's);
- the close into `nodeOwn`'s `.loop` phase with raft's node at the run's mask (`nodeLoopAt`,
  `startLoop.law`; at `md = {}` it is `nodeOwn`'s own text, `nodeLoopAt_empty`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessReport
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Boot
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.AntStorageStart
public import Proof.go_etcd_io.raft.v3.RawNodeStartApi

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

section slice_ex
-- A copy of mvccrand/newHistory.lean's (and raft LemmasEnts') `wp_slice_literal_ex`: a slice literal
-- whose elements are allocated (`[]*pb.Entry{{...}}`). TODO(Perennial): one shared copy.
open Iris.ProgramLogic Iris.Std
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [preSem : go.PreSemantics]
variable {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]

set_option goose.wp.unfoldSliceLiterals true in
/-- `wp_slice_literal` with the elements chosen in the array literal's post (`∃ l`), so that they may
be values the elements' own WPs return (here the two maps `make1` allocates); a local copy of
Perennial's `wp_slice_literal_nonnull` proof (`notes/perennial-changes.md`, "A slice literal of map
literals"). -/
theorem ant_wp_slice_literal_ex {st t : go.GoType} [IntoValTyped (GF := GF) V t]
    [st ↓u go.SliceType t] (kvs : List keyed_element) (Φ : val → IProp GF) :
    WP (App (Val (GoInstruction (CompositeLiteral (go.ArrayType (go.arrayLiteralSize kvs) t))))
          (Val (LiteralValueV kvs)))
      {{ v, ∃ l : List V, ⌜v = #(array.mk (go.arrayLiteralSize kvs) l)⌝ ∗
        (∀ sl_ptr : Loc,
          (slice.mk sl_ptr (W64 (go.arrayLiteralSize kvs)) (W64 (go.arrayLiteralSize kvs)) ↦* l ∗
            ownSliceCap V (slice.mk sl_ptr (W64 (go.arrayLiteralSize kvs))
              (W64 (go.arrayLiteralSize kvs))) (DFrac.own 1)) -∗
          Φ #(slice.mk sl_ptr (W64 (go.arrayLiteralSize kvs)) (W64 (go.arrayLiteralSize kvs)))) }} ⊢
    WP (App (Val (GoInstruction (CompositeLiteral st))) (Val (LiteralValueV kvs))) {{ Φ }} := by
  iintro HΦ
  wp_pures
  by_cases hlen : go.arrayLiteralSize kvs < 2 ^ 63
  · rw [ite_eq_left hlen]
    wp_pures
    wp_alloc_auto
    wp_pure
    wp_pure
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.ArrayType _ t)))) (Val (LiteralValueV kvs)))
    wp_apply_core wp_wand $$ HΦ
    iintro %v ⟨%l, %Hv, HΦ⟩
    subst Hv
    wp_auto
    have h0 : 0 ≤ go.arrayLiteralSize kvs := by
      unfold go.arrayLiteralSize; split; omega
    rw [ite_eq_left ⟨by decide, by word, by word⟩]
    have hz : W64 (go.arrayLiteralSize kvs) - W64 0 = W64 (go.arrayLiteralSize kvs) := by word
    simp only [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, hz]
    wp_pures
    ihave %Hlen := array_len _ _ _ _ $$ tmp
    iapply HΦ $$ %tmp_ptr
    isplitl [tmp]
    · iapply slice_array tmp_ptr _ (array.mk (go.arrayLiteralSize kvs) l) (by simp only; omega)
      iexact tmp
    · iapply ownSliceCap_empty _ rfl (by simp only; word)
  · rw [ite_eq_right hlen]; iapply wp_AngelicExit

end slice_ex

section restart
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]

/-- `node.start`'s `raft.Config` (the literal): node `id`, the mode's flags, the `bootStorage` `s`,
the logger `&nodeLogger{n}` at `l`. -/
abbrev startConfig (m : H.Mode) (id : w64) (s l : Loc) : Config :=
  { ID' := id, ElectionTick' := W64 10, HeartbeatTick' := W64 1,
    Storage' := interface.mkOk
      (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.bootStorage.ty) #s,
    Applied' := 0, AsyncStorageWrites' := m.Async', MaxSizePerMsg' := m.MaxSizePerMsg',
    MaxCommittedSizePerReady' := W64 1048576, MaxUncommittedEntriesSize' := 0,
    MaxInflightMsgs' := m.MaxInflightMsgs', MaxInflightBytes' := 0, CheckQuorum' := m.CheckQuorum',
    PreVote' := m.PreVote', ReadOnlyOption' := 0,
    Logger' := interface.mkOk
      (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.nodeLogger.ty) #l,
    DisableProposalForwarding' := false, DisableConfChangeValidation' := false,
    StepDownOnRemoval' := m.StepDownOnRemoval', TraceLogger' := interface.nil }

/-- A mode within its scope draws `MaxInflightMsgs` among `1, 2, 256`. -/
theorem inScope_inflight {s : H.Scope} {m : H.Mode} (h : InScope s m) :
    m.MaxInflightMsgs' = W64 1 ∨ m.MaxInflightMsgs' = W64 2 ∨ m.MaxInflightMsgs' = W64 256 := by
  obtain ⟨-, -, -, -, -, hl, -⟩ := h
  split at hl
  · exact hl.1
  · exact Or.inr (Or.inr hl.1)

theorem startConfig_valid (m : H.Mode) {N : Nat} (j : Fin N) (hN : N ≤ 9) (s l : Loc)
    (hmi : m.MaxInflightMsgs' = W64 1 ∨ m.MaxInflightMsgs' = W64 2 ∨ m.MaxInflightMsgs' = W64 256) :
    ConfigValid (startConfig m (AntSim.nodeId j) s l) := by
  have hj := j.isLt
  unfold ConfigValid AntSim.nodeId
  refine ⟨?_, ?_, ?_, ⟨by show (0 : Int) < sint.Z (W64 1); decide,
    by show sint.Z (W64 1) < sint.Z (W64 10); decide⟩, by simp, ?_, Or.inl rfl, by simp, Or.inl rfl⟩
  · intro h; have := congrArg (fun w : w64 => uint.Z w) h; simp only at this; word
  · intro h; have := congrArg (fun w : w64 => uint.Z w) h; simp only at this; word
  · intro h; have := congrArg (fun w : w64 => uint.Z w) h; simp only at this; word
  · show (0 : Int) < sint.Z m.MaxInflightMsgs'
    rcases hmi with h | h | h <;> rw [h] <;> decide

theorem inflight_lt {m : H.Mode}
    (hmi : m.MaxInflightMsgs' = W64 1 ∨ m.MaxInflightMsgs' = W64 2 ∨ m.MaxInflightMsgs' = W64 256) :
    sint.Z m.MaxInflightMsgs' < 2 ^ 62 := by
  rcases hmi with h | h | h <;> rw [h] <;> decide

/-- The restarted storage holds the boot write's state (`downDur`). -/
theorem start_storageHolds (R : AntSim.RunCfg) (w : AntSim.DurW) (hw : w = startDur R) :
    StorageHolds (downDur R) (bootContents (HardStateM.mk w.term w.vote w.commit) w.log) := by
  subst hw
  unfold StorageHolds downDur startDur bootContents
  rcases Bool.eq_false_or_eq_true R.boot with hb | hb <;>
    simp [hb, AntSim.bootLog, StorContents.b, StorContents.commit, RaftState.init, RaftState.entsFrom,
      base0, plogTermAt]

theorem start_last (R : AntSim.RunCfg) (h : HardStateM) (w : AntSim.DurW) (hw : w = startDur R) :
    (bootContents h w.log).last = (AntSim.bootLog R).length := by
  subst hw
  simp [StorContents.last, StorContents.b, bootContents, startDur, base0]

theorem votersL_nodup (K : Nat) (hK : K ≤ 9) :
    ((List.range K).map fun (i : Nat) => W64 ((i : Int) + 1)).Nodup := by
  unfold List.Nodup; rw [List.pairwise_map]
  refine List.Pairwise.imp_of_mem (fun {a b} ha hb hne hab => hne ?_) List.nodup_range
  simp only [List.mem_range] at ha hb
  have : uint.Z (W64 ((a : Int) + 1)) = uint.Z (W64 ((b : Int) + 1)) := by rw [hab]
  rw [uint_Z_W64 _ (by omega) (by omega), uint_Z_W64 _ (by omega) (by omega)] at this
  omega

/-- The boot storage's conf state reports the initial voters' simple membership. -/
theorem start_confStateIs (R : AntSim.RunCfg) :
    confStateIs (bootConfState ((List.range R.K).map fun (i : Nat) => W64 ((i : Int) + 1)) memSnapEmpty)
      (Membership.simple R.voters0) := by
  have hE : ([] : List w64) ≡ₚ GMap.elements (∅ : GSet w64) := by
    refine (List.perm_ext_iff_of_nodup List.nodup_nil (GMap.NoDup_elements _)).2 ?_
    intro k
    rw [GMap.elem_of_elements]
    simp only [List.not_mem_nil, false_iff]
    exact GMap.not_elem_of_empty k
  refine ⟨ApiImpl.perm_elements_listToSet' _ (votersL_nodup R.K (by have := R.hK; omega)), hE, hE, hE, rfl⟩

/-- The restart's scope premises at the run's mask. -/
theorem start_restartScope (γ : AntNames) (j : Fin γ.R.N) (s l : Loc) (σ : StorContents)
    (hsc : InScope γ.scope γ.mode) (hrun : ModeRun γ.scope γ.mode γ.R)
    (hrc : γ.raft.raftNames.reCfg = γ.R.voters0) (hb : σ.base = base0) :
    RestartScopeOk γ.raft (startConfig γ.mode (AntSim.nodeId j) s l) σ (Membership.simple γ.R.voters0)
      γ.R.md := by
  rw [hrun.2.2.2.2.1]
  obtain ⟨-, hV, -, hpv, hcq, -⟩ := hsc
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun _ => ⟨hrc.symm, rfl, rfl⟩, fun _ => hb⟩
  · show γ.mode.PreVote' = false
    cases hx : γ.mode.PreVote'
    · rfl
    · have := hpv hx; simp only [scopeMd] at h; rw [h] at this; cases this
  · show γ.mode.CheckQuorum' = false
    cases hx : γ.mode.CheckQuorum'
    · rfl
    · have := hcq hx; simp only [scopeMd] at h; rw [h] at this; cases this
  · simp only [scopeMd] at h
    have hVN : γ.mode.Voters' = γ.mode.Nodes' := by
      rcases hV with hV | ⟨hnv, -⟩
      · exact hV
      · rw [h] at hnv; cases hnv
    have hK : γ.R.K = γ.R.N := by rw [hrun.1, hrun.2.1, hVN]
    show AntSim.nodeId j ∈ γ.raft.raftNames.reCfg
    rw [hrc]
    unfold AntSim.RunCfg.voters0 AntSim.nodeId
    rw [GMap.elem_of_list_to_set, List.mem_map]
    exact ⟨j.val, List.mem_range.2 (by have := j.isLt; omega), rfl⟩

/-- **The state `NewRawNode` restarts a fresh node at is the view's** (`PInitR`; the read state
fresh). -/
theorem restartR_fresh (R : AntSim.RunCfg) (v : AntSim.NodeView) (hf : AntSim.FreshView R v)
    (hrd : v.r.p.rd = {}) (ap : Nat) (hap : ap = 0) :
    restartR (downDur R) (bootContents (HardStateM.mk v.dur.term v.dur.vote v.dur.commit) v.dur.log)
      ap 0 (ApiImpl.stOf (Membership.simple R.voters0)) [] = v.r := by
  subst hap
  rw [fresh_dur hf]
  obtain ⟨hP, -⟩ := hf
  generalize v.r = r at hP hrd ⊢
  obtain ⟨p, applied, pci, snap, cidx, cfg, fp⟩ := r
  obtain ⟨term, vote, lead, role, votes, outbox, base, log, commit, matched, rd⟩ := p
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, -⟩ := hP
  simp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 hrd
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 hrd
  have hc : ApiImpl.stOf (Membership.simple R.voters0) = R.c0 := by
    show cfgStateC (CfgM.simple R.voters0 ∅) = _
    rw [cfgStateC_simple]; rfl
  rw [hc]
  rcases Bool.eq_false_or_eq_true R.boot with hb | hb <;>
    simp [hb, restartR, restartP, initPState, downDur, startDur, bootContents, AntSim.bootLog,
      RaftState.init, RaftState.entsFrom, base0, AntSim.RunCfg.c0]

end restart

section loop
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-- **`nodeOwn`'s `.loop` phase with raft's node at the mode `md`**: `nodeOwn c γ j n v
(.loop net₀ xnet₀ r₁ xs₁)`'s text (`HarnessRun.lean`) with `rawNode γ.raft.raftNames {}` replaced by
`rawNode γ.raft.raftNames md`. (Raft's step D moves `nodeOwn`'s node to `γ.R.md`; this copy goes
then.) -/
def nodeLoopAt (md : RnMode) (c : Loc) (γ : AntNames) (j : Fin γ.R.N) (n : Loc)
    (v : AntSim.NodeView) (net₀ : List Msg) (xnet₀ : List XMsg) (r₁ : RState) (xs₁ : List XMsg) :
    IProp GF :=
  iprop(∃ (d rn ms hsl cl csl : Loc) (role : GoString) (applied : w64),
    n.[H.node, go!"disk"] ↦□ d ∗ nodeMemB1 n ∗
    n.[H.node, go!"rn"] ↦ rn ∗ n.[H.node, go!"store"] ↦ ms ∗ n.[H.node, go!"role"] ↦ role ∗
    n.[H.node, go!"hs"] ↦ hsl ∗ n.[H.node, go!"cause"] ↦ cl ∗ n.[H.node, go!"applied"] ↦ applied ∗
    n.[H.node, go!"conf"] ↦ csl ∗
    viewFrag γ j v ∗ nodeLive γ j ∗ ⌜ViewNormal v⌝ ∗
    iprop(diskOwn d v.dur ∗ ∃ (si : Loc) (rs : RNState) (qs : List Msg) (ip : Nat) (r : RState),
      nodeStor si ms ((List.range γ.R.K).map fun (i : Nat) => W64 ((i : Int) + 1))
        (HardStateM.mk v.dur.term v.dur.vote v.dur.commit) ∗
      ⌜rs.storage = interface.ok ⟨go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.bootStorage.ty, #si⟩⌝ ∗
      rawNode γ.raft.raftNames md rn (AntSim.nodeId j) rs r qs ip ∗ nodeRaft γ j rs ∗
      ⌜RsView rs v ∧ v.alive = true ∧ role = AntSim.roleS v ∧ uint.nat applied = v.delivered.length ∧
        rs.k = γ.R.k j⌝ ∗
      hsRO hsl (HardStateM.mk v.dur.term v.dur.vote v.dur.commit) ∗
      csPts csl DFrac.discard
        (ConfStateM.mk ((List.range γ.R.K).map fun (i : Nat) => W64 ((i : Int) + 1)) [] [] [] false) false ∗
      ⌜v.conf = γ.R.c0⌝ ∗
      iprop(⌜r = r₁ ∧
          AntSim.Reach γ.R γ.dec (AdmFold γ.dec γ.R.c0) net₀ xnet₀ j v r₁ ∧ qs = [] ∧
          ip = lcpLen v.r.p.log r₁.p.log ∧ ByOk v.byE⌝ ∗ sentLb γ net₀ ∗ xsentLb γ xnet₀ ∗
          causeOwn γ j v cl)))

/-- At `md = {}`, `nodeLoopAt` is `nodeOwn`'s `.loop` phase (the copy is faithful). -/
theorem nodeLoopAt_empty (c : Loc) (γ : AntNames) (j : Fin γ.R.N) (n : Loc) (v : AntSim.NodeView)
    (net₀ : List Msg) (xnet₀ : List XMsg) (r₁ : RState) (xs₁ : List XMsg) :
    nodeLoopAt (GF := GF) {} c γ j n v net₀ xnet₀ r₁ xs₁ ⊣⊢ nodeOwn c γ j n v (.loop net₀ xnet₀ r₁ xs₁) := by
  unfold nodeLoopAt nodeOwn
  exact .rfl

/-- **`node.start`'s close into `nodeOwn`** (what its `drain "boot"` takes), from raft's node at the
run's mask (`NewRawNode.restartAtApiSpec` at `γ.R.md`). Holds by `nodeLoopAt_empty` once `nodeOwn`'s
node is at `γ.R.md` (raft's step D); until then a hypothesis of `node.start.wp_proof`. -/
abbrev startLoop.law : Prop :=
  ∀ (c : Loc) (γ : AntNames) (j : Fin γ.R.N) (n : Loc) (v : AntSim.NodeView) (net₀ : List Msg)
    (xnet₀ : List XMsg) (r₁ : RState) (xs₁ : List XMsg),
    nodeLoopAt (GF := GF) γ.R.md c γ j n v net₀ xnet₀ r₁ xs₁ ⊢ nodeOwn c γ j n v (.loop net₀ xnet₀ r₁ xs₁)

end loop

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
