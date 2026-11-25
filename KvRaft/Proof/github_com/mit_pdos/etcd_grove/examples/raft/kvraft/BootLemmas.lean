/-
# kvraft's boot: the file a crash left, and the durable state the next generation starts from (2026-11-22)

`notes/kvraft-part.md`, "The crash law kvraft needs" and "`persist`".

A crash during a write's window may leave either file (`durable`'s crash lemma `durInv_crash`: the next
generation finds `v`, with `v = s.cur ∨ s.alt = some v`). The generation's file invariant
(`kdFileInvK`, allocated at the generation's boot, `kd_file_alloc`), whose contents the crash
obligation takes, says what each holds (`kdFileState`). `kd_boot_choose`
turns it into the next generation's start (raft's vacancy, the durable state `S'`, and the found
contents holding it):

* the window held a batch to `S2` and the new contents survived: the batch is entered at the boot
  (raft's `readyCrashEnter`, with the arm the node was started from, `nodeArm`, and the share of
  `nodeRunning` that waited with the batch);
* otherwise: raft's `nodeCrash` (the batch, if any, dropped), at the durable state `S`.

-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.DefsLaws

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

attribute [local instance] kdStorageModel

/-- **The boot's choice** (see the file header): from the crashed generation's file state at `(S, s,
pb)` and the contents `v` the crash left, the next generation's durable state `S'`, raft's vacancy,
and `v` holding `S'`. -/
theorem kd_boot_choose (γ : KdNames) (id : w64)
    (S : RaftState) (s : DurFs.DurSt) (pb : Option (GName × RaftState × Qp × GName)) (x : CrashNames)
    (v : Option GoString) (E : CoPset) (hE : ↑kdRaftN ⊆ E) (hv : v = s.cur ∨ s.alt = some v) :
    ⊢ isCluster (GF := GF) γ.r.cluster kdRaftN -∗ crashed -∗ nodeCrashTok γ.r.cluster id x -∗
      raftState γ.r.cluster id S -∗ kdFileState γ id x S s pb ={E}=∗
      ∃ S' : RaftState, raftState γ.r.cluster id S' ∗ nodeVacant γ.r.cluster id ∗ fileHolds γ S' v := by
  iintro #HisC #Hcr Htok HrS Hfs
  obtain ⟨cur, alt⟩ := s
  cases alt with
  | none =>
    -- outside a window: the file is `cur`, which holds `S`
    simp only [kdFileState]
    icases Hfs with ⟨Hfh, -⟩
    have hv' : v = cur := by
      rcases hv with h | h
      · exact h
      · cases h
    subst hv'
    imod nodeCrash γ.r.cluster kdRaftN id x E hE $$ HisC Hcr Htok with Hvac
    imodintro
    iexists S
    iframe HrS Hvac Hfh
  | some old =>
    simp only [kdFileState]
    icases Hfs with ⟨Hold, Hnew⟩
    rcases hv with h | h
    · -- the new contents survived
      subst h
      cases pb with
      | none =>
        imod nodeCrash γ.r.cluster kdRaftN id x E hE $$ HisC Hcr Htok with Hvac
        imodintro
        iexists S
        iframe HrS Hvac Hnew
      | some p =>
        obtain ⟨γb, S2, q', γr⟩ := p
        simp only
        icases Hnew with ⟨%n, Hrec, -, Hfh⟩
        iunfold kdBatchRec at Hrec
        icases Hrec with ⟨%st, %st', %ms, #Harm, Henter, Hrun, -, %Hst⟩
        obtain ⟨Hst1, Hst2⟩ := Hst
        ihave HrS : raftState γ.r.cluster id st.durable $$ [HrS]
        · rw [Hst1]; iexact HrS
        imod readyCrashEnter n γ.r.cluster kdRaftN id st st' ms x q' E hE $$ Hcr Htok Harm Hrun
          Henter HrS with ⟨HrS, Hvac⟩
        imodintro
        iexists S2
        rw [← Hst2]
        iframe HrS Hvac
        rw [Hst2]
        iexact Hfh
    · -- the old contents survived: the batch, if any, dropped
      have hv' : v = old := (Option.some.inj h).symm
      subst hv'
      imod nodeCrash γ.r.cluster kdRaftN id x E hE $$ HisC Hcr Htok with Hvac
      imodintro
      iexists S
      iframe HrS Hvac Hold

/-- **What `StartNode` starts from** (2026-11-22, ledger kvraft's `StartNode`: the boot's result, with the
generation's file names `fl`): the store's cluster, `durable`'s and `os`'s invariants for the file
`fl.df`, the generation's file invariant (allocated at the boot, `kd_file_alloc`, its crash token kept by
the crash obligation), the writer's half at the durable state `S` with the file outside a write's window
holding `cur`, which holds `S`, and raft's vacancy armed at `fl.x` (its crash token kept by the crash
obligation). -/
def kvStart (γ : KdNames) (vs : List w64) (dir : GoString) (id : w64) (fl : KdFileNames) (qc : Qp) :
    IProp GF :=
  iprop(∃ (S : RaftState) (cur : Option GoString),
    kdCluster γ vs ∗ Fs.osInv ∗ Fs.osSharedInv fl.fR ∗ DurFs.durInv fl.γd fl.df ∗
    DurFs.durHandle fl.γd fl.df fl.fR ∗ Fs.osCallPerm (Fs.callKey fl.fR fl.df.d) qc ∗
    kdFileInvK γ id fl ∗ ghostVar fl.wr (1 : Qp).half ((S, ⟨cur, none⟩, none) : KdWv) ∗
    fileHolds γ S cur ∗ nodeVacantA γ.r.cluster id fl.x ∗
    ⌜fl.df.Ok ∧ fl.df.name = kdFileName dir id ∧ 1 ≤ uint.nat id ∧ uint.nat id ≤ γ.max⌝)

/-- **The generation's file invariant, allocated at its boot** (decision C): from `durable`'s client
state outside a window at `cur`, the durable state `S` it holds, fresh writer and crash-token names: the
invariant, the writer's other half, and the crash token (the crash obligation's). -/
theorem kd_file_alloc (γ : KdNames) (id : w64) (γd : DurFs.DurGS) (df : DurFs.DFile) (fR : Fs.Roots)
    (x : CrashNames) (S : RaftState) (cur : Option GoString) (E : CoPset) :
    ⊢ DurFs.durSt (GF := GF) γd ⟨cur, none⟩ -∗ raftState γ.r.cluster id S -∗ fileHolds γ S cur ={E}=∗
      ∃ (wr tk : GName), kdFileInvK γ id ⟨γd, df, fR, wr, tk, x⟩ ∗
        ghostVar wr (1 : Qp).half ((S, ⟨cur, none⟩, none) : KdWv) ∗ token tk := by
  iintro Hds HrS #Hfh
  imod ghostVar_alloc (GF := GF) ((S, ⟨cur, none⟩, none) : KdWv) with ⟨%wr, Hwr⟩
  icases (ghostVar_split_half (GF := GF) wr 1 ((S, ⟨cur, none⟩, none) : KdWv)).1 $$ Hwr
    with ⟨Hwr1, Hwr2⟩
  imod token_alloc (GF := GF) with ⟨%tk, Htk⟩
  imod inv_alloc (kdRepN .@ uint.nat id) E (kdFileBody γ id ⟨γd, df, fR, wr, tk, x⟩)
    $$ [Hds HrS Hwr2] with #Hinv
  · inext
    iunfold kdFileBody
    iexists S, ⟨cur, none⟩, none
    iframe Hds Hwr2
    ileft
    iframe HrS
    iunfold kdFileState
    isplitr
    · iexact Hfh
    ipureintro; rfl
  imodintro
  iexists wr, tk
  iframe Hwr1 Htk
  iunfold kdFileInvK
  iexact Hinv

end boot

end kvraft
end EtcdGrove
end Perennial
