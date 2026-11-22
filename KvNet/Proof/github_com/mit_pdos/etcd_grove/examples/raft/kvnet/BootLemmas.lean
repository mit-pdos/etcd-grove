/-
# kvnet's boot: the file a crash left, and the durable state the next generation starts from (2026-11-22)

Drafted with no `.lake` (unchecked). `notes/kvnet-part.md`, "The crash law kvnet needs" and "`persist`".

A crash during a write's window may leave either file (`durable`'s crash lemma `durInv_crash`: the next
generation finds `v`, with `v = s.cur ∨ s.alt = some v`). The generation's file invariant
(`kdFileInvK`), carried by the crash obligation, says what each holds (`kdFileState`). `kd_boot_choose`
turns it into the next generation's start (raft's vacancy, the durable state `S'`, and the found
contents holding it):

* the window held a batch to `S2` and the new contents survived: the batch is entered at the boot
  (`readyCrashEnter.law`, raft's, a hypothesis until it lands);
* otherwise: raft's `nodeCrash` (the batch, if any, dropped), at the durable state `S`.

`readyCrashEnter.law` is the statement written for raft's agent (`notes/kvnet-part.md`).
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.DefsLaws

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

attribute [local instance] kdStorageModel

/-- **Entering a cut batch at the next boot** (raft's law, a hypothesis until raft's agent proves it:
`notes/kvnet-part.md`, "The crash law kvnet needs"): a batch cut and not entered (its *enter* unused)
may be entered after the crash, the arm's crash token giving the vacancy back as `nodeCrash` does. -/
abbrev readyCrashEnter.law : Prop :=
  ∀ (n : NodeH) (γ : Cluster) (N : Namespace) (id : w64) (st st' : NodeDriverState) (ms : List QMsg)
    (x : CrashNames) (E : CoPset), ↑N ⊆ E →
  ⊢ isCluster (GF := GF) γ N -∗ crashed -∗ nodeCrashTok γ id x -∗
      readyEnter n γ N id st st' ms -∗ raftState γ id st.durable ={E}=∗
      raftState γ id st'.durable ∗ nodeVacant γ id

/-- **The boot's choice** (see the file header): from the crashed generation's file state at `(S, s,
pb)` and the contents `v` the crash left, the next generation's durable state `S'`, raft's vacancy,
and `v` holding `S'`. -/
theorem kd_boot_choose (law : readyCrashEnter.law (GF := GF)) (γ : KdNames) (id : w64) (n : NodeH)
    (S : RaftState) (s : DurFs.DurSt) (pb : Option (GName × RaftState)) (x : CrashNames)
    (v : Option GoString) (E : CoPset) (hE : ↑kdRaftN ⊆ E) (hv : v = s.cur ∨ s.alt = some v) :
    ⊢ isCluster (GF := GF) γ.r.cluster kdRaftN -∗ crashed -∗ nodeCrashTok γ.r.cluster id x -∗
      raftState γ.r.cluster id S -∗ kdFileState γ id n S s pb ={E}=∗
      ∃ S' : RaftState, raftState γ.r.cluster id S' ∗ nodeVacant γ.r.cluster id ∗ fileHolds γ S' v := by
  iintro #HisC #Hcr Htok HrS Hfs
  rcases Hs : s with ⟨cur, alt⟩
  rw [Hs] at hv
  rw [Hs]
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
        obtain ⟨γb, S2⟩ := p
        simp only
        icases Hnew with ⟨%st, %st', %ms, Henter, -, %Hst, Hfh⟩
        obtain ⟨Hst1, Hst2⟩ := Hst
        ihave HrS : raftState γ.r.cluster id st.durable $$ [HrS]
        · rw [Hst1]; iexact HrS
        imod law n γ.r.cluster kdRaftN id st st' ms x E hE $$ HisC Hcr Htok Henter HrS
          with ⟨HrS, Hvac⟩
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

/-- **What `StartNode` starts from** (the boot's result, `kd_boot_choose`, with the file's names): the
store's cluster, `durable`'s and `os`'s invariants for the file `df` (its client state `s` outside a
window, `alt = none`), the durable state `S` that its contents hold, raft's vacancy armed at `x` (with
its crash token, which the crash obligation keeps), and both halves of the writer's variable, at
`(S, s, none)`. `StartNode` allocates the generation's file invariant `kdFileInvK` once raft's node
`n` exists, from `raftState`, `durSt` and one writer half. -/
def kvStart (γ : KdNames) (vs : List w64) (dir : GoString) (id : w64) (γd : DurFs.DurGS)
    (df : DurFs.DFile) (fR : Fs.Roots) (qc : Qp) (x : CrashNames) : IProp GF :=
  iprop(∃ (S : RaftState) (cur : Option GoString),
    kdCluster γ vs ∗ Fs.osInv ∗ Fs.osSharedInv fR ∗ DurFs.durInv γd df ∗
    DurFs.durHandle γd df fR ∗ Fs.osCallPerm (Fs.callKey fR df.d) qc ∗
    DurFs.durSt γd ⟨cur, none⟩ ∗ fileHolds γ S cur ∗ raftState γ.r.cluster id S ∗
    nodeVacantA γ.r.cluster id x ∗
    ghostVar (γ.wr id) (1 : Qp) ((S, ⟨cur, none⟩, none) : KdWv) ∗
    ⌜df.Ok ∧ df.name = kdFileName dir id ∧ 1 ≤ uint.nat id ∧ uint.nat id ≤ γ.max⌝)

end boot

end raft_kvnet
end EtcdGrove
end Perennial
