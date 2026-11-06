/-
**A restarted member's first batch enters the replay window** (R2d probe, 2026-11-06; DRAFT, the
fragment of `run`'s proof for the first batch after a restart, `notes/restart-plan.md`, R2d-5).
Lean-first (no Rocq counterpart).

At a restart the backend's ghost log `A` runs to its consistent index, past Go's applied index `ai`
(the WAL snapshot's), and raft hands its first batch `ce` from `ai + 1`. Both are prefixes of the
cluster's committed log (`srvRLogLb`), so one extends the other (`srvRLogLb_prefix`): either the
batch lies inside the window (its entries the ghost log's next ones, no new entry) or it runs past
it (the ghost log Go's log and the replays, then the new entries). In both cases the batch starts
with the pending replays `A.drop ai` (`winOk A [] (A.drop ai) ce`, `applyAll.specBatch`'s window
premise, `D = []` at the restart) and the ghost log after it is committed
(`srvRLogLb γ (A ++ winNew …)`, `kvBatchW`'s first row): `run_firstBatch_window`.

**R2d-2's statements (DRAFT, for Freeze 2; 2026-11-06).** The restart's starting point
(`srvRestartPt`: the node's handed log `P = γn.pre` a prefix of the backend's ghost log `A₀`, no conf
change in the window `A₀.drop |P|`; with `winNoMergedSend`), the server's `E.C` over `P`
(`srvCMW`), the apply thread's resources when `run` starts at `A₀` (`srvRestartAt`) and `run`'s loop
resources in the window (`applyResCW`, Go's index `aiGo = ai₀ + |P ++ A|` below the ghost one), each
today's at a first start by a law (`srvCMW_nil`, `srvRestartAt_nil`, `applyResCW_nil`). They are
not in the hub predicates yet: `isServerRunC`'s `Hsnap` (`rnSnapOnce … ai₀ at₀`: the storage's
snapshot at `ai₀ = 0` and `memSnapNone`) is a first start's, false at a restart whose WAL has a
snapshot, and is not in Q12's list (the probe extension's stop, `notes/restart-plan.md`, "R2d Draft, round
3"). The probe's glue
(`applyResCW_start`, `restart_firstBatch`): from the restart's conjunct and Go's fields at Go's
start index, `run`'s loop resources at the empty handed log, and the first batch's window premise.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyWindow
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SrvRaftLog
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthCompRows

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section lists
variable [GooseExts]

/-- A batch inside the pending replays agrees with them. -/
theorem winAgree_of_prefix_l : ∀ (W ms : List EntryModel), ms <+: W → winAgree W ms
  | [], _, _ => trivial
  | _ :: _, [], _ => trivial
  | w :: W, m :: ms, h => by
      obtain ⟨h1, h2⟩ := List.cons_prefix_cons.1 h
      exact ⟨h1.symm, winAgree_of_prefix_l W ms h2⟩

/-- A batch past the pending replays agrees with them. -/
theorem winAgree_of_prefix_r : ∀ (W ms : List EntryModel), W <+: ms → winAgree W ms
  | [], _, _ => trivial
  | _ :: _, [], h => by simp at h
  | w :: W, m :: ms, h => by
      obtain ⟨h1, h2⟩ := List.cons_prefix_cons.1 h
      exact ⟨h1, winAgree_of_prefix_r W ms h2⟩

/-- A batch inside the pending replays has no new entry. -/
theorem winNew_of_prefix_l {α : Type} : ∀ (W ms : List α), ms <+: W → winNew W ms = []
  | [], ms, h => by simpa [winNew] using List.eq_nil_of_prefix_nil h
  | _ :: _, [], _ => rfl
  | _ :: W, _ :: ms, h => winNew_of_prefix_l W ms (List.cons_prefix_cons.1 h).2

/-- A batch past the pending replays: they and its new entries. -/
theorem winNew_of_prefix_r {α : Type} : ∀ (W ms : List α), W <+: ms → W ++ winNew W ms = ms
  | [], ms, _ => rfl
  | _ :: _, [], h => by simp at h
  | w :: W, m :: ms, h => by
      obtain ⟨h1, h2⟩ := List.cons_prefix_cons.1 h
      show w :: (W ++ winNew W ms) = m :: ms
      rw [h1, winNew_of_prefix_r W ms h2]

/-- The ghost index at the restart: Go's index and the pending replays, the ghost log's length. -/
theorem winGhost_restart (ai : w64) (A : List EntryModel) (hle : uint.nat ai ≤ A.length)
    (hA : (A.length : Int) < 2 ^ 64) :
    uint.Z (winGhost ai (A.drop (uint.nat ai))) = A.length := by
  have hn := uint_nat_eq ai
  cases hd : A.drop (uint.nat ai) with
  | nil =>
    have := List.length_drop (i := uint.nat ai) (l := A)
    rw [hd, List.length_nil] at this
    simp only [winGhost]; omega
  | cons d D' =>
    have := List.length_drop (i := uint.nat ai) (l := A)
    rw [hd] at this
    simp only [winGhost]
    rw [show ((d :: D').length : Int) = A.length - uint.nat ai by omega]
    word

end lists

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **A restarted member's first batch in its window** (the R2d probe's `run` fragment): from the
backend's ghost log `A` and raft's handed log at Go's index (`A.take ai ++ ce`), both committed, the
batch starts with the pending replays `A.drop ai` (`winOk`, no replay done yet) and the ghost log
after it is committed. -/
theorem run_firstBatch_window (γ : ServerRaftNames) (ai : w64) (A ce : List EntryModel)
    (hle : uint.nat ai ≤ A.length) :
    srvRLogLb (GF := GF) γ A ∗ srvRLogLb γ (A.take (uint.nat ai) ++ ce) ⊢
      ⌜winOk A [] (A.drop (uint.nat ai)) ce⌝ ∗ srvRLogLb γ (A ++ winNew (A.drop (uint.nat ai)) ce) := by
  iintro ⟨#HA, #HL⟩
  ihave %Hp := srvRLogLb_prefix γ A (A.take (uint.nat ai) ++ ce) $$ [HA HL]
  · iframe HA HL
  have hsuf : ([] ++ A.drop (uint.nat ai)) <:+ A := by
    rw [List.nil_append]; exact List.drop_suffix _ _
  rcases Hp.symm with hp | hp
  · -- the batch inside the window
    have hce : ce <+: A.drop (uint.nat ai) := by
      have hp2 : A.take (uint.nat ai) ++ ce <+: A.take (uint.nat ai) ++ A.drop (uint.nat ai) := by
        rw [List.take_append_drop]; exact hp
      exact (List.prefix_append_right_inj _).1 hp2
    rw [winNew_of_prefix_l _ _ hce, List.append_nil]
    iframe HA
    ipureintro; exact ⟨hsuf, winAgree_of_prefix_l _ _ hce⟩
  · -- the batch past the window
    have hW : A.drop (uint.nat ai) <+: ce := by
      have hp2 : A.take (uint.nat ai) ++ A.drop (uint.nat ai) <+: A.take (uint.nat ai) ++ ce := by
        rw [List.take_append_drop]; exact hp
      exact (List.prefix_append_right_inj _).1 hp2
    have hG : A ++ winNew (A.drop (uint.nat ai)) ce = A.take (uint.nat ai) ++ ce :=
      calc A ++ winNew (A.drop (uint.nat ai)) ce
          = (A.take (uint.nat ai) ++ A.drop (uint.nat ai)) ++ winNew (A.drop (uint.nat ai)) ce := by
            rw [List.take_append_drop]
        _ = A.take (uint.nat ai) ++ ce := by rw [List.append_assoc, winNew_of_prefix_r _ _ hW]
    rw [hG]
    iframe HL
    ipureintro; exact ⟨hsuf, winAgree_of_prefix_r _ _ hW⟩

end laws

/-! ## R2d-2's statements (DRAFT, Freeze 2) -/

section r2d2
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The restart's starting point** (R2d-2, Q12; DRAFT): the node's handed log `P` (`γn.pre`, the
WAL snapshot's prefix) a prefix of the backend's ghost log `A₀` (through its consistent index), and
no conf change in the window `A₀.drop |P|` (`winNoConf`, R2d review F1). In `%HEr`'s place of
`γn.pre = []`. -/
def srvRestartPt (P A₀ : List EntryModel) : Prop :=
  P <+: A₀ ∧ winNoConf (A₀.drop P.length)

/-- A first start: nothing handed, nothing applied. -/
theorem srvRestartPt_nil : srvRestartPt [] [] := ⟨List.nil_prefix, winNoConf_nil⟩

/-- **The server's `E.C` after the handed log `P`** (R2d-2, DRAFT; `srvCM`'s restart form): a batch
`L` raft hands consecutive from `|P| + 1` (the ghost of `ai₀` past `P`), committed after `P`. -/
def srvCMW (on : Bool) (P : List EntryModel) (ρ : ReqNames) (E : apply.AEnv GF) (ai₀ c₀ : w64)
    (x₀ : apply.ApplyKV) (L : List EntryModel) : IProp GF :=
  iprop(⌜srvIdxOk (winGhost ai₀ P) L ∧ logShapeM on ρ.kv.lm L⌝ ∗ batchWaitOk ρ E L ∗
    srvRLogLb ρ.raft (P ++ L))

/-- A first start: `srvCM`. -/
theorem srvCMW_nil (on : Bool) (ρ : ReqNames) (E : apply.AEnv GF) (ai₀ c₀ : w64)
    (x₀ : apply.ApplyKV) : srvCMW (GF := GF) on [] ρ E ai₀ c₀ x₀ = srvCM on ρ E ai₀ c₀ x₀ := rfl

/-- **The apply thread's resources when `run` starts after the handed log `P`** (R2d-2, Q12;
DRAFT; `applyStartC`'s restart form): the restart's starting point at the backend's ghost log
`A₀` (`srvRestartPt`, `winNoMergedSend` of its window), the ghost rows at `A₀` (the applied index
`winGhost ai₀ A₀`, `kvRunM`, `srvRest`, `srvApRes`, the consistent index `winGhost c₀ A₀`), Go's
rows at Go's start index `winGhost ai₀ P` (`loopOk`, the snapshot resources). -/
def srvRestartAt (C : AuthC) (s : Loc) (γ : ApplyNames) (ci : Loc) (b : GoInterface)
    (E : apply.AEnv GF) (γr : ReadNames) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV) (γw : GName)
    (P : List EntryModel) : IProp GF :=
  iprop(∃ (A₀ : List EntryModel) (st₀ : ApplyState) (a t : w64) (f : Bool),
    ⌜srvRestartPt P A₀⌝ ∗ winNoMergedSend γr.raft.raft (A₀.drop P.length) ∗
    applyThread γ st₀ ∗ ⌜loopOk γ st₀ (winGhost ai₀ P) ∧ winGhost c₀ A₀ = ciEff γ st₀.k⌝ ∗
    applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvBemuReaderAt s E.γbe ∗
    srvWgReader s ∗ srvApplyKVC C s E γw x₀ srvAuthSt0 ∗
    srvAppliedOwn γr (winGhost ai₀ A₀) ∗ appliedLogAt γr (winGhost ai₀ A₀) x₀.log ∗
    kvRunM C.isOn γr ai₀ c₀ A₀ x₀ srvAuthSt0 ∗ srvRest E γr A₀ ∗
    srvApRes s γr A₀ ∗ srvForceSnapAddr s ↦ f ∗ acTok C (ciEff γ st₀.k) ∗
    srvSnapOwn s ci E γr γ (winGhost ai₀ P))

/-- **A first start's `applyStartC` is the restart form's at `P = []`** (`A₀ = []`). -/
theorem srvRestartAt_nil (C : AuthC) (s : Loc) (γ : ApplyNames) (ci : Loc) (b : GoInterface)
    (E : apply.AEnv GF) (γr : ReadNames) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV) (γw : GName) :
    applyStartC (GF := GF) C s γ ci b E γr ai₀ c₀ x₀ γw ⊢
      srvRestartAt C s γ ci b E γr ai₀ c₀ x₀ γw [] := by
  iintro H
  iunfold applyStartC at H
  icases H with ⟨%st₀, %a, %t, %f, Hth, %Hok, Hbe, Hca, Hlg, Hbm, Hwg, Hkv, Hao, Hal, Hkr, Hrest, Hap,
    Hfs, Htok, Hso⟩
  iunfold srvRestartAt
  iexists [], st₀, a, t, f
  simp only [winGhost, List.drop_nil, List.length_nil]
  iframe Hth Hbe Hca Hlg Hbm Hwg Hkv Hao Hal Hkr Hrest Hap Hfs Htok Hso
  isplitr
  · ipureintro; exact srvRestartPt_nil
  isplitr
  · iapply winNoMergedSend_nil
  ipureintro; exact Hok

/-- `kvRunM`'s log is committed. -/
theorem kvRunM_lb (on : Bool) (γr : ReadNames) (ai₀ c₀ : w64) (A : List EntryModel)
    (x : apply.ApplyKV) (st : auth.AuthState) :
    kvRunM (GF := GF) on γr ai₀ c₀ A x st ⊢ srvRLogLb γr.raft A ∗ kvRunM on γr ai₀ c₀ A x st := by
  refine (persistent_entails_left ?_).trans sep_comm.1
  cases on
  · unfold kvRunM kvRun kvApplied kvAppliedL
    iintro ⟨⟨⟨#H, -⟩, -⟩, -⟩; iexact H
  · unfold kvRunM kvRunAtOn kvAppliedOn kvAppliedLOn
    iintro ⟨⟨⟨#H, -⟩, -⟩, -⟩; iexact H

/-- **`run`'s loop resources in a restart's window** (R2d-2, DRAFT; `applyResC`'s restart form,
Q9 (d)): after the handed log `C.rn.pre ++ A` (Go's log; Go's index `aiGo = ai₀ + |P ++ A|`), with
the backend's ghost log starting at `A₀`: the pending replays `W = A₀.drop |P ++ A|`, the ghost log
`P ++ A ++ W` and the ghost index `winGhost aiGo W` (`aiGo ≤` it), the replays done `A` while `W` is
pending. Go's rows (`loopOk`, `ep`, the snapshot's state and resources, the applied term) at Go's
index and log, the ghost rows (`srvAppliedOwn`, `appliedLogAt`, `kvRunM`, `srvRestW`, `srvApRes`,
`epCsAt`, the consistent index's pins) at the ghost's. `applyResC` at a first start
(`applyResCW_nil`). -/
def applyResCW (K : AuthC) (C : ApplyCtx GF) (A₀ A : List EntryModel) : IProp GF :=
  iprop(∃ (B : ApplyBe GF) (st : ApplyState) (ai at' a t : w64) (cs : Loc) (x : apply.ApplyKV)
      (sa : auth.AuthState),
    ⌜beSucc C.γ C.E B.γ B.E⌝ ∗ isServerC K C.s B.γ C.ci B.TM B.E C.ρ C.γr ∗
    epAppliedIAddr C.ep ↦ ai ∗ epAppliedTAddr C.ep ↦ at' ∗ epConfState C.ep cs ∗
    epCsAt C.ρ.raft ((C.rn.pre ++ A) ++ A₀.drop (C.rn.pre ++ A).length) cs ∗
    srvSnapState C.s C.ep C.ms C.γs ai (W64 0) ∗ applyThread B.γ st ∗ applyBackend B.γ C.ci B.b ∗ ciApplying C.ci a t ∗
    srvLgReader C.s ∗ srvBemuReaderAt C.s C.E.γbe ∗ srvWgReader C.s ∗ srvApplyKVC K C.s B.E C.γw x sa ∗
    srvAppliedOwn C.γr (winGhost ai (A₀.drop (C.rn.pre ++ A).length)) ∗
    appliedLogAt C.γr (winGhost ai (A₀.drop (C.rn.pre ++ A).length)) x.log ∗
    kvRunM K.isOn C.γr C.ai₀ C.c₀ ((C.rn.pre ++ A) ++ A₀.drop (C.rn.pre ++ A).length) x sa ∗
    srvRestW B.E C.γr ((C.rn.pre ++ A) ++ A₀.drop (C.rn.pre ++ A).length)
      (if A₀.drop (C.rn.pre ++ A).length = [] then [] else A) ∗
    srvApRes C.s C.γr ((C.rn.pre ++ A) ++ A₀.drop (C.rn.pre ++ A).length) ∗
    (∃ kv : GoInterface, srvKVAddr C.s ↦□ kv ∗ txn.isKV kv B.E.s B.E.γ) ∗
    rnWalTokA C.rn (srvRAddr C.s) (1 : Qp).half ∗
    (∃ w : Nat, srvWTTaken C.wt.cnt w) ∗ acTok K (ciEff B.γ st.k) ∗
    srvSnapOwn C.s C.ci B.E C.γr B.γ ai ∗
    ⌜loopOk B.γ st ai ∧ uint.Z ai = uint.Z C.ai₀ + (C.rn.pre ++ A).length ∧
      ciJ (ciEff B.γ st.k) C.c₀ (winGhost ai (A₀.drop (C.rn.pre ++ A).length)) ∧
      uint.Z (winGhost ai (A₀.drop (C.rn.pre ++ A).length)) ≤ uint.Z (ciEff B.γ st.k) ∧
      lastTermIs (C.rn.pre ++ A) at'⌝)

/-- **A first start's loop resources are the restart form's at `P = A₀ = []`**. -/
theorem applyResCW_nil (K : AuthC) (C : ApplyCtx GF) (A : List EntryModel) (hP : C.rn.pre = []) :
    applyResCW (GF := GF) K C [] A = applyResC K C A := by
  unfold applyResCW applyResC
  simp only [hP, List.nil_append, List.drop_nil, List.append_nil, winGhost, ite_true, srvRestW_nil]

/-! ### The probe's glue: from the restart's conjunct to `run`'s loop and its first batch -/

private theorem winGhost_Z' {α : Type} (ai : w64) (R : List α) (h : uint.Z ai + R.length < 2 ^ 64) :
    uint.Z (winGhost ai R) = uint.Z ai + R.length := by
  cases R with
  | nil => simp [winGhost]
  | cons r R' => simp only [winGhost]; word

/-- A log consecutive from `a0` (w64 indices) is shorter than `2 ^ 64`. -/
private theorem idxOk_len_lt' (a0 : w64) (G : List EntryModel) (h : srvIdxOkW a0 G) :
    (G.length : Int) < 2 ^ 64 := by
  cases hG : G.length with
  | zero => simp
  | succ k =>
    have hk : k < G.length := by omega
    have h1 := (h k (G[k]'hk) (List.getElem?_eq_getElem hk)).1
    have hb : uint.Z (G[k]'hk).index < 2 ^ 64 := by word
    have hz : 0 ≤ uint.Z a0 := by word
    omega

/-- The ghost index past the handed log and its window is the ghost log's. -/
theorem winGhost_split (ai₀ : w64) (P A₀ : List EntryModel) (hP : P <+: A₀)
    (hov : uint.Z ai₀ + A₀.length < 2 ^ 64) :
    winGhost (winGhost ai₀ P) (A₀.drop P.length) = winGhost ai₀ A₀ := by
  have hl := hP.length_le
  have h1 := winGhost_Z' ai₀ P (by omega)
  have hd := List.length_drop (i := P.length) (l := A₀)
  have h2 := winGhost_Z' (winGhost ai₀ P) (A₀.drop P.length) (by rw [h1, hd]; omega)
  have h3 := winGhost_Z' ai₀ A₀ hov
  rw [h1, hd] at h2
  apply uint_Z_inj.1
  rw [h2, h3]; omega

/-- The handed log and its window are the ghost log. -/
theorem restart_ghost (P A₀ : List EntryModel) (hP : P <+: A₀) :
    (P ++ []) ++ A₀.drop (P ++ []).length = A₀ := by
  obtain ⟨T, rfl⟩ := hP
  simp

/-- **The restart's first batch in its window** (`run_firstBatch_window` at the restart's point):
from the ghost log `A₀` and the first batch `ce` raft hands after `P` (`srvCMW`'s), both committed,
`applyAll.specBatch`'s window premise for it (no replay done yet) and the ghost log after it. -/
theorem restart_firstBatch (γ : ServerRaftNames) (ai : w64) (P A₀ ce : List EntryModel)
    (hpt : srvRestartPt P A₀) (hai : uint.nat ai = P.length) :
    srvRLogLb (GF := GF) γ A₀ ∗ srvRLogLb γ (P ++ ce) ⊢
      ⌜winOk A₀ [] (A₀.drop P.length) ce⌝ ∗ srvRLogLb γ (A₀ ++ winNew (A₀.drop P.length) ce) := by
  have ht : A₀.take P.length = P := by
    obtain ⟨T, rfl⟩ := hpt.1; simp
  have h := run_firstBatch_window (GF := GF) γ ai A₀ ce (by rw [hai]; exact hpt.1.length_le)
  rw [hai, ht] at h
  exact h

/-- `applyResCW`'s ghost log is committed. -/
theorem applyResCW_lb (K : AuthC) (C : ApplyCtx GF) (A₀ A : List EntryModel) :
    applyResCW (GF := GF) K C A₀ A ⊢
      srvRLogLb C.γr.raft ((C.rn.pre ++ A) ++ A₀.drop (C.rn.pre ++ A).length) ∗ applyResCW K C A₀ A := by
  refine (persistent_entails_left ?_).trans sep_comm.1
  iintro H
  iunfold applyResCW at H
  icases H with ⟨%B, %st, %ai, %at', %a, %t, %cs, %x, %sa, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, Hkr, -⟩
  icases kvRunM_lb _ _ _ _ _ _ _ $$ Hkr with ⟨#H, -⟩
  iexact H

/-- **`run`'s loop at a restart, its first batch** (the probe extension's last step): from the loop's
resources at the empty handed log (`applyResCW … A₀ []`) and the first batch `ce` committed after
`P` (`srvCMW`'s row), the batch's window premise (`winOk`, `applyAll.specBatch`'s) at the ghost log
`A₀`. -/
theorem applyResCW_firstBatch (K : AuthC) (C : ApplyCtx GF) (A₀ ce : List EntryModel) (ai : w64)
    (hpt : srvRestartPt C.rn.pre A₀) (hai : uint.nat ai = C.rn.pre.length) :
    applyResCW (GF := GF) K C A₀ [] ∗ srvRLogLb C.γr.raft (C.rn.pre ++ ce) ⊢
      ⌜winOk A₀ [] (A₀.drop C.rn.pre.length) ce⌝ ∗ applyResCW K C A₀ [] := by
  iintro ⟨H, #Hce⟩
  icases applyResCW_lb K C A₀ [] $$ H with ⟨#Hlb, H⟩
  ihave #HA₀ : srvRLogLb C.γr.raft A₀ $$ []
  · have e : srvRLogLb (GF := GF) C.γr.raft ((C.rn.pre ++ []) ++ A₀.drop (C.rn.pre ++ []).length) =
        srvRLogLb C.γr.raft A₀ := by rw [restart_ghost C.rn.pre A₀ hpt.1]
    rw [← e]; iexact Hlb
  icases restart_firstBatch C.γr.raft ai C.rn.pre A₀ ce hpt hai $$ [HA₀ Hce] with ⟨%hw, -⟩
  · iframe HA₀ Hce
  iframe H
  ipureintro; exact hw

/-- **`run`'s loop resources at a restart's start** (the probe extension, R2d-2): from the restart's
conjunct (`srvRestartAt` at the handed log `C.rn.pre`) and what `run` holds of Go's fields at Go's
start index `winGhost ai₀ P`, `run`'s loop resources at the empty handed log, over the restart's
ghost log `A₀`. The premises `isServerRunC` does not give at a restart (the probe's stop): Go's
snapshot state at Go's start index (`Hsnap`'s `rnSnapOnce` gives it at `ai₀`, with `memSnapNone`),
the conf state's voters at `A₀`, the applied term `P`'s. -/
theorem applyResCW_start (K : AuthC) (C : ApplyCtx GF) (TM : MetaCI → IProp GF) (at' : w64)
    (cs : Loc) (hai₀ : C.ai₀ = W64 0) (hc₀ : uint.Z C.c₀ ≤ uint.Z C.ai₀)
    (hlt : lastTermIs C.rn.pre at') :
    isServerC (GF := GF) K C.s C.γ C.ci TM C.E C.ρ C.γr ∗
      epAppliedIAddr C.ep ↦ winGhost C.ai₀ C.rn.pre ∗ epAppliedTAddr C.ep ↦ at' ∗
      epConfState C.ep cs ∗
      (□ ∀ A₀ : List EntryModel, ⌜srvRestartPt C.rn.pre A₀⌝ -∗ epCsAt C.ρ.raft A₀ cs) ∗
      (∀ f : Bool, srvForceSnapAddr C.s ↦ f -∗
        srvSnapState C.s C.ep C.ms C.γs (winGhost C.ai₀ C.rn.pre) (W64 0)) ∗
      (∃ kv : GoInterface, srvKVAddr C.s ↦□ kv ∗ txn.isKV kv C.E.s C.E.γ) ∗
      rnWalTokA C.rn (srvRAddr C.s) (1 : Qp).half ∗ (∃ w : Nat, srvWTTaken C.wt.cnt w) ∗
      srvRestartAt K C.s C.γ C.ci C.b C.E C.γr C.ai₀ C.c₀ C.x₀ C.γw C.rn.pre ⊢
    ∃ A₀ : List EntryModel, ⌜srvRestartPt C.rn.pre A₀⌝ ∗
      winNoMergedSend C.γr.raft.raft (A₀.drop C.rn.pre.length) ∗ applyResCW K C A₀ [] := by
  iintro ⟨#Hsrv, Hai, Hat, Hcs, #Hcsat, Hss, Hkvf, Hwt, Hwtt, Hrs⟩
  iunfold srvRestartAt at Hrs
  icases Hrs with ⟨%A₀, %st₀, %a, %t, %f, %Hpt, #Hnms, Hth, %Hok, Hbe, Hca, Hlg, Hbm, Hwg, Hkv,
    Hao, Hal, Hkr, Hrest, Hap, Hfs, Htok, Hso⟩
  -- no overflow: the ghost log's length is the consistent index's (`kvRunM`'s names: `c₀ = 0`)
  ihave Hkr : iprop(kvAppliedM K.isOn C.γr.raft C.γr.kv srvAuthSt0 A₀ C.x₀ srvAuthSt0 ∗
      ⌜C.γr.kv.c0 = C.c₀ ∧ C.γr.raft.ai0 = C.ai₀⌝) $$ [Hkr]
  · rw [← kvRunM_split]; iexact Hkr
  icases Hkr with ⟨Hka, %Hkc⟩
  ihave Hkr : kvRunM K.isOn C.γr C.ai₀ C.c₀ A₀ C.x₀ srvAuthSt0 $$ [Hka]
  · rw [kvRunM_split]; iframe Hka; ipureintro; exact Hkc
  icases kvRunM_lb _ _ _ _ _ _ _ $$ Hkr with ⟨#HlbA, Hkr⟩
  ihave %hidx := srvRLogLb_idx _ A₀ $$ HlbA
  have hlen := idxOk_len_lt' _ _ hidx
  have h0 : uint.Z C.ai₀ = 0 := by rw [hai₀]; rfl
  have hc0 : uint.Z C.c₀ = 0 := by have : 0 ≤ uint.Z C.c₀ := by word
                                   omega
  have hPl := Hpt.1.length_le
  have hov : uint.Z C.ai₀ + A₀.length < 2 ^ 64 := by omega
  have hsplit := winGhost_split C.ai₀ C.rn.pre A₀ Hpt.1 hov
  have hgP := winGhost_Z' C.ai₀ C.rn.pre (by omega)
  have hgA := winGhost_Z' C.ai₀ A₀ hov
  have hgC := winGhost_Z' C.c₀ A₀ (by omega)
  ihave Hss := Hss $$ Hfs
  ihave #Hca' := Hcsat $$ %A₀ %Hpt
  iexists A₀
  iframe Hnms
  isplitr
  · ipureintro; exact Hpt
  iunfold applyResCW
  iexists ⟨C.γ, TM, C.E, C.b⟩, st₀, winGhost C.ai₀ C.rn.pre, at', a, t, cs, C.x₀, srvAuthSt0
  rw [restart_ghost C.rn.pre A₀ Hpt.1]
  simp only [List.append_nil, hsplit, ite_self, srvRestW_nil]
  isplitr
  · ipureintro; exact beSucc_refl C.γ C.E
  iframe Hsrv Hai Hat Hcs Hca' Hss Hth Hbe Hca Hlg Hbm Hwg Hkv Hao Hal Hkr Hrest Hap Hkvf Hwt Hwtt
    Htok Hso
  ipureintro
  have hce := Hok.2
  refine ⟨Hok.1, by rw [hgP], Or.inr ⟨?_, ?_⟩, ?_, hlt⟩
  · rw [hgA]; omega
  · rw [← hce, hgC, hgA]; omega
  · rw [← hce, hgC, hgA]; omega

end r2d2

end EtcdGrove
end Perennial
