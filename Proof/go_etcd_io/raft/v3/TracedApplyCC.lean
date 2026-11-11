/-
Lean-first (no Rocq counterpart). Trace-check's Q8 stage 1, slice 29n (2026-11-11; `notes/decisions.md`,
"Q8 stage 1 (slice 29n)"): **a booted node's `ApplyConfChange` line** (the application's
`ApplyConfChange` of a bootstrap conf entry, after the node's first `Ready`; `switchToConfig`'s
`traceConfChangeEvent`).

The specification's `ApplySimpleConfChange` at a server related to raft's idle state (`SimIdle`) whose
commit index covers the bootstrap log reapplies its configuration (`AccIdle` at the voters, the last
committed configuration entry being the last bootstrap entry: `accIdle_of_simServerR`), and its effect
(`lineEffect_applyCC`, `accSrv`) zeroes progress only outside the voters, which the share (`toC`) does
not hold: the share is unchanged (`toC_accSrv`). So the line is a step from the pinned share to itself
(`phaseStepB_applyCC`), its facts kept by `fxPres_skip`, and the gate of `traceConfChangeEvent` at a
booted node is `trCapB_hookGate_applyCC` (either mode: untraced, the struct's nil logger).
Raft-internal (not on `etc/api/raft.txt`).
-/
module

public import Proof.go_etcd_io.raft.v3.TraceSimMatch
public import Proof.go_etcd_io.raft.v3.TracedFamilies
public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecv
public import Proof.go_etcd_io.raft.v3.TracedHooks

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section pure
variable [GooseExts]

/-- The specification's `SelectLastInSubSeq` fold (`ApplySimpleConfChange`'s), for a predicate that holds
exactly below `B` on the scanned range: one past the last position, `min N B`. -/
theorem foldl_lastBelow (p : Nat → Bool) (B : Nat) :
    ∀ N, (∀ n, n < N → p n = decide (n < B)) →
      (List.range N).foldl (fun (acc : Nat) n => if p n then n + 1 else acc) 0 = min N B := by
  intro N
  induction N with
  | zero => intro _; simp
  | succ N ih =>
    intro h
    rw [List.range_succ, List.foldl_append, ih (fun n hn => h n (by omega))]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [h N (by omega)]
    by_cases hN : N < B
    · simp only [hN, decide_true, ↓reduceIte]; omega
    · simp only [hN, decide_false, Bool.false_eq_true, ↓reduceIte]; omega

/-- An abstract log's entry type at a position: a configuration entry exactly within the bootstrap log. -/
theorem logAbs_type (C : List w64) (bl : Nat) (l : List EntryM) (n : Nat) (hn : n < l.length) :
    ((logAbs C bl 1 l)[n]?).map Etcdraft.Entry.type =
      some (if n < bl then Etcdraft.EntryType.config else Etcdraft.EntryType.value) := by
  unfold logAbs
  rw [List.getElem?_mapIdx, List.getElem?_eq_getElem hn]
  simp only [Option.map_some, entAbs]
  by_cases h : n < bl
  · simp only [show 1 + n ≤ bl by omega, h, ↓reduceIte]
  · simp only [show ¬ 1 + n ≤ bl by omega, h, ↓reduceIte]

/-- **A related server reapplies its configuration** (`AccIdle` at the voters): its configuration is
the voters' (`SimServerR`), nothing pending, and the last configuration entry within its commit index is
the last bootstrap entry, whose value is the voters' configuration, once the commit index covers the
bootstrap log (`|C| ≤ commit ≤ |log|`). -/
theorem accIdle_of_simServerR (C : List w64) (s : PState) (a : Etcdraft.Server)
    (hR : SimServerR C C.length s a) (hC : C ≠ [])
    (hcb : (C.length : Int) ≤ uint.Z s.commit) (hcl : uint.Z s.commit ≤ (s.log.length : Int)) :
    AccIdle a (confAbs C) [] := by
  obtain ⟨-, -, -, -, -, hlog, hci, hcfg, hpc, -, -⟩ := hR
  have hlen : a.log.length = s.log.length := by rw [hlog, logAbs_length]
  have hC0 : 0 < C.length := List.length_pos_iff.2 hC
  refine ⟨by rw [hcfg]; rfl, by rw [hci, hlen]; exact hcl, hpc, C.length, ?_, hC0, by rw [hci]; exact hcb,
    ?_, by rw [hcfg]⟩
  · have hN : a.commitIndex.toNat ≤ s.log.length := by rw [hci]; omega
    have hB : C.length ≤ a.commitIndex.toNat := by rw [hci]; omega
    have := foldl_lastBelow (fun n => ((a.log[n]?).map Etcdraft.Entry.type) == some .config) C.length
      a.commitIndex.toNat (fun n hn => by
        rw [hlog, logAbs_type C C.length s.log n (by omega)]
        by_cases h : n < C.length
        · simp [h]
        · simp [h])
    rw [this]; omega
  · rw [hlog]
    unfold logAbs
    have hlt : C.length - 1 < s.log.length := by omega
    rw [List.getElem?_mapIdx, List.getElem?_eq_getElem hlt]
    simp only [Option.map_some, entAbs]
    simp only [show 1 + (C.length - 1) = C.length by omega, List.take_length, Nat.le_refl, ↓reduceIte]

/-- `accSrv` at the voters' configuration leaves the share as it was (`toC` keeps only the voters'
progress). -/
theorem toC_accSrv (C : List w64) (a : Etcdraft.Server) (lr : Etcdraft.SetIds) :
    toC (confAbs C) (accSrv a (confAbs C) lr) = toC (confAbs C) a := by
  unfold toC accSrv
  simp only
  congr 1
  apply List.map_congr_left
  intro j hj
  have : ((confAbs C).union lr).contains j = true := by
    rw [List.contains_iff_mem]
    unfold Etcdraft.SetIds.union
    rw [setIds_mk_mem]
    exact List.mem_append_left _ hj
  simp only [this, ↓reduceIte]

/-- An `ApplyConfChange` event's name. -/
theorem ccEvOf_name {id : w64} {s : NState} {c cn : CfgM} {e : TraceEv} (h : CCEvOf id s c cn e) :
    gsStr e.name = "ApplyConfChange" := by
  have hname := h.1
  simp only [evtNames] at hname
  have : e.name = go!"ApplyConfChange" := by have := hname; simp at this; exact this.symm
  rw [this]; rfl

end pure

section phase
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]

/-- **A booted node's `ApplyConfChange` line's phase step**: at the share pinned at a server
idle-related to `s` whose commit index covers the bootstrap log (`|C0| ≤ commit ≤ lastIndex`), the line
is `lineEffect_applyCC` (the configuration reapplied, `accIdle_of_simServerR`), into the same pinned
share (`toC_accSrv`), nothing sent. -/
theorem phaseStepB_applyCC (id : w64) (c cn : CfgM) (s : NState) (C0 : List w64) (cs0 : ServerC)
    (P0 : List Etcdraft.Msg) (hidle : SimIdle C0 s cs0 P0)
    (hcb : (C0.length : Int) ≤ uint.Z s.logst.committed)
    (hcl : uint.Z s.logst.committed ≤ uint.Z (plastIndex (toPState s))) :
    PhaseStepB id c (CCEvOf id s c cn) (VPin C0 cs0 P0) (VPin C0 cs0 P0) := by
  rintro C cs P ⟨rfl, rfl, rfl⟩ ⟨-, hout, hC⟩ e he
  have hname := ccEvOf_name he
  obtain ⟨-, hnid, -, hvote, -, -, -, ⟨xs, ys, -, hys, hconf⟩, hmsg, -⟩ := he
  rw [hout, elements_empty_nil] at hys
  have hys0 := List.Perm.eq_nil hys
  subst hys0
  refine ⟨hnid, by rw [hname]; decide, ?_⟩
  intro a ha
  obtain ⟨a0, ha0, hR0, hshape, -⟩ := hidle
  have hR : SimServerR C C.length (toPState s) a := simServerR_toC (ha0.trans ha.symm) hR0
  have hacc : AccIdle a (confAbs C) [] := by
    apply accIdle_of_simServerR C (toPState s) a hR (List.ne_nil_of_mem hC) hcb
    rw [← plastIndex_length C.length (toPState s) hshape]; exact hcl
  refine ⟨accSrv a (confAbs C) [], [], ⟨rfl, by rw [toC_accSrv]; exact ha, by rw [List.append_nil]⟩,
    fun _ h => by simp at h, ?_⟩
  exact lineEffect_applyCC C e id s.vote xs a _ hnid hvote hconf hmsg hname hC
    (confAbs C) [] hacc

end phase

section gate
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The gate of a booted node's `ApplyConfChange` line, either mode** (`switchToConfig`'s
`traceConfChangeEvent` at the application's `ApplyConfChange`): the capability, booted, idle at `s`,
gives the hook's gate for any `CCEvOf` event of `s` at the configuration `c` (the old one, the voters')
to the new one `cn` (of at most as many voters), whose update gives the capability back, idle at `s`
(the share unchanged: `phaseStepB_applyCC`, `fxPres_skip`), its last event `Λ'`'s. The commit index
covers the bootstrap log (`hboot`: raft's ghost state, `ownRaftGhost`'s `%Hboot`) and is within the log
(`hcl`); the event's numbers are below `traceNumBound` (`hbnd`, traced). Untraced: the struct's nil
logger (`hok`). -/
theorem trCapB_hookGate_applyCC (tr : Option GName) (γ : RaftNames) (r : Loc) (id : w64) (c cn : CfgM)
    (tl0 : GoInterface) (s : NState) (Λ Λ' : Option TraceEv → Prop)
    (hΛ : ∀ e, CCEvOf id s c cn e → Λ' (some e))
    (hboot : (γ.reBoot.length : Int) ≤ uint.Z s.logst.committed)
    (hcl : uint.Z s.logst.committed ≤ uint.Z (plastIndex (toPState s)))
    (hcn : (elements cn.incoming).length ≤ (elements c.incoming).length)
    (hbnd : tr.isSome → uint.nat s.term < traceNumBound ∧ uint.nat s.logst.committed < traceNumBound ∧
      uint.nat (plastIndex (toPState s)) < traceNumBound)
    (hok : tr = none → TraceLoggerOk tl0) :
    (r.[raft, go!"traceLogger"] ↦□ tl0 ∗ trCapB tr γ r id c true (fun C => SimIdle C s) Λ : IProp GF) ⊢
      HookGate tr r (CCEvOf id s c cn) (trCapB tr γ r id c true (fun C => SimIdle C s) Λ') := by
  cases tr with
  | none =>
    iintro ⟨#Hl, Hcap⟩
    ihave Hfx : FxPresUT (GF := GF) none γ id (CCEvOf id s c cn) phaseBot phaseBot iprop(emp) $$ []
    · simp only [FxPresUT]; imodintro; iempintro
    ihave Hgate := trCapB_hookGate none γ r id c tl0 (CCEvOf id s c cn) true phaseBot phaseBot Λ Λ'
      iprop(emp) (phaseStepB_bot id c _ phaseBot) (fun h => by cases h) hΛ (fun h => by cases h) hok
      $$ [$Hl Hcap $Hfx]
    · simp only [trCapB]; iempintro
    iapply hookGate_mono none r (CCEvOf id s c cn)
    iframe Hgate
    iintro -
    simp only [trCapB]; iempintro
  | some γd =>
    iintro ⟨#Hl, Hcap⟩
    ihave Hcap := trCapB_bootFit (some γd) γ r id c true _ Λ $$ Hcap
    icases trCapB_pinMem γd γ r id c true _ Λ $$ Hcap with ⟨%C0, %cs0, %P0, %HΦ, Hcap⟩
    obtain ⟨⟨hidle, hfit⟩, hC0⟩ := HΦ
    ihave Hcap := trCapB_mono (some γd) γ r id c true _ (VPin C0 cs0 P0) Λ
      (fun C cs P h => ⟨h.1, h.2.1, h.2.2.1⟩) $$ Hcap
    icases trCapB_pinPerm γd γ r id c true (VPin C0 cs0 P0) Λ C0 (fun _ _ _ h => h.1) $$ Hcap
      with ⟨%Hperm, Hcap⟩
    have hcb : (C0.length : Int) ≤ uint.Z s.logst.committed := by omega
    ihave #Hsk := fxPres_skip (GF := GF) γ id (CCEvOf id s c cn) C0 cs0 P0
    ihave Hfx : FxPresUT (GF := GF) (some γd) γ id (CCEvOf id s c cn) (VPin C0 cs0 P0) (VPin C0 cs0 P0)
        iprop(emp) $$ [Hsk]
    · simp only [FxPresUT]; iapply fxPres_upd; iexact Hsk
    ihave Hgate := trCapB_hookGate (some γd) γ r id c tl0 (CCEvOf id s c cn) true (VPin C0 cs0 P0)
      (VPin C0 cs0 P0) Λ Λ' iprop(emp) (phaseStepB_applyCC id c cn s C0 cs0 P0 hidle hcb hcl)
      (fun h => by cases h) hΛ
      (fun _ e he => by
        obtain ⟨b1, b2, b3⟩ := hbnd rfl
        exact ccEvOf_ok id s c cn e _ he b1 b2 b3 (Nat.le_refl _) hcn) (fun h => by cases h) $$ [$Hl $Hcap $Hfx]
    iapply hookGate_mono (some γd) r (CCEvOf id s c cn)
    iframe Hgate
    iintro ⟨Hcap, -⟩
    iapply trCapB_mono (some γd) γ r id c true (VPin C0 cs0 P0) (fun C => SimIdle C s) Λ'
      (fun C cs P h => by obtain ⟨rfl, rfl, rfl⟩ := h; exact hidle) $$ Hcap

end gate

end EtcdGrove
end Perennial
