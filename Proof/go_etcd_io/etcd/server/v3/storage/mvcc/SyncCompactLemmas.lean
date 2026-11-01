/-
`watchableStore.syncWatchers` across a compaction (watches across a compaction, W1, 2026-11-01;
`notes/watch-compaction-plan.md`, D4/D5): what the proof needs of `choose`'s compaction responses.

* `watchNoDup_crev`: under `revMu`, the compaction revision `c` the store holds is `-1` (no
  compactor) or a revision of the committed log that writes no key twice (`rangeEvents`' premise).
* `memberRes_cmp_split`: a live member's part of `choose`'s compaction send (`cmpSendPre`), with
  the rest of its resources back for it.
* `WsState.cmpSt`: the lock's state after `choose`: the members it sent the compaction response
  marked compacted (`chooseCmp`), the unsynced group `Wu1` (without them in the group branch);
  `WsOk.cmpSt`, `WsState.settled_cmpSt`, `memberRes_cmpSt` carry the lock's facts and a member's
  resources there (a member marked compacted is behind the compaction revision, `crevLb`).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.SyncWatchersLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.WatchCmpSend

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

namespace mvcc

/-! ## The state after `choose` (pure) -/

theorem chooseCmp_lookup (Cm : GMap Loc Unit) (ST : GMap Loc WatcherSt) (w : Loc) :
    chooseCmp Cm ST !! w =
      (ST !! w).map (fun st => if (Cm !! w).isSome then { st with compacted := true } else st) :=
  gmapMapK_lookup _ _ _

/-- Two of `gmapMapK` are one. -/
theorem gmapMapK_gmapMapK {V : Type} (f g : Loc → V → V) (m : GMap Loc V) :
    gmapMapK f (gmapMapK g m) = gmapMapK (fun k x => f k (g k x)) m := by
  refine GMap.ext (fun k => ?_)
  rw [gmapMapK_lookup, gmapMapK_lookup, gmapMapK_lookup]
  cases m !! k <;> rfl

/-- A member's state after `choose`: its restore flag cleared if chosen (`D`), marked compacted if
sent the compaction response (`Cm`). -/
def chooseF (curRev : w64) (D Cm : GMap Loc Unit) (k : Loc) (st : WatcherSt) : WatcherSt :=
  if (Cm !! k).isSome then
    { (if (D !! k).isSome then rstClear curRev st else st) with compacted := true }
  else if (D !! k).isSome then rstClear curRev st else st

theorem chooseCmp_chooseRst (curRev : w64) (D Cm : GMap Loc Unit) (ST : GMap Loc WatcherSt) :
    chooseCmp Cm (chooseRst curRev D ST) = gmapMapK (chooseF curRev D Cm) ST := by
  unfold chooseCmp chooseRst; rw [gmapMapK_gmapMapK]; rfl

theorem chooseCmp_chooseRst_lookup (curRev : w64) (D Cm : GMap Loc Unit) (ST : GMap Loc WatcherSt)
    (k : Loc) : chooseCmp Cm (chooseRst curRev D ST) !! k = (ST !! k).map (chooseF curRev D Cm k) := by
  rw [chooseCmp_chooseRst, gmapMapK_lookup]

@[simp] theorem chooseF_minRev (curRev : w64) (D Cm : GMap Loc Unit) (k : Loc) (st : WatcherSt) :
    (chooseF curRev D Cm k st).minRev = st.minRev := by
  unfold chooseF; split <;> split <;> simp

@[simp] theorem chooseF_ch (curRev : w64) (D Cm : GMap Loc Unit) (k : Loc) (st : WatcherSt) :
    (chooseF curRev D Cm k st).ch = st.ch := by
  unfold chooseF; split <;> split <;> simp

@[simp] theorem chooseF_victim (curRev : w64) (D Cm : GMap Loc Unit) (k : Loc) (st : WatcherSt) :
    (chooseF curRev D Cm k st).victim = st.victim := by
  unfold chooseF; split <;> split <;> simp

theorem chooseF_compacted (curRev : w64) (D Cm : GMap Loc Unit) (k : Loc) (st : WatcherSt)
    (h : (chooseF curRev D Cm k st).compacted = true) :
    st.compacted = true ∨ (Cm !! k).isSome := by
  unfold chooseF at h
  by_cases hc : (Cm !! k).isSome
  · exact Or.inr hc
  · left; rw [if_neg hc] at h; split at h <;> simp_all

theorem chooseF_of (curRev : w64) (D Cm : GMap Loc Unit) (k : Loc) (st : WatcherSt)
    (hd : (D !! k).isSome = false) (hc : (Cm !! k).isSome = false) :
    chooseF curRev D Cm k st = st := by
  unfold chooseF; simp [hd, hc]

/-- `chooseAll`'s restore reset keeps who is live. -/
theorem chooseRst_live (σ : WsState) (c : w64) (D : GMap Loc Unit) (k : Loc) :
    ({ σ with ST := chooseRst c D σ.ST } : WsState).live k ↔ σ.live k := by
  unfold WsState.live
  have : (chooseRst c D σ.ST !! k).any (fun st => st.compacted && st.ch != null) =
      (σ.ST !! k).any (fun st => st.compacted && st.ch != null) := by
    unfold chooseRst; rw [gmapMapK_lookup]
    cases σ.ST !! k with
    | none => rfl
    | some st0 => simp only [Option.map_some, Option.any_some]; split <;> simp
  simp only [WsState.victimOf] at *
  rw [this]

/-- The lock's state after `choose`'s compaction responses: the members `Cm` marked compacted, the
unsynced group `Wu1`. -/
def WsState.cmpSt (σ : WsState) (Cm : GMap Loc Unit) (Wu1 : GMap Loc WatchRange) : WsState :=
  { σ with Wu := Wu1, ST := chooseCmp Cm σ.ST }

/-- **The lock's facts after `choose`'s compaction responses** (and who is live: the same
watchers): the members marked compacted were unsynced, so not synced and no victim; each stays in
the unsynced group, or leaves it (`Wu1`), live by its open channel. -/
theorem WsOk.cmpSt {σ : WsState} (h : WsOk σ) (Cm : GMap Loc Unit) (Wu1 : GMap Loc WatchRange)
    (hCm : ∀ w, (Cm !! w).isSome → (σ.Wu !! w).isSome)
    (hWu1 : ∀ w, Wu1 !! w = σ.Wu !! w ∨ ((Cm !! w).isSome ∧ Wu1 !! w = none)) :
    WsOk (σ.cmpSt Cm Wu1) ∧ ∀ w, (σ.cmpSt Cm Wu1).live w ↔ σ.live w := by
  have hl : ∀ w, (σ.cmpSt Cm Wu1).live w ↔ σ.live w := by
    intro w
    by_cases hc : (Cm !! w).isSome
    · have hu := hCm w hc
      have hlσ : σ.live w := Or.inr (Or.inl hu)
      refine ⟨fun _ => hlσ, fun _ => ?_⟩
      obtain ⟨st, hst⟩ := Option.isSome_iff_exists.1 (h.live_st w hlσ)
      have hch : st.ch ≠ null := fun e => ((h.st_flags w st hst).2.2.1 e) hlσ
      refine Or.inr (Or.inr (Or.inr ?_))
      show (chooseCmp Cm σ.ST !! w).any _ = true
      rw [chooseCmp_lookup, hst]; simp [hc, hch]
    · have hW : Wu1 !! w = σ.Wu !! w := (hWu1 w).resolve_right (fun h' => hc h'.1)
      have hS : chooseCmp Cm σ.ST !! w = σ.ST !! w := by
        rw [chooseCmp_lookup]; cases σ.ST !! w <;> simp [hc]
      unfold WsState.live WsState.cmpSt
      simp only
      rw [hW, hS]
      exact Iff.rfl
  have hST : ∀ w, ((σ.cmpSt Cm Wu1).ST !! w).isSome = (σ.ST !! w).isSome := by
    intro w; show (chooseCmp Cm σ.ST !! w).isSome = _
    rw [chooseCmp_lookup]; cases σ.ST !! w <;> rfl
  have hWuS : ∀ w, (Wu1 !! w).isSome → (σ.Wu !! w).isSome := by
    intro w hw; rcases hWu1 w with e | ⟨-, e⟩
    · rwa [e] at hw
    · rw [e] at hw; cases hw
  refine ⟨⟨fun w hw => ?_, h.ws_v, fun w hw => h.wu_v w (hWuS w hw), h.v_one,
    fun w hw => by rw [hST]; exact h.live_st w ((hl w).1 hw), fun w => by rw [hl]; exact h.live_e w,
    fun w hw => by rw [hST] at hw; exact h.st_m w hw, h.wo_m, fun w hw => by rw [hST]; exact h.m_st w hw,
    fun w hw => ?_, fun w hw => by rw [hl]; exact h.wo_live w hw, fun w st hs => ?_, h.wo_flags,
    h.synced_d⟩, hl⟩
  · show Wu1 !! w = none
    rcases hWu1 w with e | ⟨-, e⟩
    · rw [e]; exact h.ws_wu w hw
    · exact e
  · show chooseCmp Cm σ.ST !! w = none
    rw [chooseCmp_lookup, h.wo_st w hw]; rfl
  · have hs' : chooseCmp Cm σ.ST !! w = some st := hs
    rw [chooseCmp_lookup] at hs'
    cases h0 : σ.ST !! w with
    | none => rw [h0] at hs'; cases hs'
    | some st0 =>
      rw [h0] at hs'; simp only [Option.map_some, Option.some.injEq] at hs'
      obtain ⟨f1, f2, f3⟩ := h.st_flags w st0 h0
      have e2 : st.victim = st0.victim := by rw [← hs']; split <;> rfl
      have e3 : st.ch = st0.ch := by rw [← hs']; split <;> rfl
      refine ⟨fun hc => ?_, fun hlv => by rw [e2]; exact f2 ((hl w).1 hlv), by rw [e3, hl]; exact f3⟩
      by_cases hcm : (Cm !! w).isSome
      · have hu := hCm w hcm
        refine ⟨?_, h.wu_v w hu⟩
        show σ.Ws !! w = none
        cases hws : σ.Ws !! w with
        | none => rfl
        | some _ => have := h.ws_wu w (by rw [hws]; rfl); rw [this] at hu; cases hu
      · have e1 : st = st0 := by rw [← hs']; simp [hcm]
        subst e1; exact f1 hc

/-- Settled after `choose`'s compaction responses (no `minRev` changes). -/
theorem WsState.settled_cmpSt {σ : WsState} (h : σ.settled) (Cm : GMap Loc Unit)
    (Wu1 : GMap Loc WatchRange) : (σ.cmpSt Cm Wu1).settled := by
  refine ⟨h.1, fun k st h1 hst => ?_, h.2.2⟩
  have hs' : chooseCmp Cm σ.ST !! k = some st := hst
  rw [chooseCmp_lookup] at hs'
  cases h0 : σ.ST !! k with
  | none => rw [h0] at hs'; cases hs'
  | some st0 =>
    rw [h0] at hs'; simp only [Option.map_some, Option.some.injEq] at hs'
    have e : st.minRev = st0.minRev := by rw [← hs']; split <;> rfl
    rw [e]; exact h.2.1 k st0 h1 h0

/-- A lower bound of `minRevOf` by one of every member's. -/
theorem minRevOf_ge (ST : GMap Loc WatcherSt) (S : GMap Loc Unit) (b : Int)
    (hb0 : b ≤ 2 ^ 63 - 1)
    (hb : ∀ w st, (S !! w).isSome → ST !! w = some st → b ≤ sint.Z st.minRev) :
    b ≤ minRevOf ST S := by
  unfold minRevOf minRevL
  refine sw_minRevFold_ge ST b _ _ ?_ (fun w hw st hs => hb w st ?_ hs)
  · show b ≤ sint.Z (W64 (2 ^ 63 - 1) : w64)
    rw [show sint.Z (W64 (2 ^ 63 - 1) : w64) = 2 ^ 63 - 1 by decide]; exact hb0
  · rwa [← GMap.mem_dom_list]

/-- **A member skipped** (`syncWatchers`' `continue` for a watcher behind the compaction revision:
its compaction response not sent): the loop state unchanged, the member processed. -/
theorem SyncLoop.skip {σ : WsState} {ST0 : GMap Loc WatcherSt} {v : SyncVars}
    {PB PBv PBr : GMap Loc (Loc × EventBatch)} {keys : List Loc} {i : Nat}
    (h : SyncLoop σ ST0 v PB PBv PBr keys i) {key : Loc} (hkey : keys[i]? = some key)
    (hu : ∀ st, (v.Wu !! key).isSome → v.ST !! key = some st → sint.Z st.minRev < σ.Lmu.length) :
    SyncLoop σ ST0 v PB PBv PBr keys (i + 1) := by
  refine ⟨h.ok, h.bv, fun k hk => ?_, h.set, fun k st hk hwu hst => ?_⟩
  · rw [mem_take_succ_iff hkey] at hk
    exact h.rest k (fun e => hk (Or.inl e))
  · rw [mem_take_succ_iff hkey] at hk
    by_cases hk1 : k = key
    · subst hk1; exact hu st hwu hst
    · exact h.uns k st (hk.resolve_right hk1) hwu hst

end mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

namespace mvcc

/-- **The compaction revision under `revMu`** (with the create token's `watchNoDup`): `-1`, the
store never compacting, or a revision of the committed log `log` that writes no key twice. -/
theorem watchNoDup_crev (γ : StoreNames) (q : Qp) (c : Int) (log : Log) (hc : -1 ≤ c) :
    ⊢ watchNoDup (GF := GF) γ -∗ crevUB γ.idx q c -∗ idxCert γ.idx log -∗ certOk γ log ={⊤}=∗
      crevUB γ.idx q c ∗ ⌜c = -1 ∨ oneChangePerKeyAt log c⌝ := by
  iintro #Hn Hc #Hcert #Hok
  iunfold watchNoDup at Hn
  icases Hn with (#Hf | #Hd)
  · ihave #Hf' := noCompactor_frozen γ $$ Hf
    imod crevFrozen_agree γ q c hc $$ Hf' Hc with ⟨Hc, %h⟩
    imodintro; iframe Hc; ipureintro; exact Or.inl h
  · iunfold noDupKeys at Hd
    ihave #Hs := idxCert_sealed γ.idx log $$ Hcert
    ihave #He : evLog γ log $$ []
    · iunfold evLog; iframe Hs Hok
    ihave Hd' := Hd $$ %log He
    imod Hd' with %h
    imodintro; iframe Hc; ipureintro; exact Or.inr (h c)

/-- **A live member's part of `choose`'s compaction send** (`cmpSendPre` at its liveness half,
if it is behind `c`), and the rest of its resources back for it. -/
theorem memberRes_cmp_split (γ : WsNames) (σ : WsState) (w : Loc) (st : WatcherSt) (c : w64)
    (hl : σ.live w) :
    memberRes (GF := GF) γ 1 σ w st ⊢
      (if decide (sint.Z st.minRev < sint.Z c) then cmpSendPre γ w st.ch (1 : Qp).half
        else iprop(True)) ∗
      ((if decide (sint.Z st.minRev < sint.Z c) then cmpSendPre γ w st.ch (1 : Qp).half
        else iprop(True)) -∗ memberRes γ 1 σ w st) := by
  by_cases hd : sint.Z st.minRev < sint.Z c
  · rw [decide_eq_true hd]
    simp only [↓reduceIte]
    unfold memberRes
    simp only [hl, ↓reduceIte]
    iintro ⟨%γw, %r, %fcs, %hM, #Hm, #Hf, #Hc, #Hfo, %Hsr, %evsw, %d, %hE, Ha, Hl, #Hp⟩
    isplitl [Hl]
    · iunfold cmpSendPre; iexists γw, r, fcs; iframe Hm Hf Hfo Hc Hl
    iintro Hpre
    iunfold cmpSendPre at Hpre
    icases Hpre with ⟨%γw', %r', %fcs', #Hm', -, -, -, Hl'⟩
    ihave #HmA := Hm
    ihave #HmB := Hm'
    iunfold watcherMeta at HmA HmB
    ihave %Heq := ghostMapElem_agree $$ HmA HmB
    subst Heq
    iexists γw, r, fcs
    iframe Hm Hf Hc Hfo
    isplitr
    · ipureintro; exact hM
    isplitr
    · ipureintro; exact Hsr
    iexists evsw, d
    iframe Ha Hl' Hp
    ipureintro; exact hE
  · rw [decide_eq_false hd]
    simp only [Bool.false_eq_true, ↓reduceIte]
    iintro H
    isplitl []
    · itrivial
    iintro -
    iexact H

/-- **An unsynced member marked compacted is behind the compaction revision** (`cQ`, the store's
under `revMu`): its `crevLb` is below it. -/
theorem sw_unsynced_cmp (γ : WsNames) (σ : WsState) (hok : WsOk σ) (q : Qp) (cQ : Int)
    (hcQ : -1 ≤ cQ) :
    ([∗map] w ↦ st ∈ σ.ST, memberRes (GF := GF) γ 1 σ w st) ∗ crevUB γ.st.idx q cQ ⊢
      ⌜∀ w st, σ.ST !! w = some st → (σ.Wu !! w).isSome → st.compacted = true →
        sint.Z st.minRev < cQ⌝ := by
  iintro ⟨Hmem, Hc⟩
  iapply pure_forall.2; iintro %w
  iapply pure_forall.2; iintro %st
  by_cases hst : σ.ST !! w = some st
  rotate_left
  · ipureintro; intro h; exact absurd h hst
  by_cases hu : (σ.Wu !! w).isSome
  rotate_left
  · ipureintro; intro _ h; exact absurd h hu
  by_cases hcp : st.compacted = true
  rotate_left
  · ipureintro; intro _ _ h; exact absurd h hcp
  have hws : σ.Ws !! w = none := by
    cases h : σ.Ws !! w with
    | none => rfl
    | some _ => have := hok.ws_wu w (by rw [h]; rfl); rw [this] at hu; cases hu
  icases (BigSepM.bigSepM_lookup_acc hst).1 $$ Hmem with ⟨Hw, -⟩
  icases sw_memberRes_unsynced γ 1 σ w st hws hu $$ Hw with
    ⟨%γw, %r, %fcs, %evsw, %hM, -, -, -, -, -, -, -, -, -, -, -, #Hcmp⟩
  icases Hcmp $$ %hcp with ⟨%c0, #Hlb, %Hlt⟩
  icases crevUB_lb_keep _ _ _ _ hcQ $$ [$Hc $Hlb] with ⟨-, %Hle⟩
  ipureintro
  intro _ _ _
  omega

/-- **An unsynced member's resources in the state after `choose`** (`σ1`, its state `st1`): the
same `minRev` and channel; kept unsynced or out of the groups (live by its open channel); marked
compacted only if it was or is behind `c0`, a compaction revision. -/
theorem memberRes_cmpSt (γ : WsNames) (σ σ1 : WsState) (w : Loc) (st st1 : WatcherSt) (c0 : Int)
    (hM : σ1.M = σ.M) (hE : σ1.E !! w = σ.E !! w) (hWs : σ1.Ws !! w = σ.Ws !! w)
    (hV : σ1.victimOf w = σ.victimOf w) (hWs0 : σ.Ws !! w = none) (hWu : (σ.Wu !! w).isSome)
    (hv0 : σ.victimOf w = none) (hl1 : σ1.live w)
    (hmin : st1.minRev = st.minRev) (hch : st1.ch = st.ch)
    (hcmp : st1.compacted = true → st.compacted = true ∨ sint.Z st.minRev < c0) :
    memberRes (GF := GF) γ 1 σ w st ∗ crevLb γ.st.idx c0 ⊢ memberRes γ 1 σ1 w st1 := by
  have hl : σ.live w := Or.inr (Or.inl hWu)
  have hWs1 : (σ1.Ws !! w).isSome = false := by rw [hWs, hWs0]; rfl
  unfold memberRes
  simp only [hl, hl1, ↓reduceIte, hM]
  iintro ⟨⟨%γw, %r, %fcs, %hMw, #Hm, #Hf, #Hc, #Hfo, %Hsr, %evsw, %d, %hEw, Ha, Hl, #Hp⟩, #Hlb⟩
  irevert Hp
  rw [sw_popFacts_unsynced γ σ w r γw.lo st evsw d (by rw [hWs0]; rfl) hWu]
  iintro ⟨%Hp1, #Hwf, #Hlc, #Hcm⟩
  iexists γw, r, fcs
  iframe Hm Hf
  isplitr
  · ipureintro; exact hMw
  rw [hch]
  iframe Hc Hfo
  isplitr
  · ipureintro; exact Hsr
  iexists evsw, d
  isplitr
  · ipureintro; rw [hE]; exact hEw
  iframe Ha Hl
  cases hu1 : (σ1.Wu !! w).isSome
  · unfold popFacts
    simp only [hWs1, hu1, Bool.false_eq_true, ↓reduceIte, hV, hv0]
    itrivial
  · rw [sw_popFacts_unsynced γ σ1 w _ _ st1 _ _ hWs1 hu1, hmin]
    iframe Hwf Hlc
    isplitr
    · ipureintro; exact Hp1
    iintro %hc
    rcases hcmp hc with h | h
    · iapply Hcm; ipureintro; exact h
    · iexists c0; iframe Hlb; ipureintro; exact h

end mvcc

end proof

end EtcdGrove
end Perennial
