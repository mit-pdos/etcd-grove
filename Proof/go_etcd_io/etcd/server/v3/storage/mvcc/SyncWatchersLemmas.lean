/-
`watchableStore.syncWatchers`' loop state (pure) and the lock invariant's parts across it.
Lean-first; see `watchableStore__syncWatchers.lean`.

**The loop's state** (`SyncVars`): the lock's state `σ` with its synced and unsynced members,
states and deliveries as the loop changes them, and the loop's local victims (`Bv`) as a pending
batch after `σ`'s victims (`SyncVars.st`). One step (`SyncVars.step`) moves one unsynced member:
synced, kept unsynced (a capped batch), or a victim with its batch. The lock's pure facts hold of
every loop state (`WsOk.sync_step`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchSync

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

/-! ## The loop's state -/

/-- The loop's state: populations, states, deliveries and the local victims. -/
structure SyncVars where
  Ws : GMap Loc WatchRange
  Wu : GMap Loc WatchRange
  ST : GMap Loc WatcherSt
  E : GMap Loc (List EvM × Nat)
  Bv : GMap Loc EventBatch

/-- The lock's state of a loop state: the local victims a pending batch. -/
def SyncVars.st (σ : WsState) (v : SyncVars) : WsState :=
  { σ with Ws := v.Ws, Wu := v.Wu, ST := v.ST, E := v.E, VB := σ.VB ++ [v.Bv] }

/-- Where a step moves its member. -/
inductive SyncDst where
  | synced
  | unsynced
  | victim (B : EventBatch)

def SyncDst.isVictim : SyncDst → Bool
  | .victim _ => true
  | _ => false

/-- One step: the unsynced member `w` (range `r`) moved to `dst`, with state `st'` and delivery
`e'`. -/
def SyncVars.step (v : SyncVars) (w : Loc) (r : WatchRange) (dst : SyncDst) (st' : WatcherSt)
    (e' : List EvM × Nat) : SyncVars :=
  match dst with
  | .synced => ⟨<[w := r]> v.Ws, GMap.delete w v.Wu, <[w := st']> v.ST, <[w := e']> v.E, v.Bv⟩
  | .unsynced => ⟨v.Ws, v.Wu, <[w := st']> v.ST, <[w := e']> v.E, v.Bv⟩
  | .victim B => ⟨v.Ws, GMap.delete w v.Wu, <[w := st']> v.ST, <[w := e']> v.E, <[w := B]> v.Bv⟩

section lemmas
variable (σ : WsState) (v : SyncVars)

theorem SyncVars.st_Ws : (v.st σ).Ws = v.Ws := rfl
theorem SyncVars.st_Wu : (v.st σ).Wu = v.Wu := rfl
theorem SyncVars.st_ST : (v.st σ).ST = v.ST := rfl
theorem SyncVars.st_E : (v.st σ).E = v.E := rfl
theorem SyncVars.st_M : (v.st σ).M = σ.M := rfl
theorem SyncVars.st_Wo : (v.st σ).Wo = σ.Wo := rfl
theorem SyncVars.st_Lmu : (v.st σ).Lmu = σ.Lmu := rfl
theorem SyncVars.st_VB : (v.st σ).VB = σ.VB ++ [v.Bv] := rfl

theorem SyncVars.st_victimOf (k : Loc) :
    (v.st σ).victimOf k = (σ.victimOf k).or (v.Bv !! k) := by
  unfold WsState.victimOf
  rw [SyncVars.st_VB, List.findSome?_append]
  simp

end lemmas

/-- The pure facts of a state from another's, with the same populations, states, names and
deliveries, the same victims' batches seen by each watcher, and one victim batch per watcher. -/
theorem WsOk.congr {σ σ' : WsState} (h : WsOk σ) (hWs : σ'.Ws = σ.Ws) (hWu : σ'.Wu = σ.Wu)
    (hST : σ'.ST = σ.ST) (hWo : σ'.Wo = σ.Wo) (hM : σ'.M = σ.M) (hE : σ'.E = σ.E)
    (hLmu : σ'.Lmu = σ.Lmu) (hvo : ∀ k, σ'.victimOf k = σ.victimOf k)
    (hv1 : ∀ (i j : Nat) (B B' : GMap Loc EventBatch) (w : Loc), σ'.VB[i]? = some B →
      σ'.VB[j]? = some B' → (B !! w).isSome → (B' !! w).isSome → i = j) : WsOk σ' := by
  have hl : ∀ k, σ'.live k ↔ σ.live k := by
    intro k; unfold WsState.live; rw [hWs, hWu, hvo]
  constructor
  · rw [hWs, hWu]; exact h.ws_wu
  · intro w hw; rw [hvo]; rw [hWs] at hw; exact h.ws_v w hw
  · intro w hw; rw [hvo]; rw [hWu] at hw; exact h.wu_v w hw
  · exact hv1
  · intro w hw; rw [hST]; exact h.live_st w ((hl w).1 hw)
  · intro w; rw [hE, hl]; exact h.live_e w
  · rw [hST, hM]; exact h.st_m
  · rw [hWo, hM]; exact h.wo_m
  · rw [hST, hWo, hM]; exact h.m_st
  · rw [hST, hWo]; exact h.wo_st
  · intro w hw; rw [hl]; rw [hWo] at hw; exact h.wo_live w hw
  · intro w st hst
    rw [hST] at hst
    obtain ⟨h1, h2, h3, h4⟩ := h.st_flags w st hst
    refine ⟨h1, h2, fun hlv => ?_, ?_⟩
    · rw [hvo]; exact h3 ((hl w).1 hlv)
    · rw [hl]; exact h4
  · rw [hWo]; exact h.wo_flags
  · intro w γw ed hw hm he
    rw [hWs] at hw; rw [hM] at hm; rw [hE] at he; rw [hLmu]
    exact h.synced_d w γw ed hw hm he

/-- The loop's initial state: `σ` with no local victim. -/
def SyncVars.init (σ : WsState) : SyncVars := ⟨σ.Ws, σ.Wu, σ.ST, σ.E, ∅⟩

theorem WsOk.sync_init {σ : WsState} (h : WsOk σ) : WsOk ((SyncVars.init σ).st σ) := by
  refine h.congr rfl rfl rfl rfl rfl rfl rfl (fun k => ?_) ?_
  · rw [SyncVars.st_victimOf]; simp [SyncVars.init]
  · intro i j B B' w hi hj hB hB'
    rw [SyncVars.st_VB] at hi hj
    have hlt : ∀ {n : Nat} {B0 : GMap Loc EventBatch},
        (σ.VB ++ [(SyncVars.init σ).Bv])[n]? = some B0 → (B0 !! w).isSome →
        σ.VB[n]? = some B0 := by
      intro n B0 hn hb
      by_cases hn' : n < σ.VB.length
      · rwa [List.getElem?_append_left hn'] at hn
      · rw [List.getElem?_append_right (by omega)] at hn
        have : n - σ.VB.length = 0 := by
          have := (List.getElem?_eq_some_iff.1 hn).1; simp at this; omega
        rw [this] at hn; simp [SyncVars.init] at hn; subst hn; simp at hb
    exact h.v_one i j B B' w (hlt hi hB) (hlt hj hB') hB hB'

/-- The loop's final state with no local victim: `σ`'s victims. -/
theorem WsOk.sync_final_empty {σ : WsState} {v : SyncVars} (h : WsOk (v.st σ)) (hBv : v.Bv = ∅)
    (σ' : WsState) (hWs : σ'.Ws = v.Ws) (hWu : σ'.Wu = v.Wu) (hST : σ'.ST = v.ST)
    (hWo : σ'.Wo = σ.Wo) (hM : σ'.M = σ.M) (hE : σ'.E = v.E) (hLmu : σ'.Lmu = σ.Lmu)
    (hVB : σ'.VB = σ.VB) : WsOk σ' := by
  refine h.congr hWs hWu hST hWo hM hE hLmu (fun k => ?_) ?_
  · rw [SyncVars.st_victimOf, hBv]; unfold WsState.victimOf; rw [hVB]; simp
  · intro i j B B' w hi hj hB hB'
    rw [hVB] at hi hj
    have hi' : (v.st σ).VB[i]? = some B := by
      rw [SyncVars.st_VB, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hi).1]; exact hi
    have hj' : (v.st σ).VB[j]? = some B' := by
      rw [SyncVars.st_VB, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hj).1]; exact hj
    exact h.v_one i j B B' w hi' hj' hB hB'

theorem findSome_isSome_of_mem' {B : GMap Loc EventBatch} {l : List (GMap Loc EventBatch)}
    {w : Loc} (hB : B ∈ l) (hw : (B !! w).isSome) : (l.findSome? (· !! w)).isSome := by
  induction l with
  | nil => cases hB
  | cons x xs ih =>
    rw [List.findSome?_cons]
    rcases List.mem_cons.1 hB with rfl | h
    · cases h' : B !! w with
      | none => rw [h'] at hw; cases hw
      | some _ => simp
    · cases h' : x !! w with
      | none => exact ih h
      | some _ => simp

/-- The lock's facts after one step of the loop. -/
theorem WsOk.sync_step {σ : WsState} {v : SyncVars} (h : WsOk (v.st σ)) {w : Loc} {r : WatchRange}
    {st : WatcherSt} (hWu : v.Wu !! w = some r) (hST : v.ST !! w = some st) (dst : SyncDst)
    (st' : WatcherSt) (e' : List EvM × Nat)
    (hst' : st'.compacted = false ∧ st'.restore = false ∧ st'.ch = st.ch ∧
      st'.victim = dst.isVictim)
    (hd : dst = .synced → ∀ γw, σ.M !! w = some γw → max γw.lo σ.Lmu.length ≤ e'.2) :
    WsOk ((v.step w r dst st' e').st σ) := by
  generalize hS' : (v.step w r dst st' e').st σ = S'
  generalize hS : v.st σ = S at h
  have hWuS : S.Wu !! w = some r := by rw [← hS]; exact hWu
  have hSTS : S.ST !! w = some st := by rw [← hS]; exact hST
  have hwsN : S.Ws !! w = none := by
    cases h1 : S.Ws !! w with
    | none => rfl
    | some _ => have := h.ws_wu w (by rw [h1]; rfl); rw [hWuS] at this; cases this
  have hvN : S.victimOf w = none := h.wu_v w (by rw [hWuS]; rfl)
  have hσvN : σ.victimOf w = none ∧ v.Bv !! w = none := by
    have := hvN; rw [← hS, SyncVars.st_victimOf] at this
    cases h1 : σ.victimOf w <;> cases h2 : v.Bv !! w <;> simp_all
  have hliveS : S.live w := Or.inr (Or.inl (by rw [hWuS]; rfl))
  have hflags := h.st_flags w st hSTS
  have hchnn : st.ch ≠ null := fun he => (hflags.2.2.2.1 he) hliveS
  -- the step off `w`, and at `w`
  have hoff : ∀ k, k ≠ w → S'.Ws !! k = S.Ws !! k ∧ S'.Wu !! k = S.Wu !! k ∧
      S'.ST !! k = S.ST !! k ∧ S'.E !! k = S.E !! k ∧ S'.victimOf k = S.victimOf k := by
    intro k hk
    have hk' : w ≠ k := Ne.symm hk
    rw [← hS', ← hS, SyncVars.st_victimOf, SyncVars.st_victimOf]
    cases dst <;>
      simp [SyncVars.step, SyncVars.st, GMap.lookup_insert_ne _ _ hk', GMap.lookup_delete_ne _ hk', hk']
  have hSTw : S'.ST !! w = some st' := by
    rw [← hS']; cases dst <;> simp [SyncVars.step, SyncVars.st, GMap.lookup_insert]
  have hEw : S'.E !! w = some e' := by
    rw [← hS']; cases dst <;> simp [SyncVars.step, SyncVars.st, GMap.lookup_insert]
  have hpop : (dst = .synced → S'.Ws !! w = some r ∧ S'.Wu !! w = none ∧ S'.victimOf w = none) ∧
      (dst = .unsynced → S'.Ws !! w = none ∧ S'.Wu !! w = some r ∧ S'.victimOf w = none) ∧
      (∀ B, dst = .victim B → S'.Ws !! w = none ∧ S'.Wu !! w = none ∧
        S'.victimOf w = some B) := by
    have hWs0 : v.Ws !! w = none := by have := hwsN; rw [← hS] at this; exact this
    refine ⟨fun hd => ?_, fun hd => ?_, fun B hd => ?_⟩ <;> subst hd <;>
      rw [← hS', SyncVars.st_victimOf] <;>
      simp [SyncVars.step, SyncVars.st, GMap.lookup_insert, GMap.lookup_delete, hσvN.1, hσvN.2,
        hWs0, hWu]
  have hlivew : S'.live w := by
    unfold WsState.live
    cases dst with
    | synced => exact Or.inl (by rw [(hpop.1 rfl).1]; rfl)
    | unsynced => exact Or.inr (Or.inl (by rw [(hpop.2.1 rfl).2.1]; rfl))
    | victim B => exact Or.inr (Or.inr (by rw [(hpop.2.2 B rfl).2.2]; rfl))
  have hlive : ∀ k, S'.live k ↔ S.live k := by
    intro k
    by_cases hk : k = w
    · subst hk; exact ⟨fun _ => hliveS, fun _ => hlivew⟩
    · obtain ⟨h1, h2, -, -, h5⟩ := hoff k hk
      unfold WsState.live; rw [h1, h2, h5]
  have hM : S'.M = S.M := by rw [← hS, ← hS']; rfl
  have hWo : S'.Wo = S.Wo := by rw [← hS, ← hS']; rfl
  have hLmu : S'.Lmu = S.Lmu := by rw [← hS, ← hS']; rfl
  -- the populations at `w`: exactly one
  have hone : ((S'.Ws !! w).isSome → S'.Wu !! w = none ∧ S'.victimOf w = none) ∧
      ((S'.Wu !! w).isSome → S'.victimOf w = none) := by
    cases dst with
    | synced => obtain ⟨_, h2, h3⟩ := hpop.1 rfl; exact ⟨fun _ => ⟨h2, h3⟩, fun _ => h3⟩
    | unsynced =>
      obtain ⟨h1, _, h3⟩ := hpop.2.1 rfl
      exact ⟨(fun hh => by rw [h1] at hh; cases hh), fun _ => h3⟩
    | victim B =>
      obtain ⟨h1, h2, _⟩ := hpop.2.2 B rfl
      exact ⟨(fun hh => by rw [h1] at hh; cases hh), (fun hh => by rw [h2] at hh; cases hh)⟩
  constructor
  · intro k hk
    by_cases hkw : k = w
    · subst hkw; exact (hone.1 hk).1
    · obtain ⟨h1, h2, -⟩ := hoff k hkw; rw [h2]; rw [h1] at hk; exact h.ws_wu k hk
  · intro k hk
    by_cases hkw : k = w
    · subst hkw; exact (hone.1 hk).2
    · obtain ⟨h1, -, -, -, h5⟩ := hoff k hkw; rw [h5]; rw [h1] at hk; exact h.ws_v k hk
  · intro k hk
    by_cases hkw : k = w
    · subst hkw; exact hone.2 hk
    · obtain ⟨-, h2, -, -, h5⟩ := hoff k hkw; rw [h5]; rw [h2] at hk; exact h.wu_v k hk
  · -- one batch per victim
    intro i j B B' k hi hj hB hB'
    have hVB : S'.VB = σ.VB ++ [(v.step w r dst st' e').Bv] := by rw [← hS']; rfl
    have hBv' : ∀ k', k' ≠ w → (v.step w r dst st' e').Bv !! k' = v.Bv !! k' := by
      intro k' hk'; cases dst <;> simp [SyncVars.step, GMap.lookup_insert_ne _ _ (Ne.symm hk'), Ne.symm hk']
    -- every batch of `S'` with `k` is one of `S` with `k`, unless `k = w` (only in the last)
    by_cases hkw : k = w
    · subst hkw
      -- `w` is in no batch of `σ`
      have hnot : ∀ (n : Nat) (B0 : GMap Loc EventBatch), σ.VB[n]? = some B0 → (B0 !! k).isSome → False := by
        intro n B0 hn hb
        have := findSome_isSome_of_mem' (List.mem_of_getElem? hn) hb
        unfold WsState.victimOf at hσvN
        rw [hσvN.1] at this; cases this
      have hlast : ∀ (n : Nat) (B0 : GMap Loc EventBatch), S'.VB[n]? = some B0 → (B0 !! k).isSome → n = σ.VB.length := by
        intro n B0 hn hb
        rw [hVB] at hn
        by_cases hn' : n < σ.VB.length
        · rw [List.getElem?_append_left hn'] at hn; exact (hnot n B0 hn hb).elim
        · have := (List.getElem?_eq_some_iff.1 hn).1; simp at this; omega
      rw [hlast i B hi hB, hlast j B' hj hB']
    · have hconv : ∀ (n : Nat) (B0 : GMap Loc EventBatch), S'.VB[n]? = some B0 → (B0 !! k).isSome →
          ∃ B1 : GMap Loc EventBatch, S.VB[n]? = some B1 ∧ (B1 !! k).isSome := by
        intro n B0 hn hb
        rw [hVB] at hn
        by_cases hn' : n < σ.VB.length
        · rw [List.getElem?_append_left hn'] at hn
          exact ⟨B0, by rw [← hS, SyncVars.st_VB, List.getElem?_append_left hn']; exact hn, hb⟩
        · rw [List.getElem?_append_right (by omega)] at hn
          have h0 : n - σ.VB.length = 0 := by
            have := (List.getElem?_eq_some_iff.1 hn).1; simp at this; omega
          rw [h0] at hn; simp at hn; subst hn
          refine ⟨v.Bv, ?_, by rw [← hBv' k hkw]; exact hb⟩
          rw [← hS, SyncVars.st_VB, List.getElem?_append_right (by omega),
            show n - σ.VB.length = 0 from h0]
          rfl
      obtain ⟨B1, hi1, hb1⟩ := hconv i B hi hB
      obtain ⟨B2, hj2, hb2⟩ := hconv j B' hj hB'
      exact h.v_one i j B1 B2 k hi1 hj2 hb1 hb2
  · intro k hk
    by_cases hkw : k = w
    · subst hkw; rw [hSTw]; rfl
    · obtain ⟨-, -, h3, -⟩ := hoff k hkw; rw [h3]; exact h.live_st k ((hlive k).1 hk)
  · intro k
    by_cases hkw : k = w
    · subst hkw; rw [hEw]; simp [hlivew]
    · obtain ⟨-, -, -, h4, -⟩ := hoff k hkw; rw [h4, hlive]; exact h.live_e k
  · intro k hk
    by_cases hkw : k = w
    · subst hkw; rw [hM]; exact h.st_m k (by rw [hSTS]; rfl)
    · obtain ⟨-, -, h3, -⟩ := hoff k hkw; rw [h3] at hk; rw [hM]; exact h.st_m k hk
  · intro k hk; rw [hM]; rw [hWo] at hk; exact h.wo_m k hk
  · intro k hk
    by_cases hkw : k = w
    · subst hkw; exact Or.inl (by rw [hSTw]; rfl)
    · obtain ⟨-, -, h3, -⟩ := hoff k hkw; rw [h3, hWo]; rw [hM] at hk; exact h.m_st k hk
  · intro k hk
    by_cases hkw : k = w
    · subst hkw
      rw [hWo] at hk
      have := h.wo_st k hk; rw [hSTS] at this; cases this
    · obtain ⟨-, -, h3, -⟩ := hoff k hkw; rw [h3]; rw [hWo] at hk; exact h.wo_st k hk
  · intro k hk
    rw [hlive]; rw [hWo] at hk; exact h.wo_live k hk
  · intro k st0 hst0
    by_cases hkw : k = w
    · subst hkw
      rw [hSTw] at hst0; cases hst0
      obtain ⟨h1, h2, h3, h4⟩ := hst'
      refine ⟨h1, h2, fun _ => ?_, ?_⟩
      · rw [h4]
        cases dst with
        | synced => rw [(hpop.1 rfl).2.2]; simp [SyncDst.isVictim]
        | unsynced => rw [(hpop.2.1 rfl).2.2]; simp [SyncDst.isVictim]
        | victim B => rw [(hpop.2.2 B rfl).2.2]; simp [SyncDst.isVictim]
      · rw [h3]; exact ⟨fun he => absurd he hchnn, fun hn => absurd hlivew hn⟩
    · obtain ⟨-, -, h3, -, h5⟩ := hoff k hkw
      rw [h3] at hst0
      obtain ⟨g1, g2, g3, g4⟩ := h.st_flags k st0 hst0
      refine ⟨g1, g2, fun hl => ?_, ?_⟩
      · rw [h5]; exact g3 ((hlive k).1 hl)
      · rw [hlive]; exact g4
  · intro k st0 h0; rw [hWo] at h0; exact h.wo_flags k st0 h0
  · intro k γw ed hk hm he
    rw [hM] at hm
    by_cases hkw : k = w
    · subst hkw
      cases dst with
      | synced =>
        rw [hEw] at he; cases he
        have : S'.Lmu = σ.Lmu := by rw [← hS']; rfl
        rw [this]; rw [← hS] at hm; exact hd rfl γw hm
      | unsynced => rw [(hpop.2.1 rfl).1] at hk; cases hk
      | victim B => rw [(hpop.2.2 B rfl).1] at hk; cases hk
    · obtain ⟨h1, -, -, h4, -⟩ := hoff k hkw
      rw [h1] at hk; rw [h4] at he; rw [hLmu]
      exact h.synced_d k γw ed hk hm he

/-- `syncWatchers`' loop invariant (pure part), before the `i`-th key of `keys`: the lock's facts of
the loop state, the local victims' batches `PBv`, and the members not processed yet untouched
(their batches `PB` still in the remaining ones `PBr`). -/
structure SyncLoop (σ : WsState) (v : SyncVars) (PB PBv PBr : GMap Loc (Loc × EventBatch))
    (keys : List Loc) (i : Nat) : Prop where
  ok : WsOk (v.st σ)
  bv : v.Bv = GMap.fmap Prod.snd PBv
  rest : ∀ k, k ∉ keys.take i → v.ST !! k = σ.ST !! k ∧ v.Wu !! k = σ.Wu !! k ∧
    v.Ws !! k = σ.Ws !! k ∧ v.E !! k = σ.E !! k ∧ v.Bv !! k = none ∧ PBr !! k = PB !! k

theorem sw_not_mem_take (keys : List Loc) (hnd : keys.Nodup) (i : Nat) (key : Loc)
    (hkey : keys[i]? = some key) : key ∉ keys.take i := by
  intro hm
  obtain ⟨j, hj, hjk⟩ := List.getElem_of_mem hm
  rw [List.getElem_take] at hjk
  have hj' : keys[j]? = some key := by
    rw [List.getElem?_eq_getElem (by simp at hj; omega)]; exact congrArg some hjk
  have := list_nodup_getElem?_inj keys hnd j i key hj' hkey
  simp at hj; omega

theorem sw_take_succ (keys : List Loc) (i : Nat) (key : Loc) (hkey : keys[i]? = some key) (k : Loc) :
    k ∈ keys.take (i + 1) ↔ k ∈ keys.take i ∨ k = key := by
  rw [List.take_add_one, hkey]; simp

theorem SyncVars.step_ne (v : SyncVars) (w : Loc) (r : WatchRange) (dst : SyncDst)
    (st' : WatcherSt) (e' : List EvM × Nat) (k : Loc) (hk : k ≠ w) :
    (v.step w r dst st' e').ST !! k = v.ST !! k ∧ (v.step w r dst st' e').Wu !! k = v.Wu !! k ∧
    (v.step w r dst st' e').Ws !! k = v.Ws !! k ∧ (v.step w r dst st' e').E !! k = v.E !! k ∧
    (v.step w r dst st' e').Bv !! k = v.Bv !! k := by
  have hk' : w ≠ k := Ne.symm hk
  cases dst <;> simp [SyncVars.step, GMap.lookup_insert_ne _ _ hk', GMap.lookup_delete_ne _ hk', hk']

theorem SyncVars.step_ST (v : SyncVars) (w : Loc) (r : WatchRange) (dst : SyncDst)
    (st' : WatcherSt) (e' : List EvM × Nat) :
    (v.step w r dst st' e').ST = <[w := st']> v.ST := by cases dst <;> rfl

theorem SyncVars.step_E (v : SyncVars) (w : Loc) (r : WatchRange) (dst : SyncDst)
    (st' : WatcherSt) (e' : List EvM × Nat) :
    (v.step w r dst st' e').E = <[w := e']> v.E := by cases dst <;> rfl

theorem SyncLoop.step {σ : WsState} {v : SyncVars} {PB PBv PBr : GMap Loc (Loc × EventBatch)}
    {keys : List Loc} {i : Nat} (h : SyncLoop σ v PB PBv PBr keys i) {key : Loc}
    (hkey : keys[i]? = some key) (r : WatchRange) (dst : SyncDst) (st' : WatcherSt)
    (e' : List EvM × Nat) (PBv' PBr' : GMap Loc (Loc × EventBatch))
    (hok : WsOk ((v.step key r dst st' e').st σ))
    (hbv : (v.step key r dst st' e').Bv = GMap.fmap Prod.snd PBv')
    (hPBr : ∀ k, k ≠ key → PBr' !! k = PBr !! k) :
    SyncLoop σ (v.step key r dst st' e') PB PBv' PBr' keys (i + 1) := by
  refine ⟨hok, hbv, fun k hk => ?_⟩
  rw [sw_take_succ keys i key hkey] at hk
  have hk1 : k ≠ key := fun e => hk (Or.inr e)
  have hk2 : k ∉ keys.take i := fun e => hk (Or.inl e)
  obtain ⟨h1, h2, h3, h4, h5⟩ := v.step_ne key r dst st' e' k hk1
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := h.rest k hk2
  rw [h1, h2, h3, h4, h5, hPBr k hk1]
  exact ⟨g1, g2, g3, g4, g5, g6⟩

/-- An unsynced member of a loop state: its flags, not a victim, not synced. -/
theorem SyncLoop.unsynced_facts {σ : WsState} {v : SyncVars} {PB PBv PBr : GMap Loc (Loc × EventBatch)}
    {keys : List Loc} {i : Nat} (h : SyncLoop σ v PB PBv PBr keys i) {key : Loc} {r : WatchRange}
    {st : WatcherSt} (hWu : v.Wu !! key = some r) (hST : v.ST !! key = some st) :
    st.compacted = false ∧ st.restore = false ∧ st.victim = false ∧ st.ch ≠ null ∧
      σ.victimOf key = none ∧ v.Bv !! key = none ∧ v.Ws !! key = none := by
  have hu : ((v.st σ).Wu !! key).isSome := by rw [SyncVars.st_Wu, hWu]; rfl
  have hv := h.ok.wu_v key hu
  have hv' := hv
  rw [SyncVars.st_victimOf] at hv'
  have hσ : σ.victimOf key = none ∧ v.Bv !! key = none := by
    cases h1 : σ.victimOf key <;> cases h2 : v.Bv !! key <;> simp_all
  have hl : (v.st σ).live key := Or.inr (Or.inl hu)
  obtain ⟨f1, f2, f3, f4⟩ := h.ok.st_flags key st hST
  have hws : v.Ws !! key = none := by
    cases h1 : v.Ws !! key with
    | none => rfl
    | some _ =>
      have := h.ok.ws_wu key (by rw [SyncVars.st_Ws, h1]; rfl)
      rw [SyncVars.st_Wu, hWu] at this; cases this
  refine ⟨f1, f2, ?_, fun hn => (f4.1 hn) hl, hσ.1, hσ.2, hws⟩
  have := (f3 hl)
  rw [hv] at this
  cases hs : st.victim
  · rfl
  · rw [hs] at this; simp at this

/-! ## The least `minRev` of the chosen members -/

theorem sw_minRevFold_le_init (ST : GMap Loc WatcherSt) :
    ∀ (D : List Loc) (a : Int), D.foldl (minRevStep ST) a ≤ a
  | [], _ => Int.le_refl _
  | w :: D, a => by
    rw [List.foldl_cons]
    refine Int.le_trans (sw_minRevFold_le_init ST D _) ?_
    unfold minRevStep; split <;> omega

theorem sw_minRevFold_le_mem (ST : GMap Loc WatcherSt) :
    ∀ (D : List Loc) (a : Int) (w : Loc) (st : WatcherSt), w ∈ D → ST !! w = some st →
      D.foldl (minRevStep ST) a ≤ sint.Z st.minRev
  | [], _, _, _, h, _ => by cases h
  | x :: D, a, w, st, h, hs => by
    rw [List.foldl_cons]
    rcases List.mem_cons.1 h with rfl | h
    · refine Int.le_trans (sw_minRevFold_le_init ST D _) ?_
      unfold minRevStep; rw [hs]; simp only; omega
    · exact sw_minRevFold_le_mem ST D _ w st h hs

theorem sw_minRevFold_ge (ST : GMap Loc WatcherSt) (b : Int) :
    ∀ (D : List Loc) (a : Int), b ≤ a →
      (∀ w ∈ D, ∀ st, ST !! w = some st → b ≤ sint.Z st.minRev) →
      b ≤ D.foldl (minRevStep ST) a
  | [], _, h, _ => h
  | x :: D, a, h, hD => by
    rw [List.foldl_cons]
    refine sw_minRevFold_ge ST b D _ ?_ (fun w hw => hD w (List.mem_cons_of_mem _ hw))
    unfold minRevStep
    cases hs : ST !! x with
    | none => exact h
    | some st => have := hD x List.mem_cons_self st hs; simp only; omega

/-- The least `minRev` of a non-empty set of members, all with states between `0` and `cur`: at
most each member's, between `0` and `cur`. -/
theorem sw_minRevOf_bounds (ST : GMap Loc WatcherSt) (S : GMap Loc Unit) (cur : Int)
    (hne : ∃ w, (S !! w).isSome) (hst : ∀ w, (S !! w).isSome → (ST !! w).isSome)
    (hb : ∀ w st, (S !! w).isSome → ST !! w = some st → 0 ≤ sint.Z st.minRev ∧ sint.Z st.minRev ≤ cur) :
    0 ≤ minRevOf ST S ∧ minRevOf ST S ≤ cur ∧
      ∀ w st, (S !! w).isSome → ST !! w = some st → minRevOf ST S ≤ sint.Z st.minRev := by
  unfold minRevOf minRevL
  refine ⟨sw_minRevFold_ge ST 0 _ _ (by omega) (fun w hw st hs =>
      (hb w st ((GMap.mem_dom_list S w).1 hw) hs).1), ?_, fun w st hw hs =>
      sw_minRevFold_le_mem ST _ _ w st ((GMap.mem_dom_list S w).2 hw) hs⟩
  obtain ⟨w, hw⟩ := hne
  obtain ⟨st, hs⟩ := Option.isSome_iff_exists.1 (hst w hw)
  exact Int.le_trans (sw_minRevFold_le_mem ST _ _ w st ((GMap.mem_dom_list S w).2 hw) hs)
    (hb w st hw hs).2

/-! ## The lock's resources across the loop -/

theorem sw_filter_lookup {V : Type} (p : Loc → V → Bool) (m : GMap Loc V) (k : Loc) :
    (Iris.Std.PartialMap.filter p m : GMap Loc V) !! k =
      (m !! k).bind (fun v => if p k v then some v else none) := by
  show Iris.Std.PartialMap.get? (M := GMap Loc) (Iris.Std.PartialMap.filter p m) k = _
  rw [Iris.Std.LawfulPartialMap.get?_filter]; rfl

section res
open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- A big separating conjunction as the parts a predicate selects and the others. -/
theorem sw_bigSepM_split {V : Type} (p : Loc → V → Bool) (m : GMap Loc V)
    (Φ : Loc → V → IProp GF) :
    ([∗map] k ↦ x ∈ m, Φ k x) ⊣⊢ ([∗map] k ↦ x ∈ Iris.Std.PartialMap.filter p m, Φ k x) ∗
      ([∗map] k ↦ x ∈ Iris.Std.PartialMap.filter (fun k x => !p k x) m, Φ k x) := by
  rw [BigSepM.bigSepM_filter_cond p, BigSepM.bigSepM_filter_cond, ← BigSepM.bigSepM_sep_eq]
  refine ⟨BigSepM.bigSepM_mono fun {k x} _ => ?_, BigSepM.bigSepM_mono fun {k x} _ => ?_⟩
  · cases p k x <;> simp <;> iintro H <;> iframe
  · cases p k x <;> simp <;> iintro ⟨H1, H2⟩ <;> iframe

/-- `memberRes` depends on the state only at the watcher: its names, delivery, populations and
victim batch. -/
theorem sw_memberRes_congr (γ : WsNames) (q : Qp) (σ1 σ2 : WsState) (w : Loc) (st : WatcherSt)
    (hM : σ1.M !! w = σ2.M !! w) (hE : σ1.E !! w = σ2.E !! w) (hWs : σ1.Ws !! w = σ2.Ws !! w)
    (hWu : σ1.Wu !! w = σ2.Wu !! w) (hvo : σ1.victimOf w = σ2.victimOf w) :
    memberRes (GF := GF) γ q σ1 w st = memberRes γ q σ2 w st := by
  unfold memberRes popFacts WsState.live
  simp only [hM, hE, hWs, hWu, hvo]

/-- An unsynced member's resources, unfolded. -/
theorem sw_memberRes_unsynced (γ : WsNames) (q : Qp) (σ : WsState) (w : Loc) (st : WatcherSt)
    (hWs : σ.Ws !! w = none) (hWu : (σ.Wu !! w).isSome) :
    memberRes (GF := GF) γ q σ w st ⊢ ∃ (γw : WatcherNames) (r : WatchRange) (fcs : GoSlice)
      (evsw : List EvM),
      ⌜σ.M !! w = some γw⌝ ∗ watcherMeta γ w γw ∗ watcherFixed w r fcs ∗
      watcherChan γ w γw st.ch ∗ filtersOk fcs ∗ ⌜sint.Z r.startRev ≤ (γw.lo : Int)⌝ ∗
      ⌜σ.E !! w = some (evsw, sint.nat st.minRev)⌝ ∗ monoListAuthOwn γw.evs q.half evsw ∗
      dghostVar γw.live (DFrac.own q.half) true ∗ ⌜(γw.lo : Int) ≤ sint.Z st.minRev⌝ ∗
      evsWf γ r γw.lo evsw (sint.nat st.minRev) ∗
      ∃ Lc : Log, idxCert γ.st.idx Lc ∗ ⌜sint.Z st.minRev < Lc.length⌝ := by
  have hl : σ.live w := Or.inr (Or.inl hWu)
  have hWs' : (σ.Ws !! w).isSome = false := by rw [hWs]; rfl
  unfold memberRes popFacts
  simp only [hl, hWs', hWu, ↓reduceIte, Bool.false_eq_true]
  iintro ⟨%γw, %r, %fcs, %hM, #Hm, #Hf, #Hc, #Hfo, %Hsr, %evsw, %d, %hE, Ha, Hl, ⟨%Hp, #Hwf, #Hc2⟩⟩
  obtain ⟨h1, rfl⟩ := Hp
  iexists γw, r, fcs, evsw
  iframe Hm Hf Hc Hfo Ha Hl Hwf Hc2
  ipureintro; exact ⟨hM, Hsr, hE, h1⟩

/-- A live member's resources from their parts. -/
theorem sw_memberRes_intro (γ : WsNames) (σ : WsState) (w : Loc) (st : WatcherSt)
    (hl : σ.live w) (γw : WatcherNames) (r : WatchRange) (fcs : GoSlice) (evsw : List EvM) (d : Nat)
    (hM : σ.M !! w = some γw) (hE : σ.E !! w = some (evsw, d))
    (hsr : sint.Z r.startRev ≤ (γw.lo : Int)) :
    watcherMeta γ w γw ∗ watcherFixed w r fcs ∗ watcherChan γ w γw st.ch ∗ filtersOk fcs ∗
      monoListAuthOwn γw.evs (1 : Qp).half evsw ∗ dghostVar γw.live (DFrac.own (1 : Qp).half) true ∗
      popFacts γ σ w r γw.lo st evsw d ⊢
    memberRes (GF := GF) γ 1 σ w st := by
  iintro ⟨#Hm, #Hf, #Hc, #Hfo, Ha, Hl, #Hp⟩
  unfold memberRes
  iexists γw, r, fcs
  simp only [hl, ↓reduceIte]
  iframe Hm Hf Hc Hfo
  isplitr
  · ipureintro; exact hM
  isplitr
  · ipureintro; exact hsr
  iexists evsw, d
  iframe Ha Hl Hp
  ipureintro; exact hE

theorem sw_popFacts_synced (γ : WsNames) (σ : WsState) (k : Loc) (r : WatchRange) (lo : Nat)
    (st : WatcherSt) (evsw : List EvM) (d : Nat) (h : (σ.Ws !! k).isSome) :
    popFacts (GF := GF) γ σ k r lo st evsw d =
      iprop(⌜(lo : Int) ≤ sint.Z st.minRev ∧ sint.Z st.minRev ≤ d⌝ ∗ evsWf γ r lo evsw d) := by
  unfold popFacts; rw [if_pos h]

theorem sw_popFacts_unsynced (γ : WsNames) (σ : WsState) (k : Loc) (r : WatchRange) (lo : Nat)
    (st : WatcherSt) (evsw : List EvM) (d : Nat) (h1 : (σ.Ws !! k).isSome = false)
    (h2 : (σ.Wu !! k).isSome) :
    popFacts (GF := GF) γ σ k r lo st evsw d =
      iprop(⌜(lo : Int) ≤ sint.Z st.minRev ∧ d = sint.nat st.minRev⌝ ∗ evsWf γ r lo evsw d ∗
        ∃ Lc : Log, idxCert γ.st.idx Lc ∗ ⌜sint.Z st.minRev < Lc.length⌝) := by
  unfold popFacts; simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]

theorem sw_popFacts_victim (γ : WsNames) (σ : WsState) (k : Loc) (r : WatchRange) (lo : Nat)
    (st : WatcherSt) (evsw : List EvM) (d : Nat) (B : EventBatch) (h1 : (σ.Ws !! k).isSome = false)
    (h2 : (σ.Wu !! k).isSome = false) (h3 : σ.victimOf k = some B) :
    popFacts (GF := GF) γ σ k r lo st evsw d =
      iprop(⌜(lo : Int) ≤ sint.Z st.minRev ∧ d = sint.nat st.minRev ∧ victimBatchOk lo st B⌝ ∗
        evsWf γ r lo (evsw ++ B.evs) d) := by
  unfold popFacts; simp only [h1, h2, h3, Bool.false_eq_true, ↓reduceIte]

/-- The unsynced members' `minRev`s are non-negative and below the committed log's length (their
certificates are below it). -/
theorem sw_unsynced_bounds (γ : WsNames) (σ : WsState) (hok : WsOk σ) (q : Qp) (C : Log) :
    ([∗map] w ↦ st ∈ σ.ST, memberRes (GF := GF) γ 1 σ w st) ∗ idxLogAuth γ.st.idx q C ⊢
      ⌜∀ w st, σ.ST !! w = some st → (σ.Wu !! w).isSome →
        0 ≤ sint.Z st.minRev ∧ sint.Z st.minRev < C.length⌝ := by
  iintro ⟨Hmem, Hauth⟩
  iapply pure_forall.2; iintro %w
  iapply pure_forall.2; iintro %st
  by_cases hst : σ.ST !! w = some st
  rotate_left
  · ipureintro; intro h; exact absurd h hst
  by_cases hu : (σ.Wu !! w).isSome
  rotate_left
  · ipureintro; intro _ h; exact absurd h hu
  have hws : σ.Ws !! w = none := by
    cases h : σ.Ws !! w with
    | none => rfl
    | some _ => have := hok.ws_wu w (by rw [h]; rfl); rw [this] at hu; cases hu
  icases (BigSepM.bigSepM_lookup_acc hst).1 $$ Hmem with ⟨Hw, -⟩
  icases sw_memberRes_unsynced γ 1 σ w st hws hu $$ Hw with
    ⟨%γw, %r, %fcs, %evsw, -, -, -, -, -, -, -, -, -, %Hlo, -, %Lc, #HLc, %HLc⟩
  icases idxLogAuth_cert_prefix _ _ _ _ $$ [$Hauth $HLc] with %Hp
  ipureintro
  intro _ _
  have := Hp.length_le
  omega

/-- A step changes no other member's resources. -/
theorem sw_memberRes_step_ne (γ : WsNames) (σ : WsState) (v : SyncVars) (w : Loc)
    (r : WatchRange) (dst : SyncDst) (st' : WatcherSt) (e' : List EvM × Nat) (k : Loc)
    (hk : k ≠ w) (x : WatcherSt) :
    memberRes (GF := GF) γ 1 (v.st σ) k x = memberRes γ 1 ((v.step w r dst st' e').st σ) k x := by
  obtain ⟨-, h2, h3, h4, h5⟩ := v.step_ne w r dst st' e' k hk
  refine sw_memberRes_congr γ 1 _ _ k x rfl ?_ ?_ ?_ ?_
  · exact h4.symm
  · exact h3.symm
  · exact h2.symm
  · rw [SyncVars.st_victimOf, SyncVars.st_victimOf, h5]

/-- Replacing one key's entry of a big separating conjunction, with a new predicate that agrees
elsewhere. -/
theorem sw_bigSepM_step {V : Type} {Φ Ψ : Loc → V → IProp GF} (m : GMap Loc V) (w : Loc) (y : V)
    (h : ∀ k v, k ≠ w → Φ k v ⊢ Ψ k v) :
    ([∗map] k ↦ v ∈ Iris.Std.delete m w, Φ k v) ∗ Ψ w y ⊢ [∗map] k ↦ v ∈ <[w := y]> m, Ψ k v := by
  refine (sep_comm.1.trans ?_).trans BigSepM.bigSepM_insert_delete.2
  refine sep_mono_right (BigSepM.bigSepM_mono (fun {k v} hk => h k v ?_))
  intro e; subst e
  have : (Iris.Std.delete m k : GMap Loc V) = GMap.delete k m := rfl
  rw [this, gmap_get?_eq] at hk
  have h2 := GMap.lookup_delete m k
  rw [h2] at hk; cases hk

/-- A watcher's delivered events extended with the range's events of a certified log from where
they stopped. -/
theorem sw_evsWf_extend (γ : WsNames) (r : WatchRange) (lo : Nat) (evsw : List EvM) (m D : Nat)
    (C : Log) (hm : m ≤ D) (hD : D ≤ C.length) (hlo : lo ≤ m) :
    evsWf (GF := GF) γ r lo evsw m ∗ idxCert γ.st.idx C ⊢
      evsWf γ r lo (evsw ++ watchEvents C r m D) D := by
  iintro ⟨Hwf, #HC⟩
  iunfold evsWf at Hwf
  icases Hwf with ⟨%L, #HlbL, %HL⟩
  iunfold idxCert at HC
  icases HC with ⟨#HlbC, -, -, -⟩
  ihave %Hcmp := mono_list_lb_valid _ _ _ $$ HlbC HlbL
  have hcmp := histOf_cmp_log Hcmp
  iunfold evsWf
  iexists C
  iframe HlbC
  ipureintro
  refine ⟨?_, Or.inl hD⟩
  rw [HL.1, watchEvents_cmp hcmp.symm r HL.2 (Or.inl (by omega)),
    ← watchEvents_append C r hlo hm]

/-- The lock's resources of the members after a step: the stepped member's new ones. -/
theorem sw_res_step (γ : WsNames) (σ : WsState) (v : SyncVars) (key : Loc) (r : WatchRange)
    (dst : SyncDst) (st' : WatcherSt) (e' : List EvM × Nat) :
    ([∗map] k ↦ x ∈ Iris.Std.delete v.ST key, watcherOwn (GF := GF) k x) ∗ watcherOwn key st' ∗
      ([∗map] k ↦ x ∈ Iris.Std.delete v.ST key, memberRes γ 1 (v.st σ) k x) ∗
      memberRes γ 1 ((v.step key r dst st' e').st σ) key st' ⊢
    ([∗map] k ↦ x ∈ (v.step key r dst st' e').ST, watcherOwn k x) ∗
      ([∗map] k ↦ x ∈ (v.step key r dst st' e').ST,
        memberRes γ 1 ((v.step key r dst st' e').st σ) k x) := by
  rw [SyncVars.step_ST]
  iintro ⟨Hst, Hw, Hmem, Hm⟩
  isplitl [Hst Hw]
  · iapply (sw_bigSepM_step v.ST key st' (fun k x _ => .rfl)) $$ [$Hst $Hw]
  · iapply (sw_bigSepM_step v.ST key st' (fun k x hk => by
      rw [sw_memberRes_step_ne γ σ v key r dst st' e' k hk x])) $$ [$Hmem $Hm]

/-- The stepped member's resources, synced. -/
theorem sw_memberRes_new_synced (γ : WsNames) (σ : WsState) (v : SyncVars) (key : Loc)
    (r : WatchRange) (st' : WatcherSt) (γw : WatcherNames) (fcs : GoSlice) (evsw : List EvM)
    (D : Nat) (hM : σ.M !! key = some γw) (hsr : sint.Z r.startRev ≤ (γw.lo : Int))
    (hlo : (γw.lo : Int) ≤ sint.Z st'.minRev ∧ sint.Z st'.minRev ≤ D) :
    watcherMeta γ key γw ∗ watcherFixed key r fcs ∗ watcherChan γ key γw st'.ch ∗ filtersOk fcs ∗
      monoListAuthOwn γw.evs (1 : Qp).half evsw ∗ dghostVar γw.live (DFrac.own (1 : Qp).half) true ∗
      evsWf γ r γw.lo evsw D ⊢
    memberRes (GF := GF) γ 1 ((v.step key r .synced st' (evsw, D)).st σ) key st' := by
  have hWs : ((v.step key r .synced st' (evsw, D)).st σ).Ws !! key = some r := by
    simp [SyncVars.step, SyncVars.st, GMap.lookup_insert]
  iintro ⟨#Hm, #Hf, #Hc, #Hfo, Ha, Hl, #Hwf⟩
  iapply (sw_memberRes_intro γ ((v.step key r .synced st' (evsw, D)).st σ) key st' (Or.inl (by rw [hWs]; rfl)) γw r fcs evsw D hM
    (by simp [SyncVars.step, SyncVars.st, GMap.lookup_insert]) hsr)
  rw [sw_popFacts_synced γ _ key r γw.lo st' evsw D (by rw [hWs]; rfl)]
  iframe Hm Hf Hc Hfo Ha Hl Hwf
  ipureintro; exact hlo

/-- The stepped member's resources, kept unsynced. -/
theorem sw_memberRes_new_unsynced (γ : WsNames) (σ : WsState) (v : SyncVars) (key : Loc)
    (r : WatchRange) (st' : WatcherSt) (γw : WatcherNames) (fcs : GoSlice) (evsw : List EvM)
    (D : Nat) (Lc : Log) (hM : σ.M !! key = some γw) (hsr : sint.Z r.startRev ≤ (γw.lo : Int))
    (hWs0 : v.Ws !! key = none) (hWu0 : v.Wu !! key = some r)
    (hlo : (γw.lo : Int) ≤ sint.Z st'.minRev ∧ D = sint.nat st'.minRev)
    (hLc : sint.Z st'.minRev < Lc.length) :
    watcherMeta γ key γw ∗ watcherFixed key r fcs ∗ watcherChan γ key γw st'.ch ∗ filtersOk fcs ∗
      monoListAuthOwn γw.evs (1 : Qp).half evsw ∗ dghostVar γw.live (DFrac.own (1 : Qp).half) true ∗
      evsWf γ r γw.lo evsw D ∗ idxCert γ.st.idx Lc ⊢
    memberRes (GF := GF) γ 1 ((v.step key r .unsynced st' (evsw, D)).st σ) key st' := by
  have hWs : ((v.step key r .unsynced st' (evsw, D)).st σ).Ws !! key = none := by
    simp [SyncVars.step, SyncVars.st, hWs0]
  have hWu : ((v.step key r .unsynced st' (evsw, D)).st σ).Wu !! key = some r := by
    simp [SyncVars.step, SyncVars.st, hWu0]
  iintro ⟨#Hm, #Hf, #Hc, #Hfo, Ha, Hl, #Hwf, #HLc⟩
  iapply (sw_memberRes_intro γ ((v.step key r .unsynced st' (evsw, D)).st σ) key st' (Or.inr (Or.inl (by rw [hWu]; rfl))) γw r fcs evsw D hM
    (by simp [SyncVars.step, SyncVars.st, GMap.lookup_insert]) hsr)
  rw [sw_popFacts_unsynced γ _ key r γw.lo st' evsw D (by rw [hWs]; rfl) (by rw [hWu]; rfl)]
  iframe Hm Hf Hc Hfo Ha Hl Hwf
  isplitr
  · ipureintro; exact hlo
  iexists Lc
  iframe HLc
  ipureintro; exact hLc

/-- The stepped member's resources, a victim with its batch. -/
theorem sw_memberRes_new_victim (γ : WsNames) (σ : WsState) (v : SyncVars) (key : Loc)
    (r : WatchRange) (B : EventBatch) (st' : WatcherSt) (γw : WatcherNames) (fcs : GoSlice)
    (evsw : List EvM) (D : Nat) (hM : σ.M !! key = some γw)
    (hsr : sint.Z r.startRev ≤ (γw.lo : Int)) (hWs0 : v.Ws !! key = none)
    (hvo : σ.victimOf key = none)
    (hlo : (γw.lo : Int) ≤ sint.Z st'.minRev ∧ D = sint.nat st'.minRev ∧ victimBatchOk γw.lo st' B) :
    watcherMeta γ key γw ∗ watcherFixed key r fcs ∗ watcherChan γ key γw st'.ch ∗ filtersOk fcs ∗
      monoListAuthOwn γw.evs (1 : Qp).half evsw ∗ dghostVar γw.live (DFrac.own (1 : Qp).half) true ∗
      evsWf γ r γw.lo (evsw ++ B.evs) D ⊢
    memberRes (GF := GF) γ 1 ((v.step key r (.victim B) st' (evsw, D)).st σ) key st' := by
  have hWs : ((v.step key r (.victim B) st' (evsw, D)).st σ).Ws !! key = none := by
    simp [SyncVars.step, SyncVars.st, hWs0]
  have hWu : ((v.step key r (.victim B) st' (evsw, D)).st σ).Wu !! key = none := by
    simp [SyncVars.step, SyncVars.st, GMap.lookup_delete]
  have hv : ((v.step key r (.victim B) st' (evsw, D)).st σ).victimOf key = some B := by
    rw [SyncVars.st_victimOf, hvo]; simp [SyncVars.step, GMap.lookup_insert]
  iintro ⟨#Hm, #Hf, #Hc, #Hfo, Ha, Hl, #Hwf⟩
  iapply (sw_memberRes_intro γ ((v.step key r (.victim B) st' (evsw, D)).st σ) key st' (Or.inr (Or.inr (by rw [hv]; rfl))) γw r fcs evsw D hM
    (by simp [SyncVars.step, SyncVars.st, GMap.lookup_insert]) hsr)
  rw [sw_popFacts_victim γ _ key r γw.lo st' evsw D B (by rw [hWs]; rfl) (by rw [hWu]; rfl) hv]
  iframe Hm Hf Hc Hfo Ha Hl Hwf
  ipureintro; exact hlo

end res

end mvcc
end EtcdGrove
end Perennial
