/-
**The lessor-window tie** (auth-lease S4 item 7b F4, 2026-11-17; design: `questions.md`, "Item 7b F4 decision",
"the tie cannot see the store's log", K1, and the namespace decision (b)).

An invariant of its own namespace `winTieN` (outside `kvsN`, `mvccN`, `wsN`) that ties the lessor's windows' list (the
tie's quarter, `lease.lessorWinTie`) to the store's committed log (a quarter of `γs.st`, split from the apply thread's
half: K1). It records, append-only:
- per window of the lessor's list, its start, its target `T` and the model log `Lt` after the entry whose target it is
  (`□ Nx Lt`, `T` its items), or a free marker (with the fact `Fr`: the server's is "not in the no-snapshot mode");
- *anchors* `(n, j, L)`: in window `n`, the lessor's snapshot `j` (at or after the window's start) has the items of the
  store's log `L`, which the store had committed (`□ Nx L`). A window's push records one at its start, at the store's
  log then; every store commit within a window records one (the end builder, holding the window token).
The anchors' logs grow along the list, and the last one is the store's current log while a window is open: what the
per-member lessor law (step 7) needs to place an index pushed after a floor of the store.

The apply thread holds the window token `ghostVar γt.w ½ w` (the server's `E.Wt`), the tie the other half at the
lessor's open window.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVStoreCore
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section
namespace Perennial
namespace EtcdGrove
namespace srvApi
open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc mvcc.api
open go_etcd_io.etcd.server.v3.lease (LeaseItem)
open lease (LWin LWinRec lastWin lessorWinTie lessorAt winWit)

/-! ## The pure part -/

section pure
variable [GooseExts]

/-- The lessor's item map of the store's log `L`: the items of the state after it. -/
abbrev itemsOfLog (L : mvcc.Log) : GMap LeaseItem w64 := mvcc.leaseItemsOf (mvcc.stateAfter L)

/-- **A window's record**: its start, its target (`none`: a free marker) and the model log after the entry whose
target it is. -/
abbrev TWRec := Nat × Option (GMap LeaseItem w64) × mvcc.Log

/-- **An anchor**: the window's index in the windows' list, the lessor's snapshot index, the store's log. -/
abbrev TARec := Nat × Nat × mvcc.Log

/-- **The tie's pure facts**: the records are the lessor's windows; every anchor at or after its window's start,
toward its window's target (its log a prefix of the window's model log, or its items the target); every window's
target the items of its model log, with an anchor at its start whose log is a prefix of the model log; the anchors'
logs growing, all prefixes of the store's log `log`; while a window is open, the last anchor its own, at `log`. -/
def tieOk (ws : List LWinRec) (log : mvcc.Log) (tw : List TWRec) (anc : List TARec) : Prop :=
  tw.map (fun r => (r.1, r.2.1)) = ws ∧ tw ≠ [] ∧
  (∀ a ∈ anc, ∃ (s : Nat) (x : Option (GMap LeaseItem w64)) (Lt : mvcc.Log), tw[a.1]? = some (s, x, Lt) ∧
    s ≤ a.2.1 ∧ ∀ T, x = some T → (a.2.2 <+: Lt ∨ itemsOfLog a.2.2 = T)) ∧
  (∀ (n s : Nat) (T : GMap LeaseItem w64) (Lt : mvcc.Log), tw[n]? = some (s, some T, Lt) →
    T = itemsOfLog Lt ∧ ∃ Ls, (n, s, Ls) ∈ anc ∧ Ls <+: Lt) ∧
  anc.Pairwise (fun a b => a.2.2 <+: b.2.2) ∧ (∀ a ∈ anc, a.2.2 <+: log) ∧
  (∀ (s : Nat) (T : GMap LeaseItem w64), lastWin ws = some (s, T) →
    ∃ j, anc.getLast? = some (tw.length - 1, j, log))

theorem getElem?_prefix {A : Type} {l l' : List A} (h : l <+: l') {i : Nat} {a : A} (hi : l[i]? = some a) :
    l'[i]? = some a := by
  obtain ⟨t, rfl⟩ := h
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hi).1]; exact hi

/-- The open window's record is the last one. -/
theorem tw_last {ws : List LWinRec} {tw : List TWRec} (hw : tw.map (fun r => (r.1, r.2.1)) = ws)
    {s : Nat} {T : GMap LeaseItem w64} (h : lastWin ws = some (s, T)) :
    ∃ Lt, tw[tw.length - 1]? = some (s, some T, Lt) := by
  unfold lastWin at h
  subst hw
  cases hl : tw.getLast? with
  | none =>
    rw [List.getLast?_eq_none_iff.1 hl] at h; simp at h
  | some r =>
    rw [List.getLast?_map, hl] at h
    obtain ⟨s', x, Lt⟩ := r
    simp only [Option.map_some] at h
    cases x with
    | none => simp at h
    | some T' =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨Lt, ?_⟩
      rw [List.getLast?_eq_getElem?] at hl; exact hl

/-- The store's log grows (a restore, a commit outside a window): the facts stay. -/
theorem tieOk_grow {ws : List LWinRec} {log log' : mvcc.Log} {tw : List TWRec} {anc : List TARec}
    (h : tieOk ws log tw anc) (hl : log <+: log') (hw : lastWin ws = none) : tieOk ws log' tw anc :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, fun a ha => (h.2.2.2.2.2.1 a ha).trans hl,
    fun s T h' => by rw [hw] at h'; cases h'⟩

/-- **A commit in the open window `(s0, T0)`**: the anchor `(n, j, Lc)` at the new log `Lc`, the lessor's snapshot
`j ≥ s0` at its items; `Lc` the old log if the commit is empty, otherwise of items `T0`. -/
theorem tieOk_commit {ws : List LWinRec} {log : mvcc.Log} {tw : List TWRec} {anc : List TARec}
    (h : tieOk ws log tw anc) {s0 : Nat} {T0 : GMap LeaseItem w64} (hw : lastWin ws = some (s0, T0))
    (pend : List mvcc.Change) (j : Nat) (hj : s0 ≤ j)
    (hT : pend ≠ [] → T0 = itemsOfLog (mvcc.commitLog log pend)) :
    tieOk ws (mvcc.commitLog log pend) tw (anc ++ [(tw.length - 1, j, mvcc.commitLog log pend)]) := by
  obtain ⟨hW, hne, hA, hT', hP, hC, hL⟩ := h
  obtain ⟨Lt0, hLt0⟩ := tw_last hW hw
  have hpre : log <+: mvcc.commitLog log pend := by
    unfold mvcc.commitLog; split
    · exact List.prefix_refl _
    · exact List.prefix_append _ _
  refine ⟨hW, hne, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hA a ha
    · simp only [List.mem_singleton] at ha
      subst ha
      refine ⟨s0, some T0, Lt0, hLt0, hj, ?_⟩
      intro T hTT
      simp only [Option.some.injEq] at hTT
      subst hTT
      by_cases hp : pend = []
      · -- an empty commit: the last anchor's log, `log`
        obtain ⟨j0, hj0⟩ := hL s0 T0 hw
        have hm : (tw.length - 1, j0, log) ∈ anc := List.mem_of_getLast? hj0
        obtain ⟨s', x', Lt', h1, -, h3⟩ := hA _ hm
        rw [hLt0] at h1
        simp only [Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨-, rfl, rfl⟩ := h1
        have hc : mvcc.commitLog log pend = log := by unfold mvcc.commitLog; rw [if_pos hp]
        rw [hc]; exact h3 _ rfl
      · exact Or.inr (hT hp).symm
  · intro n s T Lt hn
    obtain ⟨h1, Ls, h2, h3⟩ := hT' n s T Lt hn
    exact ⟨h1, Ls, List.mem_append_left _ h2, h3⟩
  · rw [List.pairwise_append]
    refine ⟨hP, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    exact (hC a ha).trans hpre
  · intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact (hC a ha).trans hpre
    · simp only [List.mem_singleton] at ha; subst ha; exact List.prefix_refl _
  · intro s T _
    exact ⟨j, by simp⟩

/-- **A window's push** `(s, T)`, its model log `Lt` extending the store's log `log`, whose items `T` are; its start
anchor at `log`. -/
theorem tieOk_push {ws : List LWinRec} {log : mvcc.Log} {tw : List TWRec} {anc : List TARec}
    (h : tieOk ws log tw anc) (s : Nat) (T : GMap LeaseItem w64) (Lt : mvcc.Log) (hlt : log <+: Lt)
    (hT : T = itemsOfLog Lt) :
    tieOk (ws ++ [(s, some T)]) log (tw ++ [(s, some T, Lt)]) (anc ++ [(tw.length, s, log)]) := by
  obtain ⟨hW, hne, hA, hT', hP, hC, hL⟩ := h
  refine ⟨by rw [List.map_append, hW]; rfl, by simp, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨s', x, Lt', h1, h2, h3⟩ := hA a ha
      exact ⟨s', x, Lt', getElem?_prefix (List.prefix_append _ _) h1, h2, h3⟩
    · simp only [List.mem_singleton] at ha
      subst ha
      refine ⟨s, some T, Lt, by simp, Nat.le_refl _, ?_⟩
      intro T' hTT
      exact Or.inl hlt
  · intro n s' T' Lt' hn
    by_cases hlt' : n < tw.length
    · rw [List.getElem?_append_left hlt'] at hn
      obtain ⟨h1, Ls, h2, h3⟩ := hT' n s' T' Lt' hn
      exact ⟨h1, Ls, List.mem_append_left _ h2, h3⟩
    · have hn' : n = tw.length := by
        have := (List.getElem?_eq_some_iff.1 hn).1
        simp at this; omega
      subst hn'
      simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero,
        Option.some.injEq, Prod.mk.injEq] at hn
      obtain ⟨rfl, hTT, rfl⟩ := hn
      subst hTT
      exact ⟨hT, log, by simp, hlt⟩
  · rw [List.pairwise_append]
    refine ⟨hP, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    exact hC a ha
  · intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hC a ha
    · simp only [List.mem_singleton] at ha; subst ha; exact List.prefix_refl _
  · intro s' T' _
    exact ⟨s, by simp⟩

/-- **A free marker's push** `s`. -/
theorem tieOk_free {ws : List LWinRec} {log : mvcc.Log} {tw : List TWRec} {anc : List TARec}
    (h : tieOk ws log tw anc) (s : Nat) (Lt : mvcc.Log) :
    tieOk (ws ++ [(s, none)]) log (tw ++ [(s, none, Lt)]) anc := by
  obtain ⟨hW, hne, hA, hT', hP, hC, hL⟩ := h
  refine ⟨by rw [List.map_append, hW]; rfl, by simp, ?_, ?_, hP, hC, ?_⟩
  · intro a ha
    obtain ⟨s', x, Lt', h1, h2, h3⟩ := hA a ha
    exact ⟨s', x, Lt', getElem?_prefix (List.prefix_append _ _) h1, h2, h3⟩
  · intro n s' T' Lt' hn
    by_cases hlt' : n < tw.length
    · rw [List.getElem?_append_left hlt'] at hn
      exact hT' n s' T' Lt' hn
    · have hn' : n = tw.length := by
        have := (List.getElem?_eq_some_iff.1 hn).1
        simp at this; omega
      subst hn'
      simp [List.getElem?_append_right (Nat.le_refl _)] at hn
  · intro s' T' h'
    simp [lastWin] at h'

/-- **The first window** `(s, T)` of an empty list, at the store's log `log`. -/
theorem tieOk_first (log : mvcc.Log) (s : Nat) (T : GMap LeaseItem w64) (Lt : mvcc.Log) (hlt : log <+: Lt)
    (hT : T = itemsOfLog Lt) :
    tieOk [(s, some T)] log [(s, some T, Lt)] [(0, s, log)] := by
  refine ⟨rfl, by simp, ?_, ?_, List.pairwise_singleton _ _, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_singleton] at ha; subst ha
    exact ⟨s, some T, Lt, rfl, Nat.le_refl _, fun T' _ => Or.inl hlt⟩
  · intro n s' T' Lt' hn
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hn
      obtain ⟨rfl, hTT, rfl⟩ := hn
      subst hTT
      exact ⟨hT, log, by simp, hlt⟩
    | succ n => simp at hn
  · intro a ha; simp only [List.mem_singleton] at ha; subst ha; exact List.prefix_refl _
  · intro s' T' _; exact ⟨s, rfl⟩

/-- The greatest index below `b` satisfying `P`, above one that does. -/
theorem exists_greatest (P : Nat → Prop) : ∀ (b n0 : Nat), n0 < b → P n0 →
    ∃ n, n0 ≤ n ∧ n < b ∧ P n ∧ ∀ k, n < k → k < b → ¬ P k
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | b + 1, n0, h, hP => by
    by_cases hb : P b
    · exact ⟨b, by omega, by omega, hb, fun k h1 h2 => by omega⟩
    · have hn0 : n0 < b := by
        rcases Nat.lt_or_ge n0 b with h' | h'
        · exact h'
        · have : n0 = b := by omega
          subst this; exact absurd hP hb
      obtain ⟨n, h1, h2, h3, h4⟩ := exists_greatest P b n0 hn0 hP
      refine ⟨n, h1, by omega, h3, fun k hk1 hk2 => ?_⟩
      rcases Nat.lt_or_ge k b with h' | h'
      · exact h4 k hk1 h'
      · have : k = b := by omega
        subst this; exact hb

/-- **The window of an index `i` at or after the observation's anchor** (the law's core, pure): the tie's facts now
(`tieOk ws log tw anc`, `winsOk hs ws`) and at the observation (the records `tw0`, the anchors `anc0`, whose last is
`(tw0.length - 1, j0, L0)` in a window) give `i`'s window `n`: a free marker, or a window `(s, T)` with an anchor
`(n, ja, La)` at or before `i` whose log extends `L0`, from which `i` is stable. -/
theorem tie_pick {ws : List LWinRec} {log : mvcc.Log} {tw : List TWRec} {anc : List TARec}
    (hok : tieOk ws log tw anc) {hs : List lease.LSnap} (hW : lease.winsOk hs ws)
    {tw0 : List TWRec} {anc0 : List TARec} (htw : tw0 <+: tw) (hanc : anc0 <+: anc)
    {j0 : Nat} {L0 : mvcc.Log} (hlast : anc0.getLast? = some (tw0.length - 1, j0, L0))
    (hidx : ∀ a ∈ anc0, a.1 < tw0.length) {i : Nat} {σl : lease.LSnap} (hi : hs[i]? = some σl)
    (hj0 : j0 ≤ i) :
    ∃ (n s : Nat) (x : Option (GMap LeaseItem w64)) (Lt : mvcc.Log), tw[n]? = some (s, x, Lt) ∧
      ∀ T, x = some T → ∃ (ja : Nat) (La : mvcc.Log), (n, ja, La) ∈ anc ∧ L0 <+: La ∧ ja ≤ i ∧
        (La <+: Lt ∨ itemsOfLog La = T) ∧ lease.winStable hs ja T i := by
  obtain ⟨hWm, hne, hA, hT, hP, hC, hL⟩ := hok
  have hmem0 : (tw0.length - 1, j0, L0) ∈ anc0 := List.mem_of_getLast? hlast
  have hmem : (tw0.length - 1, j0, L0) ∈ anc := hanc.subset hmem0
  obtain ⟨s0, x0, Lt0, h01, h02, -⟩ := hA _ hmem
  have hn0 : tw0.length - 1 < tw.length := (List.getElem?_eq_some_iff.1 h01).1
  -- the greatest window starting at or before `i`
  let P : Nat → Prop := fun n => ∃ r : TWRec, tw[n]? = some r ∧ r.1 ≤ i
  obtain ⟨n, hn1, hn2, ⟨⟨s, x, Lt⟩, hr, hsi⟩, hgr⟩ :=
    exists_greatest P tw.length (tw0.length - 1) hn0 ⟨_, h01, by simp only at h02 ⊢; omega⟩
  have hwn : ws[n]? = some (s, x) := by rw [← hWm, List.getElem?_map, hr]; rfl
  have hend : i ≤ lease.winEnd hs ws n := by
    unfold lease.winEnd
    cases hn' : ws[n + 1]? with
    | none => have := (List.getElem?_eq_some_iff.1 hi).1; simp only; omega
    | some r' =>
      simp only
      rcases Nat.lt_or_ge i r'.1 with h' | h'
      · omega
      · exfalso
        have hlt : n + 1 < tw.length := by
          have := (List.getElem?_eq_some_iff.1 hn').1
          rw [← hWm, List.length_map] at this; exact this
        rw [← hWm, List.getElem?_map] at hn'
        cases hr' : tw[n + 1]? with
        | none => rw [hr'] at hn'; cases hn'
        | some r'' =>
          rw [hr'] at hn'
          simp only [Option.map_some, Option.some.injEq] at hn'
          exact hgr (n + 1) (by omega) hlt ⟨r'', hr', by rw [← hn'] at h'; exact h'⟩
  refine ⟨n, s, x, Lt, hr, ?_⟩
  intro T hx
  subst hx
  rcases Nat.lt_or_ge (tw0.length - 1) n with hlt | hge
  · -- a window pushed after the observation: its start anchor
    obtain ⟨-, Ls, hLs, hLsLt⟩ := hT n s T Lt hr
    obtain ⟨rest, rfl⟩ := hanc
    have hrest : (n, s, Ls) ∈ rest := by
      rcases List.mem_append.1 hLs with h | h
      · exact absurd (hidx _ h) (by simp only; omega)
      · exact h
    have hpre : L0 <+: Ls := (List.pairwise_append.1 hP).2.2 _ hmem0 _ hrest
    exact ⟨s, Ls, hLs, hpre, hsi, Or.inl hLsLt,
      hW.2.2 n s T s i hwn (Nat.le_refl _) hsi hend⟩
  · -- the observation's window: its last anchor then
    have hn : n = tw0.length - 1 := by omega
    subst hn
    rw [h01] at hr
    simp only [Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl, rfl⟩ := hr
    obtain ⟨s', x', Lt', h1, h2, h3⟩ := hA _ hmem
    rw [h01] at h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl, rfl⟩ := h1
    exact ⟨j0, L0, hmem, List.prefix_refl _, hj0, h3 T rfl,
      hW.2.2 _ s0 T j0 i hwn h2 hj0 hend⟩

/-- With no window open, the last record is a free marker. -/
theorem tieOk_free_last {ws : List LWinRec} {log : mvcc.Log} {tw : List TWRec} {anc : List TARec}
    (h : tieOk ws log tw anc) (hw : lastWin ws = none) :
    ∃ (s : Nat) (Lt : mvcc.Log), tw[tw.length - 1]? = some (s, none, Lt) := by
  obtain ⟨hW, hne, -⟩ := h
  cases hl : tw.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.1 hl) hne
  | some r =>
    obtain ⟨s, x, Lt⟩ := r
    have hws : ws.getLast? = some (s, x) := by rw [← hW, List.getLast?_map, hl]; rfl
    cases x with
    | none => exact ⟨s, Lt, by rw [List.getLast?_eq_getElem?] at hl; exact hl⟩
    | some T => unfold lastWin at hw; rw [hws] at hw; cases hw

/-- Every anchor's window is a record. -/
theorem tieOk_idx {ws : List LWinRec} {log : mvcc.Log} {tw : List TWRec} {anc : List TARec}
    (h : tieOk ws log tw anc) : ∀ a ∈ anc, a.1 < tw.length := by
  intro a ha
  obtain ⟨s, x, Lt, h1, -⟩ := h.2.2.1 a ha
  exact (List.getElem?_eq_some_iff.1 h1).1

/-- **The law's conclusion at an index of a window** (pure): the snapshot `σl` at `i`, stable from the anchor's
snapshot `σa` (at `ja`, of the items of `La`) in the window of target `T` (the items of `Lt`), holds every item that
both `La` and `Lt` put on `id`, and `id` is live there. -/
theorem tie_holds {hs : List lease.LSnap} {ja i : Nat} {σa σl : lease.LSnap} {La Lt : mvcc.Log}
    {T : GMap LeaseItem w64} (ha : hs[ja]? = some σa) (haI : σa.2.1 = itemsOfLog La)
    (hst : lease.winStable hs ja T i) (hi : hs[i]? = some σl) (hT : T = itemsOfLog Lt)
    (hlive : lease.itemsLive σl) :
    ∀ (it : LeaseItem) (id : w64), (itemsOfLog La).lookup it = some id →
      (itemsOfLog Lt).lookup it = some id → σl.2.1.lookup it = some id ∧ (σl.1.lookup id).isSome := by
  intro it id h1 h2
  have h3 := hst σa σl ha hi it (by rw [haI, hT, h1, h2])
  rw [hT, h2] at h3
  exact ⟨h3, hlive it id h3⟩

end pure

/-! ## The invariant -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The tie's namespace (its own: outside `kvsN`, `mvccN` and the watch path's `wsN`; the namespace decision (b)). -/
def winTieN : Namespace := nroot .@ "server_lessor_win"

/-- **The tie's ghost names**: the window token `w` (a ghost variable of the open window: ½ the tie, ½ the apply
thread), the windows' records `t` and the anchors `a` (monotone lists). -/
structure WTNames where
  w : GName
  t : GName
  a : GName
deriving Inhabited

/-- A window record's facts: a window's model log committed, a free marker's fact `Fr`. -/
def twFacts (Nx : mvcc.Log → IProp GF) (Fr : Prop) (r : TWRec) : IProp GF :=
  match r.2.1 with
  | some _ => iprop(□ Nx r.2.2)
  | none => iprop(⌜Fr⌝)

instance twFacts_persistent (Nx : mvcc.Log → IProp GF) (Fr : Prop) (r : TWRec) :
    Persistent (twFacts Nx Fr r) := by
  unfold twFacts; split <;> infer_instance

/-- An anchor's facts: the lessor's snapshot at its index has its log's items, its log committed. -/
def ancFacts (Nx : mvcc.Log → IProp GF) (γl : GName) (a : TARec) : IProp GF :=
  iprop(∃ σ : lease.LSnap, lessorAt γl a.2.1 σ ∗ ⌜σ.2.1 = itemsOfLog a.2.2⌝ ∗ □ Nx a.2.2)

instance ancFacts_persistent (Nx : mvcc.Log → IProp GF) (γl : GName) (a : TARec) :
    Persistent (ancFacts Nx γl a) := by
  unfold ancFacts; infer_instance

/-- **The tie's body.** -/
def winTieBody (Nx : mvcc.Log → IProp GF) (Fr : Prop) (γl : GName) (γs : KVSNames) (γt : WTNames) : IProp GF :=
  iprop(∃ (ws : List LWinRec) (log : mvcc.Log) (p : Option (List mvcc.Change)) (tw : List TWRec)
      (anc : List TARec),
    lessorWinTie γl ws ∗ ghostVar γt.w (1 : Qp).half (lastWin ws) ∗
    ghostVar γs.st (1 : Qp).half.half (log, p) ∗ monoListAuthOwn γt.t 1 tw ∗ monoListAuthOwn γt.a 1 anc ∗
    ([∗list] r ∈ tw, twFacts Nx Fr r) ∗ ([∗list] a ∈ anc, ancFacts Nx γl a) ∗ ⌜tieOk ws log tw anc⌝)

/-- **The tie** (persistent). -/
def winTieInv (Nx : mvcc.Log → IProp GF) (Fr : Prop) (γl : GName) (γs : KVSNames) (γt : WTNames) : IProp GF :=
  inv winTieN (winTieBody Nx Fr γl γs γt)

instance winTieInv_persistent (Nx : mvcc.Log → IProp GF) (Fr : Prop) (γl : GName) (γs : KVSNames)
    (γt : WTNames) : Persistent (winTieInv Nx Fr γl γs γt) := by
  unfold winTieInv; infer_instance

/-- **The apply thread's window token** at the open window `w`. -/
def winTok (γt : WTNames) (w : Option LWin) : IProp GF := ghostVar γt.w (1 : Qp).half w

end defs

/-! ## Namespaces -/

/-- The tie's namespace inside the store's AUs' mask, outside the store invariant's. -/
theorem winTieN_mask : (↑winTieN : CoPset) ⊆ (⊤ \ ↑mvccN) \ ↑kvsN :=
  mask_ndot_ne2 nroot "server_lessor_win" "mvcc" "server_kv_store" (by decide) (by decide)

theorem winTieN_kvsN : (↑winTieN : CoPset) ⊆ ⊤ \ ↑kvsN :=
  mask_ndot_ne' nroot "server_lessor_win" "server_kv_store" (by decide)

/-! ## The laws -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable (Nx : mvcc.Log → IProp GF) (Cp : Int → IProp GF)
variable [hNxP : ∀ l, Persistent (Nx l)] [hNxT : ∀ l, Timeless (Nx l)]
variable [hCpP : ∀ c, Persistent (Cp c)] [hCpT : ∀ c, Timeless (Cp c)]

instance lessorWinTie_timeless (γl : GName) (ws : List LWinRec) :
    Timeless (lessorWinTie (GF := GF) γl ws) := by
  unfold lessorWinTie lease.lessorPinR lease.lessorPinAll; infer_instance

instance lessorAt_timeless (γl : GName) (i : Nat) (σ : lease.LSnap) :
    Timeless (lessorAt (GF := GF) γl i σ) := by
  unfold lessorAt lease.lessorPinR lease.lessorPinAll; infer_instance

instance twFacts_timeless (Fr : Prop) (r : TWRec) : Timeless (twFacts Nx Fr r) := by
  unfold twFacts; split <;> infer_instance

instance ancFacts_timeless (γl : GName) (a : TARec) : Timeless (ancFacts Nx γl a) := by
  unfold ancFacts; infer_instance

/-- **A commit's anchor**: in the open window `w` (the tie's), the lessor's witness gives the anchor at the committed
log; with no window, the facts stay. -/
theorem tie_anchor (γl : GName) (γt : WTNames) {ws : List LWinRec} {log : mvcc.Log} {tw : List TWRec}
    {anc : List TARec} (pend : List mvcc.Change) {w : Option LWin} (hw : lastWin ws = w)
    (hok : tieOk ws log tw anc)
    (HT : pend ≠ [] → ∀ (s : Nat) (T : GMap LeaseItem w64), w = some (s, T) →
      T = itemsOfLog (mvcc.commitLog log pend)) :
    monoListAuthOwn (GF := GF) γt.a 1 anc ∗ ([∗list] a ∈ anc, ancFacts Nx γl a) ∗
      winWit γl w (itemsOfLog (mvcc.commitLog log pend)) ∗ Nx (mvcc.commitLog log pend) ⊢
    |==> ∃ anc' : List TARec, monoListAuthOwn γt.a 1 anc' ∗ ([∗list] a ∈ anc', ancFacts Nx γl a) ∗
      ⌜tieOk ws (mvcc.commitLog log pend) tw anc'⌝ := by
  cases w with
  | none =>
    iintro ⟨Han, #Haf, -, -⟩
    imodintro
    iexists anc
    iframe Han Haf
    ipureintro
    exact tieOk_grow hok (commitLog_prefix log pend) hw
  | some v =>
    obtain ⟨s0, T0⟩ := v
    iintro ⟨Han, #Haf, #Hwit, #Hnx⟩
    iunfold winWit at Hwit
    icases Hwit with ⟨%j, %σl, #Hla, %Hj⟩
    imod monoListAuthOwn_update_app [(tw.length - 1, j, mvcc.commitLog log pend)] $$ Han
      with ⟨Han, -⟩
    imodintro
    iexists anc ++ [(tw.length - 1, j, mvcc.commitLog log pend)]
    iframe Han
    isplitl
    · iapply BigSepL.bigSepL_snoc.2
      iframe Haf
      iunfold ancFacts
      iexists σl
      iframe Hla Hnx
      ipureintro; exact Hj.2
    ipureintro
    exact tieOk_commit hok hw pend j Hj.1 (fun hp => HT hp s0 T0 rfl)

/-- **A write's end at the server** (F4: `envAus`' end builder at the apply thread's quarter `wStQ γs ¼`): both steps
open the store invariant and the tie; the notify step moves the tie's quarter of `γs.st` with the pending changes, the
commit step to the committed log, recording the commit's anchor in the open window `w` (the window token says which:
the lessor's witness `winWit` gives the anchor's snapshot). -/
theorem au_end_tie (Hp : persistent.law (GF := GF)) (kv : GoInterface) (γ : MvccName)
    (γs : KVSNames) (Fr : Prop) (γl : GName) (γt : WTNames) (log : mvcc.Log) (c : Int)
    (pend : List mvcc.Change) (w : Option LWin) :
    kvStoreInvG (GF := GF) kv γ Nx Cp γs ⊢ winTieInv Nx Fr γl γs γt -∗
      wStQ γs (1 : Qp).half.half log c -∗ winTok γt w -∗ Nx (mvcc.commitLog log pend) -∗
      ⌜pend ≠ [] → ∀ (s : Nat) (T : GMap LeaseItem w64), w = some (s, T) →
        T = itemsOfLog (mvcc.commitLog log pend)⌝ -∗
      winWit γl w (itemsOfLog (mvcc.commitLog log pend)) -∗
        auEnd γ (stAt log c) pend
          iprop(wStQ γs (1 : Qp).half.half (mvcc.commitLog log pend) c ∗ winTok γt w) := by
  haveI := fun σ => Hp.2.2.2.2.2.1 γ σ
  haveI := kvStoreInvG_persistent Hp kv γ Nx Cp γs
  iintro #Hk #Ht Hw Hwt #Hnx %HT #Hwit
  iunfold kvStoreInvG at Hk
  icases Hk with ⟨#Hm, #Hinv⟩
  iunfold winTieInv at Ht
  iunfold winTieBody at Ht
  iunfold wStQ at Hw
  icases Hw with ⟨Hw1, Hw2⟩
  iunfold winTok at Hwt
  iunfold auEnd
  iauintro
  unfold atomic_acc
  have Hdisj := kvsN_mvccN
  have Hdisj2 := winTieN_mask
  iinv Hinv with ⟨%σ, >Hs, >Hst, >Hcr, >Hsl, >Hnl, >#Hnx1, >#Hnx2, >#Hrc, >#Hco⟩ Hclose
  iinv Ht with ⟨%ws, %tl, %tp, %tw, %anc, >Hwt', >Hgw, >Hts, >Htw, >Han, >#Htf, >#Haf, >%Hok⟩ Hclose'
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ((⊤ \ ↑mvccN) \ ↑kvsN) \ ↑winTieN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  iframe Hs
  isplit
  · iintro Hs
    imod Hclose2 with -
    imod Hclose' $$ [Hwt' Hgw Hts Htw Han] with -
    · inext
      skip
      iexists ws, tl, tp, tw, anc
      iframe Hwt' Hgw Hts Htw Han Htf Haf
      ipureintro; exact Hok
    imod Hclose $$ [Hs Hst Hcr Hsl Hnl] with -
    · inext
      iexists σ
      iframe Hs Hst Hcr Hsl Hnl Hnx1 Hnx2 Hrc Hco
    imodintro
    iframe Hw1 Hw2 Hwt
  · iintro ⟨%Hσ, Hs, #Hrc'⟩
    imod Hclose2 with -
    subst Hσ
    simp only [stAt_log, stAt_crev, stAt_pending, stAt_notifiedLog]
    ihave %Hag := ghostVar_agree γs.st _ _ _ _ $$ Hw1 Hts
    simp only [Prod.mk.injEq] at Hag
    obtain ⟨rfl, rfl⟩ := Hag
    ihave Hq := (ghostVar_split_half γs.st (1 : Qp).half (log, (none : Option (List mvcc.Change)))).2 $$ [Hw1 Hts]
    · iframe
    imod ghostVar_update_halves (log, ((stAt log c).notify pend).pending) γs.st _ _ $$ Hst Hq
      with ⟨Hst, Hq⟩
    ihave ⟨Hw1, Hts⟩ := (ghostVar_split_half γs.st (1 : Qp).half _).1 $$ Hq
    imod monoListAuthOwn_update (mvcc.commitLog log pend) (commitLog_prefix log pend) $$ Hnl
      with ⟨Hnl, -⟩
    imod Hclose' $$ [Hwt' Hgw Hts Htw Han] with -
    · inext
      skip
      iexists ws, log, ((stAt log c).notify pend).pending, tw, anc
      iframe Hwt' Hgw Hts Htw Han Htf Haf
      ipureintro; exact Hok
    imod Hclose $$ [Hs Hst Hcr Hsl Hnl] with -
    · inext
      iexists (stAt log c).notify pend
      simp only [stAt_notify_log, stAt_notify_crev, stAt_notify_notifiedLog]
      iframe Hs Hst Hcr Hsl Hnl Hnx1 Hnx Hco
      rw [logCh_commitLog]
      iexact Hrc'
    imodintro
    -- the commit step
    iauintro
    unfold atomic_acc
    iinv Hinv with ⟨%σ2, >Hs, >Hst, >Hcr, >Hsl, >Hnl, >#Hnx1', >#Hnx2', >#Hrc2, >#Hco'⟩ Hclose
    iinv Ht with ⟨%ws2, %tl2, %tp2, %tw2, %anc2, >Hwt', >Hgw, >Hts, >Htw, >Han, >#Htf, >#Haf, >%Hok2⟩
      Hclose'
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ((⊤ \ ↑mvccN) \ ↑kvsN) \ ↑winTieN from
      Std.LawfulSet.empty_subset)
    iintro Hclose2
    isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
    iexists σ2
    iframe Hs
    isplit
    · iintro Hs
      imod Hclose2 with -
      imod Hclose' $$ [Hwt' Hgw Hts Htw Han] with -
      · inext
        skip
        iexists ws2, tl2, tp2, tw2, anc2
        iframe Hwt' Hgw Hts Htw Han Htf Haf
        ipureintro; exact Hok2
      imod Hclose $$ [Hs Hst Hcr Hsl Hnl] with -
      · inext
        iexists σ2
        iframe Hs Hst Hcr Hsl Hnl Hnx1' Hnx2' Hrc2 Hco'
      imodintro
      iframe Hw1 Hw2 Hwt
    · iintro ⟨%Hσ2, Hs⟩
      imod Hclose2 with -
      subst Hσ2
      simp only [stAt_notify_log, stAt_notify_crev, stAt_notify_notifiedLog, stAt_notify_commit]
      ihave %Hag := ghostVar_agree γs.st _ _ _ _ $$ Hw1 Hts
      simp only [Prod.mk.injEq] at Hag
      obtain ⟨rfl, rfl⟩ := Hag
      ihave Hq := (ghostVar_split_half γs.st (1 : Qp).half _).2 $$ [Hw1 Hts]
      · iframe
      imod ghostVar_update_halves (mvcc.commitLog log pend, (none : Option (List mvcc.Change)))
        γs.st _ _ $$ Hst Hq with ⟨Hst, Hq⟩
      ihave ⟨Hw1, Hts⟩ := (ghostVar_split_half γs.st (1 : Qp).half _).1 $$ Hq
      imod monoListAuthOwn_update (mvcc.commitLog log pend) (commitLog_prefix log pend) $$ Hsl
        with ⟨Hsl, -⟩
      ihave %Hwa := ghostVar_agree γt.w _ _ _ _ $$ Hwt Hgw
      -- the tie: an anchor in the open window
      imod (tie_anchor Nx γl γt pend Hwa.symm Hok2 HT) $$ [Han Hwit Hnx] with ⟨%anc', Han, #Haf', %Hok'⟩
      · iframe Han Haf Hwit Hnx
      imod Hclose' $$ [Hwt' Hgw Hts Htw Han] with -
      · inext
        iexists ws2, mvcc.commitLog log pend, (none : Option (List mvcc.Change)), tw2, anc'
        iframe Hwt' Hgw Hts Htw Han Htf Haf'
        ipureintro; exact Hok'
      imod Hclose $$ [Hs Hst Hcr Hsl Hnl] with -
      · inext
        iexists stAt (mvcc.commitLog log pend) c
        simp only [stAt_log, stAt_crev, stAt_pending, stAt_notifiedLog]
        iframe Hs Hst Hcr Hsl Hnl Hnx Hrc2 Hco'
      imodintro
      iunfold wStQ
      iunfold winTok
      iframe Hw1 Hw2 Hwt

/-- The lessor's reader namespace is outside the tie's. -/
theorem lessorRdN_winTieN : (↑lease.lessorRdN : CoPset) ⊆ ⊤ \ ↑winTieN :=
  mask_ndot_ne' nroot "lessor_rd" "server_lessor_win" (by decide)

/-- `lease.win_push` with the new window's option spelled out. -/
theorem win_push_some (γl : GName) (L : List w64) (I : GMap LeaseItem w64) (w : Option LWin)
    (ws : List LWinRec) (T : GMap LeaseItem w64) (E : CoPset) (hE : ↑lease.lessorRdN ⊆ E) :
    lease.lessorRdInv (GF := GF) γl ∗ lease.leaseOwnW γl L I w ∗ lessorWinTie γl ws ⊢
    |={E}=> ∃ (s : Nat) (σ : lease.LSnap), ⌜σ.2.1 = I ∧ lastWin ws = w⌝ ∗ lessorAt γl s σ ∗
      lease.leaseOwnW γl L I (some (s, T)) ∗ lessorWinTie γl (ws ++ [(s, some T)]) :=
  lease.win_push γl L I w ws (some T) E hE

/-- `lease.win_push` for a free marker. -/
theorem win_push_none (γl : GName) (L : List w64) (I : GMap LeaseItem w64) (w : Option LWin)
    (ws : List LWinRec) (E : CoPset) (hE : ↑lease.lessorRdN ⊆ E) :
    lease.lessorRdInv (GF := GF) γl ∗ lease.leaseOwnW γl L I w ∗ lessorWinTie γl ws ⊢
    |={E}=> ∃ (s : Nat) (σ : lease.LSnap), ⌜σ.2.1 = I ∧ lastWin ws = w⌝ ∗ lessorAt γl s σ ∗
      lease.leaseOwnW γl L I none ∗ lessorWinTie γl (ws ++ [(s, none)]) :=
  lease.win_push γl L I w ws none E hE

/-- **A restore at the server** (F4: the snapshot path's builder at the apply thread's quarter), in a free window (the
token at `none`): both the store invariant's and the tie's parts of `γs.st` move to the restored log (an extension,
so the tie's facts stay). -/
theorem au_restore_tie (Hp : persistent.law (GF := GF)) (kv : GoInterface) (γ : MvccName)
    (γs : KVSNames) (Fr : Prop) (γl : GName) (γt : WTNames) (log log' : mvcc.Log) (c c' : Int)
    (hl : log <+: log') (hc : c ≤ c') :
    kvStoreInvG (GF := GF) kv γ Nx Cp γs ⊢ winTieInv Nx Fr γl γs γt -∗
      wStQ γs (1 : Qp).half.half log c -∗ crOwn γs c -∗ winTok γt none -∗ Nx log' -∗ Cp c' -∗
        auRestore γ (stAt log' c') (fun σ => iprop(⌜σ = stAt log c⌝ ∗
          wStQ γs (1 : Qp).half.half log' c' ∗ crOwn γs c' ∗ winTok γt none)) := by
  haveI := fun σ => Hp.2.2.2.2.2.1 γ σ
  haveI := kvStoreInvG_persistent Hp kv γ Nx Cp γs
  iintro #Hk #Ht Hw Hc Hwt #Hnx #Hcp
  iunfold kvStoreInvG at Hk
  icases Hk with ⟨#Hm, #Hinv⟩
  iunfold winTieInv at Ht
  iunfold winTieBody at Ht
  iunfold wStQ at Hw
  icases Hw with ⟨Hw1, Hw2⟩
  iunfold crOwn at Hc
  iunfold winTok at Hwt
  iunfold auRestore
  iauintro
  unfold atomic_acc
  have Hdisj := kvsN_mvccN
  have Hdisj2 := winTieN_mask
  iinv Hinv with ⟨%σ, >Hs, >Hst, >Hcr, >Hsl, >Hnl, >#Hnx1, >#Hnx2, >#Hrc, >#Hco⟩ Hclose
  iinv Ht with ⟨%ws, %tl, %tp, %tw, %anc, >Hwt', >Hgw, >Hts, >Htw, >Han, >#Htf, >#Haf, >%Hok⟩ Hclose'
  icombine Hst Hw1 gives %H1
  icombine Hcr Hw2 gives %H2
  have Hσ := stAt_of σ log c H1.2 H2.2
  subst Hσ
  simp only [stAt_log, stAt_crev, stAt_pending, stAt_notifiedLog]
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ((⊤ \ ↑mvccN) \ ↑kvsN) \ ↑winTieN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists stAt log c
  isplitl [Hs]
  · iframe Hs; ipureintro; exact ⟨hl, hc⟩
  isplit
  · iintro ⟨Hs, -⟩
    imod Hclose2 with -
    imod Hclose' $$ [Hwt' Hgw Hts Htw Han] with -
    · inext
      iexists ws, tl, tp, tw, anc
      iframe Hwt' Hgw Hts Htw Han Htf Haf
      ipureintro; exact Hok
    imod Hclose $$ [Hs Hst Hcr Hsl Hnl] with -
    · inext
      iexists stAt log c
      simp only [stAt_log, stAt_crev, stAt_pending, stAt_notifiedLog]
      iframe Hs Hst Hcr Hsl Hnl Hnx1 Hrc Hco
    imodintro
    iframe Hw1 Hw2 Hc Hwt
  · iintro ⟨Hs, #Hrc'⟩
    imod Hclose2 with -
    ihave %Hag := ghostVar_agree γs.st _ _ _ _ $$ Hw1 Hts
    simp only [Prod.mk.injEq] at Hag
    obtain ⟨rfl, rfl⟩ := Hag
    ihave %Hwa := ghostVar_agree γt.w _ _ _ _ $$ Hwt Hgw
    ihave Hq := (ghostVar_split_half γs.st (1 : Qp).half _).2 $$ [Hw1 Hts]
    · iframe
    imod ghostVar_update_halves (log', (none : Option (List mvcc.Change))) γs.st _ _ $$ Hst Hq
      with ⟨Hst, Hq⟩
    ihave ⟨Hw1, Hts⟩ := (ghostVar_split_half γs.st (1 : Qp).half _).1 $$ Hq
    icombine Hw2 Hc as Hq2
    imod ghostVar_update_halves c' γs.cr _ _ $$ Hcr Hq2 with ⟨Hcr, Hq2⟩
    ihave ⟨Hw2, Hc⟩ := (ghostVar_split_half γs.cr (1 : Qp).half c').1 $$ Hq2
    imod monoListAuthOwn_update log' hl $$ Hsl with ⟨Hsl, -⟩
    imod monoListAuthOwn_update log' hl $$ Hnl with ⟨Hnl, -⟩
    imod Hclose' $$ [Hwt' Hgw Hts Htw Han] with -
    · inext
      iexists ws, log', (none : Option (List mvcc.Change)), tw, anc
      iframe Hwt' Hgw Hts Htw Han Htf Haf
      ipureintro; exact tieOk_grow Hok hl Hwa.symm
    imod Hclose $$ [Hs Hst Hcr Hsl Hnl] with -
    · inext
      iexists stAt log' c'
      simp only [stAt_log, stAt_crev, stAt_pending, stAt_notifiedLog]
      iframe Hs Hst Hcr Hsl Hnl Hnx Hrc' Hcp
    imodintro
    isplitr
    · ipureintro; rfl
    iunfold wStQ
    iunfold crOwn
    iunfold winTok
    iframe Hw1 Hw2 Hc Hwt

/-- **A window's push** (F4, per entry): the owner opens the window `(s, T)` at the lessor's last index `s`, whose
snapshot has the owner's items, the items of the store's log `log` (the apply thread's quarter says it is the store's);
`T` the items of the model log `Lt` after the entry, committed (`□ Nx Lt`), extending `log`. The tie records the window
and its start anchor. -/
theorem tie_push (Fr : Prop) (γl : GName) (γs : KVSNames) (γt : WTNames) (L : List w64)
    (w : Option LWin) (log Lt : mvcc.Log) (c : Int) (T : GMap LeaseItem w64)
    (hlt : log <+: Lt) (hT : T = itemsOfLog Lt) :
    winTieInv (GF := GF) Nx Fr γl γs γt ∗ lease.lessorRdInv γl ∗ lease.leaseOwnW γl L (itemsOfLog log) w ∗
      winTok γt w ∗ wStQ γs (1 : Qp).half.half log c ∗ □ Nx log ∗ □ Nx Lt ={⊤}=∗
    ∃ s : Nat, lease.leaseOwnW γl L (itemsOfLog log) (some (s, T)) ∗ winTok γt (some (s, T)) ∗
      wStQ γs (1 : Qp).half.half log c := by
  iintro ⟨#Ht, #Hl, Ho, Hwt, Hw, #Hnl, #Hnx⟩
  iunfold winTieInv at Ht
  iunfold winTieBody at Ht
  iunfold wStQ at Hw
  icases Hw with ⟨Hw1, Hw2⟩
  iunfold winTok at Hwt
  iinv Ht with ⟨%ws, %tl, %tp, %tw, %anc, >Hwt', >Hgw, >Hts, >Htw, >Han, >#Htf, >#Haf, >%Hok⟩ Hclose'
  ihave %Hag := ghostVar_agree γs.st _ _ _ _ $$ Hw1 Hts
  simp only [Prod.mk.injEq] at Hag
  obtain ⟨rfl, rfl⟩ := Hag
  imod (win_push_some γl L (itemsOfLog log) w ws T (⊤ \ ↑winTieN) lessorRdN_winTieN) $$ [Hl Ho Hwt']
    with ⟨%s, %σ, %Hσ, #Has, Ho, Hwt'⟩
  · iframe Hl Ho Hwt'
  ihave %Hwa := ghostVar_agree γt.w _ _ _ _ $$ Hwt Hgw
  imod ghostVar_update_halves (some (s, T) : Option LWin) γt.w _ _ $$ Hwt Hgw with ⟨Hwt, Hgw⟩
  imod monoListAuthOwn_update_app [(s, some T, Lt)] $$ Htw with ⟨Htw, -⟩
  imod monoListAuthOwn_update_app [(tw.length, s, log)] $$ Han with ⟨Han, -⟩
  imod Hclose' $$ [Hwt' Hgw Hts Htw Han] with -
  · inext
    iexists ws ++ [(s, some T)], log, (none : Option (List mvcc.Change)), tw ++ [(s, some T, Lt)],
      anc ++ [(tw.length, s, log)]
    rw [show lastWin (ws ++ [(s, some T)]) = some (s, T) by simp [lastWin]]
    iframe Hwt' Hgw Hts Htw Han
    isplitl
    · iapply BigSepL.bigSepL_snoc.2
      iframe Htf
      iunfold twFacts
      simp only
      iexact Hnx
    isplitl
    · iapply BigSepL.bigSepL_snoc.2
      iframe Haf
      iunfold ancFacts
      simp only
      iexists σ
      iframe Has Hnl
      ipureintro; exact Hσ.1
    ipureintro; exact tieOk_push Hok s T Lt hlt hT
  imodintro
  iexists s
  iunfold winTok
  iunfold wStQ
  iframe Ho Hwt Hw1 Hw2

/-- **A free marker's push** (F4: the snapshot path, before the lessor's `Recover`): the owner drops its window; the
marker carries the fact `Fr` (the server's: not in the no-snapshot mode). -/
theorem tie_free (Fr : Prop) (hFr : Fr) (γl : GName) (γs : KVSNames) (γt : WTNames) (L : List w64)
    (I : GMap LeaseItem w64) (w : Option LWin) :
    winTieInv (GF := GF) Nx Fr γl γs γt ∗ lease.lessorRdInv γl ∗ lease.leaseOwnW γl L I w ∗
      winTok γt w ={⊤}=∗ lease.leaseOwnW γl L I none ∗ winTok γt none := by
  iintro ⟨#Ht, #Hl, Ho, Hwt⟩
  iunfold winTieInv at Ht
  iunfold winTieBody at Ht
  iunfold winTok at Hwt
  iinv Ht with ⟨%ws, %tl, %tp, %tw, %anc, >Hwt', >Hgw, >Hts, >Htw, >Han, >#Htf, >#Haf, >%Hok⟩ Hclose'
  imod (win_push_none γl L I w ws (⊤ \ ↑winTieN) lessorRdN_winTieN) $$ [Hl Ho Hwt']
    with ⟨%s, %σ, %Hσ, -, Ho, Hwt'⟩
  · iframe Hl Ho Hwt'
  imod ghostVar_update_halves (none : Option LWin) γt.w _ _ $$ Hwt Hgw with ⟨Hwt, Hgw⟩
  imod monoListAuthOwn_update_app [(s, (none : Option (GMap LeaseItem w64)), tl)] $$ Htw with ⟨Htw, -⟩
  imod Hclose' $$ [Hwt' Hgw Hts Htw Han] with -
  · inext
    iexists ws ++ [(s, none)], tl, tp, tw ++ [(s, none, tl)], anc
    rw [show lastWin (ws ++ [(s, none)]) = none by simp [lastWin]]
    iframe Hwt' Hgw Hts Htw Han Haf
    isplitl
    · iapply BigSepL.bigSepL_snoc.2
      iframe Htf
      iunfold twFacts
      simp only
      ipureintro; exact hFr
    ipureintro; exact tieOk_free Hok s tl
  imodintro
  iunfold winTok
  iframe Ho Hwt

/-- **The tie's allocation** (F4: `NewServer`, right after `NewLessor`, whose post has the tie's quarter of the
windows' list at `[]`): with a quarter of `γs.st` at the boot log `log`, the owner opens the first window `(s, T)`
(`T` the items of a committed model log `Lt` extending `log`). -/
theorem tie_alloc (Fr : Prop) (γl : GName) (γs : KVSNames) (L : List w64) (log Lt : mvcc.Log)
    (p : Option (List mvcc.Change)) (T : GMap LeaseItem w64) (hlt : log <+: Lt) (hT : T = itemsOfLog Lt) :
    lease.lessorRdInv (GF := GF) γl ∗ lessorWinTie γl [] ∗ lease.leaseOwnW γl L (itemsOfLog log) none ∗
      ghostVar γs.st (1 : Qp).half.half (log, p) ∗ □ Nx log ∗ □ Nx Lt ={⊤}=∗
    ∃ (γt : WTNames) (s : Nat), winTieInv Nx Fr γl γs γt ∗
      lease.leaseOwnW γl L (itemsOfLog log) (some (s, T)) ∗ winTok γt (some (s, T)) := by
  iintro ⟨#Hl, Hwt', Ho, Hts, #Hnl, #Hnx⟩
  imod (win_push_some γl L (itemsOfLog log) none [] T ⊤ (by intro _ _; exact CoPset.mem_full))
    $$ [Hl Ho Hwt'] with ⟨%s, %σ, %Hσ, #Has, Ho, Hwt'⟩
  · iframe Hl Ho Hwt'
  imod (ghostVar_alloc (GF := GF) (some (s, T) : Option LWin)) with ⟨%γw, Hg⟩
  ihave ⟨Hwt, Hgw⟩ := (ghostVar_split_half γw 1 _).1 $$ Hg
  imod (mono_list_own_alloc (GF := GF) [((s, some T, Lt) : TWRec)]) with ⟨%γtw, Htw, -⟩
  imod (mono_list_own_alloc (GF := GF) [((0, s, log) : TARec)]) with ⟨%γa, Han, -⟩
  let γt : WTNames := ⟨γw, γtw, γa⟩
  imod inv_alloc winTieN ⊤ (winTieBody Nx Fr γl γs γt) $$ [Hwt' Hgw Hts Htw Han] with #Hinv
  · inext
    iunfold winTieBody
    iexists [(s, some T)], log, p, [(s, some T, Lt)], [(0, s, log)]
    simp only [List.nil_append]
    rw [show lastWin [(s, some T)] = some (s, T) from rfl]
    iframe Hwt' Hgw Hts Htw Han
    isplitl
    · iapply BigSepL.bigSepL_singleton.2
      iunfold twFacts
      simp only
      iexact Hnx
    isplitl
    · iapply BigSepL.bigSepL_singleton.2
      iunfold ancFacts
      simp only
      iexists σ
      iframe Has Hnl
      ipureintro; exact Hσ.1
    ipureintro; exact tieOk_first log s T Lt hlt hT
  imodintro
  iexists γt, s
  iunfold winTieInv
  iunfold winTok
  iframe Hinv Ho Hwt

/-- **The law's observation** (step 7): with no window free (`¬ Fr`: a free marker carries `Fr`), the tie's records
`tw0` and anchors `anc0` now, whose last anchor `(tw0.length - 1, j0, L0)` is the open window's at the store's log
`L0`, which extends the floor `F`; the lessor's history reaches `j0`. -/
theorem tie_obs (kv : GoInterface) (γ : MvccName) (γs : KVSNames) (Fr : Prop) (hFr : ¬ Fr) (γl : GName)
    (γt : WTNames) (F : mvcc.Log) (E : CoPset) (hE1 : ↑kvsN ⊆ E) (hE2 : ↑winTieN ⊆ E \ ↑kvsN) :
    kvStoreInvG (GF := GF) kv γ Nx Cp γs ∗ winTieInv Nx Fr γl γs γt ∗ kvLogLb γs F ⊢ |={E}=>
      ∃ (tw0 : List TWRec) (anc0 : List TARec) (j0 : Nat) (L0 : mvcc.Log),
        monoListLbOwn γt.t tw0 ∗ monoListLbOwn γt.a anc0 ∗ lease.lessorLb γl j0 ∗
        ⌜anc0.getLast? = some (tw0.length - 1, j0, L0) ∧ F <+: L0 ∧ ∀ a ∈ anc0, a.1 < tw0.length⌝ := by
  iintro ⟨Hk, #Ht, #Hlb⟩
  iunfold kvStoreInvG at Hk
  icases Hk with ⟨-, #Hinv⟩
  iunfold winTieInv at Ht
  iunfold winTieBody at Ht
  iunfold kvLogLb at Hlb
  iinv Hinv with ⟨%σ, Hs, >Hst, >Hcr, >Hsl, >Hnl, >#Hnx1, >#Hnx2, >#Hrc, >#Hco⟩ Hclose
  iinv Ht with ⟨%ws, %tl, %tp, %tw, %anc, >Hwt', >Hgw, >Hts, >Htw, >Han, >#Htf, >#Haf, >%Hok⟩ Hclose'
  ihave %HF := mono_list_auth_lb_valid γs.slog 1 σ.log F $$ Hsl Hlb
  ihave %Hag := ghostVar_agree γs.st _ _ _ _ $$ Hst Hts
  simp only [Prod.mk.injEq] at Hag
  obtain ⟨hl, -⟩ := Hag
  subst hl
  rcases Option.eq_none_or_eq_some (lastWin ws) with hlw | ⟨⟨s, T⟩, hlw⟩
  · obtain ⟨s, Lt, hr⟩ := tieOk_free_last Hok hlw
    ihave Hf := BigSepL.bigSepL_lookup (Φ := fun _ r => twFacts Nx Fr r) hr $$ Htf
    iunfold twFacts at Hf
    simp only
    icases Hf with %Hf
    exact absurd Hf hFr
  · obtain ⟨j, hj⟩ := Hok.2.2.2.2.2.2 s T hlw
    ihave #Ha := BigSepL.bigSepL_mem (Φ := fun a => ancFacts Nx γl a) (List.mem_of_getLast? hj) $$ Haf
    iunfold ancFacts at Ha
    icases Ha with ⟨%σa, #Has, -, -⟩
    ihave #Hlj := lease.lessorAt_lb γl j σa $$ Has
    ihave #Htw0 := monoListLbOwn_get γt.t 1 tw $$ Htw
    ihave #Han0 := monoListLbOwn_get γt.a 1 anc $$ Han
    imod Hclose' $$ [Hwt' Hgw Hts Htw Han] with -
    · inext
      iexists ws, σ.log, tp, tw, anc
      iframe Hwt' Hgw Hts Htw Han Htf Haf
      ipureintro; exact Hok
    imod Hclose $$ [Hs Hst Hcr Hsl Hnl] with -
    · inext
      iexists σ
      iframe Hs Hst Hcr Hsl Hnl Hnx1 Hnx2 Hrc Hco
    imodintro
    iexists tw, anc, j, σ.log
    iframe Htw0 Han0 Hlj
    ipureintro
    exact ⟨hj, HF.2, tieOk_idx Hok⟩

/-- **The law at an index** (step 7): for an index `i ≥ j0` of the lessor's history (at the snapshot `σl`), from the
observation's records `tw0`/`anc0` (`tie_obs`), two committed logs `La` (extending the observation's `L0`) and `Lt`
(`La`'s extension, or of `La`'s items) such that `σl` holds every item both put on `id`, with `id` live. -/
theorem tie_law (Fr : Prop) (hFr : ¬ Fr) (γl : GName) (γs : KVSNames) (γt : WTNames) {tw0 : List TWRec}
    {anc0 : List TARec} {j0 : Nat} {L0 : mvcc.Log} (hlast : anc0.getLast? = some (tw0.length - 1, j0, L0))
    (hidx : ∀ a ∈ anc0, a.1 < tw0.length) (i : Nat) (σl : lease.LSnap) (hj0 : j0 ≤ i) (E : CoPset)
    (hE1 : ↑winTieN ⊆ E) (hE2 : ↑lease.lessorRdN ⊆ E \ ↑winTieN) :
    winTieInv (GF := GF) Nx Fr γl γs γt ∗ lease.lessorRdInv γl ∗ monoListLbOwn γt.t tw0 ∗
      monoListLbOwn γt.a anc0 ∗ lessorAt γl i σl ⊢ |={E}=>
      ∃ (La Lt : mvcc.Log), □ Nx La ∗ □ Nx Lt ∗ ⌜L0 <+: La ∧ (La <+: Lt ∨ itemsOfLog La = itemsOfLog Lt) ∧
        ∀ (it : LeaseItem) (id : w64), (itemsOfLog La).lookup it = some id →
          (itemsOfLog Lt).lookup it = some id → σl.2.1.lookup it = some id ∧ (σl.1.lookup id).isSome⌝ := by
  iintro ⟨#Ht, #Hl, #Htw0, #Han0, #Hi⟩
  iunfold winTieInv at Ht
  iunfold winTieBody at Ht
  iunfold lease.lessorRdInv at Hl
  icases Hl with ⟨%γr, #Hpr, #Hinv⟩
  iinv Ht with ⟨%ws, %tl, %tp, %tw, %anc, >Hwt', >Hgw, >Hts, >Htw, >Han, >#Htf, >#Haf, >%Hok⟩ Hclose'
  ihave %Htw := mono_list_auth_lb_valid γt.t 1 tw tw0 $$ Htw Htw0
  ihave %Han := mono_list_auth_lb_valid γt.a 1 anc anc0 $$ Han Han0
  iinv Hinv with Hb Hclose
  iunfold lease.lessorRdBody at Hb
  icases Hb with ⟨%hs, %Sm, >Hh, HS, Hok1, Hmono, HU, Htie, Hids, >HW, HQ⟩
  iunfold lease.lessorWinBody at HW
  icases HW with ⟨%ws1, Hwi, %HWok⟩
  iunfold lessorWinTie at Hwt'
  icases Hwt' with ⟨%γr2, #Hpr2, Hwt'⟩
  ihave %H2 := lease.lessorPinR_agree γl γr γr2 $$ [$Hpr $Hpr2]
  subst H2
  ihave %Hag := monoListAuthOwn_agree γr.2.2.2.2.2.1 _ _ ws1 ws $$ Hwi Hwt'
  obtain ⟨-, Hag⟩ := Hag
  subst ws1
  iunfold lessorAt at Hi
  icases Hi with ⟨%γr3, #Hpr3, #Hidx⟩
  ihave %H3 := lease.lessorPinR_agree γl γr γr3 $$ [$Hpr $Hpr3]
  subst H3
  ihave %hi := mono_list_auth_idx_lookup γr.1 _ hs i σl $$ Hh Hidx
  obtain ⟨n, s, x, Lt, hr, hpick⟩ := tie_pick Hok HWok.1 Htw.2 Han.2 hlast hidx hi hj0
  ihave #Hf := BigSepL.bigSepL_lookup (Φ := fun _ r => twFacts Nx Fr r) hr $$ Htf
  iunfold twFacts at Hf
  cases x with
  | none =>
    simp only
    icases Hf with %Hf
    exact absurd Hf hFr
  | some T =>
    simp only
    obtain ⟨ja, La, hmem, hL0, -, hor, hst⟩ := hpick T rfl
    obtain ⟨hT, -⟩ := Hok.2.2.2.1 n s T Lt hr
    ihave #Ha := BigSepL.bigSepL_mem (Φ := fun a => ancFacts Nx γl a) hmem $$ Haf
    iunfold ancFacts at Ha
    simp only
    icases Ha with ⟨%σa, #Has, %HaI, #HnA⟩
    iunfold lessorAt at Has
    icases Has with ⟨%γr4, #Hpr4, #Hidx4⟩
    ihave %H4 := lease.lessorPinR_agree γl γr γr4 $$ [$Hpr $Hpr4]
    subst H4
    ihave %ha := mono_list_auth_idx_lookup γr.1 _ hs ja σa $$ Hh Hidx4
    have hlive : lease.itemsLive σl := HWok.2 σl (List.mem_of_getElem? hi)
    imod Hclose $$ [Hh HS Hok1 Hmono HU Htie Hids HQ Hwi] with -
    · inext; iunfold lease.lessorRdBody; iexists hs, Sm; iframe Hh HS Hok1 Hmono HU Htie Hids HQ
      iunfold lease.lessorWinBody
      iexists ws; iframe Hwi
      ipureintro; exact HWok
    imod Hclose' $$ [Hwt' Hgw Hts Htw Han] with -
    · inext
      iexists ws, tl, tp, tw, anc
      iframe Hgw Hts Htw Han Htf Haf
      isplitl [Hwt']
      · iunfold lessorWinTie; iexists γr; iframe Hpr Hwt'
      ipureintro; exact Hok
    imodintro
    iexists La, Lt
    iframe HnA Hf
    ipureintro
    refine ⟨hL0, ?_, tie_holds ha HaI hst hi hT hlive⟩
    rcases hor with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans hT)

end laws

end srvApi
end EtcdGrove
end Perennial
