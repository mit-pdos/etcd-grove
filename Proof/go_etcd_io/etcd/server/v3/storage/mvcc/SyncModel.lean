/-
The sync machinery's model (pure): what a range read of the bucket of a well-formed log returns
(`bucketRange_logEnts`: the entries of the revisions in the range, in revision order, since a
revision's bytes are big-endian), that they are the log's events (`logEnts_events`), and what
`newWatcherBatch` makes of them for one member (`memberBatch_logEvents`: the range's events from
its `minRev`, all of them or, past the cap of `watchBatchMaxRevs` revisions, those below the
first revision left out). Lean-first; see `InvWatchSync.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchSync

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

/-- Big-endian value of a byte list. -/
def beVal : List w8 → Nat
  | [] => 0
  | a :: xs => a.toNat * 256 ^ xs.length + beVal xs

theorem beVal_lt (l : List w8) : beVal l < 256 ^ l.length := by
  induction l with
  | nil => simp [beVal]
  | cons a xs ih =>
    simp only [beVal, List.length_cons, Nat.pow_succ]
    have ha : a.toNat < 256 := a.isLt
    have : a.toNat * 256 ^ xs.length + beVal xs < (a.toNat + 1) * 256 ^ xs.length := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    calc _ < (a.toNat + 1) * 256 ^ xs.length := this
      _ ≤ 256 * 256 ^ xs.length := Nat.mul_le_mul_right _ (by omega)
      _ = 256 ^ xs.length * 256 := Nat.mul_comm _ _

theorem combine_append_single (l : List w8) (b : w8) :
    LittleEndian.combine (l ++ [b]) = LittleEndian.combine l + b.toNat * 256 ^ l.length := by
  induction l with
  | nil => simp [LittleEndian.combine]
  | cons a xs ih =>
    simp only [List.cons_append, LittleEndian.combine, ih, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_add]
    have : 256 * (b.toNat * 256 ^ xs.length) = b.toNat * (256 ^ xs.length * 256) := by
      rw [Nat.mul_comm (256 ^ xs.length) 256, ← Nat.mul_assoc, Nat.mul_comm 256 b.toNat, Nat.mul_assoc]
    omega

theorem combine_reverse (l : List w8) : LittleEndian.combine l.reverse = beVal l := by
  induction l with
  | nil => rfl
  | cons a xs ih =>
    rw [List.reverse_cons, combine_append_single, ih, List.length_reverse, beVal]; omega

theorem lex_of_beVal_lt : ∀ (x y : List w8), x.length = y.length → beVal x < beVal y →
    go.GoStringLt x y
  | [], [], _, h => by simp [beVal] at h
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | a :: xs, b :: ys, hl, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    simp only [beVal] at h
    have hx := beVal_lt xs
    have hy := beVal_lt ys
    rw [← hl] at h hy
    by_cases hab : a.toNat < b.toNat
    · exact List.Lex.rel (by simpa [uint.Z] using hab)
    · by_cases hba : b.toNat < a.toNat
      · exfalso
        have : (b.toNat + 1) * 256 ^ xs.length ≤ a.toNat * 256 ^ xs.length :=
          Nat.mul_le_mul_right _ hba
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      · have hab' : a = b := BitVec.eq_of_toNat_eq (by omega)
        subst hab'
        exact List.Lex.cons (lex_of_beVal_lt xs ys hl (by omega))

theorem beVal_u64Be (x : w64) : beVal (u64Be x) = x.toNat := by
  rw [← combine_reverse]
  simp only [u64Be, List.reverse_reverse, u64Le, u64LeDef, LittleEndian.combine_split]
  have := x.isLt; omega

/-- `u64Be` (8 big-endian bytes) is monotone in the unsigned value, lexicographically. -/
theorem u64Be_lt {a b : w64} (h : uint.Z a < uint.Z b) : go.GoStringLt (u64Be a) (u64Be b) := by
  apply lex_of_beVal_lt _ _ (by simp [u64Be_length])
  rw [beVal_u64Be, beVal_u64Be]
  have : uint.Z a = a.toNat := rfl
  have : uint.Z b = b.toNat := rfl
  omega


/-! ## A change's key-value -/

theorem take_succ_getElem {α : Type} (l : List α) (i : Nat) (a : α) (h : l[i]? = some a) :
    l.take (i + 1) = l.take i ++ [a] := by
  rw [List.take_add_one, h]; rfl

/-- What a change writes: a delete's key alone, or a put's key-value modified at `r`, created at
the key's previous create revision or at `r`. -/
theorem changeKv_cases (r : w64) (b : List EtcdKv) (hb : b.Pairwise etcdKvLess) (cs : List Change)
    (i : Nat) (kv : EtcdKv) (h : changeKv r b cs i = some kv) :
    (∃ k, cs[i]? = some (.del k) ∧ kv = zeroKv k) ∨
    (∃ k v l, cs[i]? = some (.put k v l) ∧ kv.modRev = r ∧
      kv.createRev = ((findKey k (applyChanges r b (cs.take i))).map EtcdKv.createRev).getD r) := by
  unfold changeKv at h
  cases hc : cs[i]? with
  | none => rw [hc] at h; cases h
  | some c =>
    rw [hc] at h
    cases c with
    | del k => left; exact ⟨k, rfl, (Option.some.inj h).symm⟩
    | put k v l =>
      right
      simp only at h
      rw [take_succ_getElem cs i _ hc, applyChanges_append_singleton] at h
      simp only [applyChange] at h
      obtain ⟨nv, hnv, -, hmod, hcr, -⟩ :=
        findKey_putKv_self (applyChanges_sorted r (cs.take i) hb) r k v l
      rw [hnv] at h
      cases h
      exact ⟨k, v, l, rfl, hmod, hcr⟩

/-- The events of a revision are at that revision. -/
theorem evsOfRevM_modRev_sm (m : Nat) (b : List EtcdKv) (hb : b.Pairwise etcdKvLess)
    (cs : List Change) : ∀ ev ∈ evsOfRevM m b cs, ev.kv.modRev = W64 m := by
  intro ev hev
  unfold evsOfRevM at hev
  rw [List.mem_filterMap] at hev
  obtain ⟨i, -, hi⟩ := hev
  cases hk : changeKv (W64 m) b cs i with
  | none => rw [hk] at hi; cases hi
  | some kv =>
    rw [hk] at hi
    simp only [Option.map_some, Option.some.injEq] at hi
    subst hi
    unfold evOfKv
    split
    · rfl
    · rcases changeKv_cases _ b hb cs i kv hk with ⟨k, -, rfl⟩ | ⟨k, v, l, -, hmod, -⟩
      · rename_i h; exact absurd rfl h
      · exact hmod

theorem mem_logEvents (log : Log) (a b : Nat) (ev : EvM) :
    ev ∈ logEvents log a b ↔ ∃ j, a ≤ j ∧ j < b ∧
      ev ∈ evsOfRevM j (stateAt log (j - 1)) (log.getD j []) := by
  unfold logEvents
  simp only [List.mem_flatten, List.mem_map, List.mem_range']
  constructor
  · rintro ⟨l, ⟨j, ⟨k, hk, rfl⟩, rfl⟩, hev⟩
    exact ⟨a + 1 * k, by omega, by omega, hev⟩
  · rintro ⟨j, h1, h2, hev⟩
    exact ⟨_, ⟨j, ⟨j - a, by omega, by omega⟩, rfl⟩, hev⟩

theorem evsOfRevM_nil (m : Nat) (b : List EtcdKv) : evsOfRevM m b [] = [] := rfl

/-- The events of `logEvents` are at their revision, one of the log's. -/
theorem logEvents_rev (log : Log) (a b : Nat) :
    ∀ ev ∈ logEvents log a b, ∃ j, a ≤ j ∧ j < b ∧ j < log.length ∧ ev.kv.modRev = W64 j := by
  intro ev hev
  obtain ⟨j, h1, h2, hev⟩ := (mem_logEvents log a b ev).1 hev
  by_cases hj : j < log.length
  · exact ⟨j, h1, h2, hj, evsOfRevM_modRev_sm j _ (stateAt_sorted _ _) _ ev hev⟩
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hev
    simp [evsOfRevM_nil] at hev

/-- The events of the revisions `[a, b)` of a log are at those revisions. -/
theorem watchEvents_modRev (L : Log) (hlen : L.length < 2 ^ 63) (r : WatchRange) (a b : Nat)
    (hb : b ≤ L.length) :
    ∀ ev ∈ watchEvents L r a b, (a : Int) ≤ sint.Z ev.kv.modRev ∧ sint.Z ev.kv.modRev < b := by
  intro ev hev
  unfold watchEvents at hev
  obtain ⟨j, h1, h2, h3, hm⟩ := logEvents_rev L a b ev (List.mem_filter.1 hev).1
  rw [hm]
  have : sint.Z (W64 (j : Int)) = j := by word
  omega

/-! ## The batches of the range's events -/

/-- `newWatcherBatch`'s fold for one member, over the events it gets. -/
def ebFold (F : List EvM) : Option EventBatch :=
  F.foldl (fun ob ev => some (ebAdd (ob.getD .empty) ev)) none

theorem foldl_ite_filter {α β : Type} (q : α → Bool) (g : β → α → β) :
    ∀ (l : List α) (init : β),
      l.foldl (fun ob a => if q a then g ob a else ob) init = (l.filter q).foldl g init
  | [], _ => rfl
  | a :: l, init => by
    rw [List.foldl_cons, List.filter_cons]
    by_cases h : q a
    · simp only [h, ↓reduceIte, List.foldl_cons]; exact foldl_ite_filter q g l _
    · simp only [h, Bool.false_eq_true, ↓reduceIte]; exact foldl_ite_filter q g l _

theorem memberBatch_eq (r : WatchRange) (st : WatcherSt) (evs : List EvM) :
    memberBatch r st evs = ebFold (evs.filter fun ev =>
      r.covers ev.kv.key && decide (sint.Z st.minRev ≤ sint.Z ev.kv.modRev)) := by
  unfold memberBatch ebFold
  exact foldl_ite_filter _ (fun ob ev => some (ebAdd (ob.getD .empty) ev)) evs none

/-- What the fold keeps of the events `P` so far (sorted by revision): all of them, with
`moreRev = 0` and at most the cap of revisions; or, past the cap, those below the first
revision left out, `moreRev`, the revision of one of them above the first. -/
def ebInv (P : List EvM) (B : EventBatch) : Prop :=
  (B.moreRev = W64 0 ∧ B.evs = P ∧ 1 ≤ sint.Z B.revs ∧ sint.Z B.revs ≤ 1000) ∨
  (sint.Z B.revs = 1001 ∧ B.evs ≠ [] ∧ ∃ ev ∈ P, B.moreRev = ev.kv.modRev ∧
    (∀ h, P.head? = some h → sint.Z h.kv.modRev < sint.Z ev.kv.modRev) ∧
    B.evs = P.filter fun e => decide (sint.Z e.kv.modRev < sint.Z ev.kv.modRev))

abbrev RevSorted (P : List EvM) : Prop :=
  P.Pairwise fun a b => sint.Z a.kv.modRev ≤ sint.Z b.kv.modRev

theorem ebInv_single (x : EvM) : ebInv [x] (ebAdd .empty x) := by
  have h : ebAdd .empty x = ⟨[x], W64 1, W64 0⟩ := by
    unfold ebAdd EventBatch.empty
    rw [if_neg (by decide)]; rfl
  rw [h]; left
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> dsimp only <;> decide

theorem ebInv_snoc (P : List EvM) (x : EvM) (B : EventBatch) (hP : P ≠ [])
    (hs : RevSorted (P ++ [x])) (h : ebInv P B) : ebInv (P ++ [x]) (ebAdd B x) := by
  have hle : ∀ e ∈ P, sint.Z e.kv.modRev ≤ sint.Z x.kv.modRev := by
    intro e he
    exact List.pairwise_append.1 hs |>.2.2 e he x (List.mem_singleton_self x)
  have hhead : (P ++ [x]).head? = P.head? := by
    cases P with
    | nil => exact absurd rfl hP
    | cons a l => rfl
  rcases h with ⟨hm, he, h1, h2⟩ | ⟨h1, hne, ev, hev, hm, hh, he⟩
  · -- not capped
    obtain ⟨last, hlast⟩ : ∃ last, P.getLast? = some last := by
      cases h : P.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.1 h) hP
      | some l => exact ⟨l, rfl⟩
    have hlastm : last ∈ P := List.mem_of_getLast? hlast
    have hcap : ¬ sint.Z watchBatchMaxRevsV < sint.Z B.revs := by
      unfold watchBatchMaxRevsV
      have : sint.Z (W64 1000 : w64) = 1000 := by decide
      omega
    have hrevs1 : sint.Z (B.revs + W64 1) = sint.Z B.revs + 1 := by word
    have hmax : sint.Z watchBatchMaxRevsV = 1000 := by decide
    unfold ebAdd
    rw [if_neg hcap, he, hlast]
    simp only
    by_cases hlt : sint.Z last.kv.modRev < sint.Z x.kv.modRev
    · rw [if_pos hlt]
      by_cases hc : sint.Z watchBatchMaxRevsV < sint.Z (B.revs + W64 1)
      · rw [if_pos hc]
        right
        dsimp only
        refine ⟨by omega, hP, x, List.mem_append_right _ (List.mem_singleton_self x),
          rfl, ?_, ?_⟩
        · intro h hh
          rw [hhead] at hh
          have hhm : h ∈ P := List.mem_of_mem_head? hh
          have := List.pairwise_append.1 hs |>.1
          -- h is the head, last is in P: h ≤ last
          have hhl : sint.Z h.kv.modRev ≤ sint.Z last.kv.modRev := by
            cases P with
            | nil => exact absurd rfl hP
            | cons a l =>
              simp only [List.head?_cons, Option.some.injEq] at hh
              subst hh
              rcases List.mem_cons.1 hlastm with h' | h'
              · rw [h']; exact Int.le_refl _
              · exact List.rel_of_pairwise_cons this h'
          omega
        · rw [List.filter_append, List.filter_eq_self.2, List.filter_eq_nil_iff.2]
          · simp
          · intro a ha; simp at ha; subst ha; simp
          · intro a ha
            have h1 := hle a ha
            -- a ≤ last
            have hal : sint.Z a.kv.modRev ≤ sint.Z last.kv.modRev := by
              have hp := List.pairwise_append.1 hs |>.1
              obtain ⟨l0, hl0⟩ := List.getLast?_eq_some_iff.1 hlast
              subst hl0
              rcases List.mem_append.1 ha with ha | ha
              · exact List.pairwise_append.1 hp |>.2.2 a ha last (List.mem_singleton_self _)
              · simp at ha; rw [ha]; exact Int.le_refl _
            simp; omega
      · rw [if_neg hc]
        left
        dsimp only
        refine ⟨hm, rfl, by omega, by omega⟩
    · rw [if_neg hlt]
      left
      dsimp only
      refine ⟨hm, rfl, h1, h2⟩
  · -- capped: nothing changes
    have hcap : sint.Z watchBatchMaxRevsV < sint.Z B.revs := by
      have : sint.Z watchBatchMaxRevsV = 1000 := by decide
      omega
    unfold ebAdd
    rw [if_pos hcap]
    right
    refine ⟨h1, hne, ev, List.mem_append_left _ hev, hm, by rw [hhead]; exact hh, ?_⟩
    rw [he, List.filter_append]
    have : ([x].filter fun e => decide (sint.Z e.kv.modRev < sint.Z ev.kv.modRev)) = [] := by
      have := hle ev hev
      simp; omega
    rw [this, List.append_nil]

theorem ebFold_spec_aux : ∀ (n : Nat) (F : List EvM), F.length = n → RevSorted F →
    (F = [] ∧ ebFold F = none) ∨ (F ≠ [] ∧ ∃ B, ebFold F = some B ∧ ebInv F B)
  | 0, F, hn, _ => by left; rw [List.length_eq_zero_iff.1 hn]; exact ⟨rfl, rfl⟩
  | n + 1, F, hn, hs => by
    right
    have hF : F ≠ [] := by intro h; rw [h] at hn; cases hn
    refine ⟨hF, ?_⟩
    rw [← List.dropLast_concat_getLast hF] at hs ⊢
    generalize F.getLast hF = x at hs ⊢
    have hlen : F.dropLast.length = n := by simp [hn]
    generalize F.dropLast = P at hs hlen ⊢
    have hsP : RevSorted P := (List.pairwise_append.1 hs).1
    unfold ebFold
    rw [List.foldl_append]
    rcases ebFold_spec_aux n P hlen hsP with ⟨rfl, -⟩ | ⟨hne, B, hB, hinv⟩
    · exact ⟨_, rfl, ebInv_single x⟩
    · unfold ebFold at hB
      rw [hB]
      exact ⟨_, rfl, ebInv_snoc P x B hne hs hinv⟩

theorem ebFold_spec (F : List EvM) (hs : RevSorted F) :
    (F = [] ∧ ebFold F = none) ∨ (F ≠ [] ∧ ∃ B, ebFold F = some B ∧ ebInv F B) :=
  ebFold_spec_aux F.length F rfl hs

/-- A revision's events, in `logEvents`, are of a revision of the log, at it. -/
theorem evsOfRevM_getD_rev (log : Log) (j : Nat) (ev : EvM)
    (hev : ev ∈ evsOfRevM j (stateAt log (j - 1)) (log.getD j [])) :
    j < log.length ∧ ev.kv.modRev = W64 j := by
  by_cases hj : j < log.length
  · exact ⟨hj, evsOfRevM_modRev_sm j _ (stateAt_sorted _ _) _ ev hev⟩
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hev
    simp [evsOfRevM_nil] at hev

/-- The log's events are in revision order. -/
theorem logEvents_sorted (log : Log) (hlen : log.length < 2 ^ 63) (a b : Nat) :
    RevSorted (logEvents log a b) := by
  unfold logEvents RevSorted
  rw [List.pairwise_flatten, List.pairwise_map]
  constructor
  · intro l hl
    rw [List.mem_map] at hl
    obtain ⟨j, -, rfl⟩ := hl
    apply List.Pairwise.imp_of_mem (R := fun _ _ => True)
    · intro x y hx hy _
      rw [(evsOfRevM_getD_rev log j x hx).2, (evsOfRevM_getD_rev log j y hy).2]
      exact Int.le_refl _
    · exact List.pairwise_of_forall (fun _ _ => trivial)
  · apply (List.pairwise_lt_range' (s := a) (n := b - a)).imp_of_mem
    intro j j' _ _ hjj x hx y hy
    have hx' := evsOfRevM_getD_rev log j x hx
    have hy' := evsOfRevM_getD_rev log j' y hy
    rw [hx'.2, hy'.2]
    have h1 : sint.Z (W64 (j : Int)) = j := by word
    have h2 : sint.Z (W64 (j' : Int)) = j' := by word
    omega

/-- **One member's batch of the range's events** (`newWatcherBatch` of `rangeEvents`' events,
filtered by a predicate `p` true of the keys the member covers), for a member at `minRev = m`
(at or above the range's start `lo`): none if the range has no event of the member from `m`, else
its events from `m`, all of them up to `hi` (no revision left out: `moreRev = 0`), or, past the
cap of `watchBatchMaxRevs` revisions, those below the first revision left out `M`
(`moreRev = M`, above `m`, below `hi`). -/
theorem memberBatch_logEvents (C : Log) (hwf : LogWf' C) (hlen : C.length < 2 ^ 63)
    (hcs : ∀ cs ∈ C, cs.length < 2 ^ 63) (r : WatchRange) (st : WatcherSt) (p : EvM → Bool)
    (lo hi : Nat) (hp : ∀ ev, r.covers ev.kv.key = true → p ev = true)
    (hlo : (lo : Int) ≤ sint.Z st.minRev) (hhi : hi ≤ C.length) :
    (memberBatch r st ((logEvents C lo hi).filter p) = none ∧
        watchEvents C r (sint.nat st.minRev) hi = []) ∨
      ∃ B : EventBatch, memberBatch r st ((logEvents C lo hi).filter p) = some B ∧ B.evs ≠ [] ∧
        ((B.moreRev = W64 0 ∧ B.evs = watchEvents C r (sint.nat st.minRev) hi) ∨
         (∃ M : Nat, B.moreRev = W64 (M : Int) ∧ sint.nat st.minRev < M ∧ M < hi ∧
            B.evs = watchEvents C r (sint.nat st.minRev) M)) := by
  have hm : sint.Z st.minRev = (sint.nat st.minRev : Int) := by
    have : sint.nat st.minRev = (sint.Z st.minRev).toNat := rfl
    omega
  generalize hmdef : sint.nat st.minRev = m at hm ⊢
  have hrev := logEvents_rev C lo hi
  -- the member's events are the range's from `m`
  have hF : ((logEvents C lo hi).filter p).filter (fun ev =>
      r.covers ev.kv.key && decide (sint.Z st.minRev ≤ sint.Z ev.kv.modRev)) =
      watchEvents C r m hi := by
    rw [List.filter_filter]
    unfold watchEvents
    by_cases hmh : hi ≤ m
    · rw [logEvents_empty C hmh]
      apply List.filter_eq_nil_iff.2
      intro ev hev
      obtain ⟨j, -, hj, hjl, hjm⟩ := hrev ev hev
      have : sint.Z ev.kv.modRev = j := by rw [hjm]; word
      simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
      intro _ _; omega
    · rw [logEvents_append C (show lo ≤ m by omega) (show m ≤ hi by omega), List.filter_append,
        List.filter_eq_nil_iff.2, List.nil_append]
      · apply List.filter_congr
        intro ev hev
        obtain ⟨j, hj1, -, hjl, hjm⟩ := logEvents_rev C m hi ev hev
        have : sint.Z ev.kv.modRev = j := by rw [hjm]; word
        have hd : decide (sint.Z st.minRev ≤ sint.Z ev.kv.modRev) = true := by
          simp only [decide_eq_true_eq]; omega
        rw [hd]
        cases hc : r.covers ev.kv.key
        · simp
        · simp [hp ev hc]
      · intro ev hev
        obtain ⟨j, -, hj, hjl, hjm⟩ := logEvents_rev C lo m ev hev
        have : sint.Z ev.kv.modRev = j := by rw [hjm]; word
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
        intro _ _; omega
  rw [memberBatch_eq, hF]
  have hsorted : RevSorted (watchEvents C r m hi) :=
    (logEvents_sorted C hlen m hi).sublist List.filter_sublist
  rcases ebFold_spec _ hsorted with ⟨he, hf⟩ | ⟨hne, B, hB, hinv⟩
  · left; exact ⟨hf, he⟩
  · right
    refine ⟨B, hB, ?_, ?_⟩
    · rcases hinv with ⟨-, he, -, -⟩ | ⟨-, hne', -⟩
      · rw [he]; exact hne
      · exact hne'
    rcases hinv with ⟨hmr, he, -, -⟩ | ⟨-, -, ev, hev, hmr, hh, he⟩
    · left; exact ⟨hmr, he⟩
    · right
      obtain ⟨hj1, hj2⟩ := watchEvents_modRev C hlen r m hi hhi ev hev
      have hev' := (List.mem_filter.1 hev).1
      obtain ⟨j, -, -, hjl, hjm⟩ := logEvents_rev C m hi ev hev'
      have hjz : sint.Z ev.kv.modRev = j := by rw [hjm]; word
      obtain ⟨h0, hh0⟩ : ∃ h0, (watchEvents C r m hi).head? = some h0 := by
        cases h : (watchEvents C r m hi).head? with
        | none => exact absurd (List.head?_eq_none_iff.1 h) hne
        | some h0 => exact ⟨h0, rfl⟩
      have hhm := watchEvents_modRev C hlen r m hi hhi h0 (List.mem_of_mem_head? hh0)
      have hlt := hh h0 hh0
      refine ⟨j, by rw [hmr, hjm], by omega, by omega, ?_⟩
      rw [he, watchEvents_append C r (show m ≤ j by omega) (show j ≤ hi by omega),
        List.filter_append, List.filter_eq_self.2, List.filter_eq_nil_iff.2, List.append_nil]
      · intro e he'
        have := watchEvents_modRev C hlen r j hi hhi e he'
        simp only [decide_eq_true_eq]; omega
      · intro e he'
        have := watchEvents_modRev C hlen r m j (by omega) e he'
        simp only [decide_eq_true_eq]; omega

/-! ## The byte order of bucket keys -/

theorem lex_append_eq_len : ∀ {x y : List w8} (s t : List w8), x.length = y.length →
    go.GoStringLt x y → go.GoStringLt (x ++ s) (y ++ t)
  | [], [], _, _, _, h => by cases h
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, _, h => by cases h
  | a :: xs, b :: ys, s, t, hl, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    cases h with
    | cons h => exact List.Lex.cons (lex_append_eq_len s t hl h)
    | rel h => exact List.Lex.rel h

theorem lex_append_left : ∀ (p : List w8) {x y : List w8}, go.GoStringLt x y →
    go.GoStringLt (p ++ x) (p ++ y)
  | [], _, _, h => h
  | _ :: p, _, _, h => List.Lex.cons (lex_append_left p h)

theorem lex_prefix : ∀ (x : List w8) (c : w8) (d : List w8), go.GoStringLt x (x ++ c :: d)
  | [], _, _ => List.Lex.nil
  | _ :: x, c, d => List.Lex.cons (lex_prefix x c d)

theorem revBytes_split (a : Rev) (t : Bool) :
    revBytes a t = u64Be a.main ++ ([W8 95] ++ u64Be a.sub ++ (if t then [W8 116] else [])) := by
  simp [revBytes]

theorem revBytes_split2 (a : Rev) (t : Bool) :
    revBytes a t = (u64Be a.main ++ [W8 95]) ++ (u64Be a.sub ++ (if t then [W8 116] else [])) := by
  simp [revBytes]

theorem revBytes_lt_main (a b : Rev) (ta tb : Bool) (h : a.main.toNat < b.main.toNat) :
    go.GoStringLt (revBytes a ta) (revBytes b tb) := by
  rw [revBytes_split, revBytes_split]
  have h1 : uint.Z a.main = a.main.toNat := rfl
  have h2 : uint.Z b.main = b.main.toNat := rfl
  exact lex_append_eq_len _ _ (by simp [u64Be_length]) (u64Be_lt (by omega))

theorem revBytes_lt_sub (a b : Rev) (ta tb : Bool) (hm : a.main = b.main)
    (h : a.sub.toNat < b.sub.toNat) : go.GoStringLt (revBytes a ta) (revBytes b tb) := by
  rw [revBytes_split2, revBytes_split2, hm]
  have h1 : uint.Z a.sub = a.sub.toNat := rfl
  have h2 : uint.Z b.sub = b.sub.toNat := rfl
  exact lex_append_left _ (lex_append_eq_len _ _ (by simp [u64Be_length]) (u64Be_lt (by omega)))

theorem revBytes_lt_tomb (a : Rev) : go.GoStringLt (revBytes a false) (revBytes a true) := by
  rw [revBytes_true]; exact lex_prefix _ _ _

theorem w64_toNat_of_lt (n : Nat) (h : n < 2 ^ 64) : (W64 (n : Int)).toNat = n := by
  have := W64_inj_of_lt (a := (W64 (n : Int)).toNat) (b := n) (by have := (W64 (n:Int)).isLt; omega) h
    (by rw [W64_toNat])
  exact this

theorem goStringLe_of_lt_not {a b : GoString} (h : go.GoStringLt b a) : ¬ go.GoStringLe a b := by
  rintro (rfl | h')
  · exact adt.strLt_irrefl _ h
  · exact adt.strLt_asymm h h'

theorem revKey_ge (lo r i : Nat) (t : Bool) (hlo : lo < 2 ^ 64) (hr : r < 2 ^ 64)
    (hi : i < 2 ^ 64) :
    go.GoStringLe (revBytes ⟨W64 lo, W64 0⟩ false) (revBytes ⟨W64 r, W64 i⟩ t) ↔ lo ≤ r := by
  constructor
  · intro h
    rcases Nat.lt_or_ge r lo with hlt | hge
    · exact absurd h (goStringLe_of_lt_not (revBytes_lt_main _ _ _ _ (by
        simp only; rw [w64_toNat_of_lt r hr, w64_toNat_of_lt lo hlo]; omega)))
    · exact hge
  · intro h
    rcases Nat.lt_or_eq_of_le h with h | rfl
    · exact Or.inr (revBytes_lt_main _ _ _ _ (by
        simp only; rw [w64_toNat_of_lt r hr, w64_toNat_of_lt lo hlo]; omega))
    · by_cases hi0 : i = 0
      · subst hi0
        cases t
        · exact Or.inl rfl
        · exact Or.inr (revBytes_lt_tomb _)
      · exact Or.inr (revBytes_lt_sub _ _ _ _ rfl (by
          simp only; rw [w64_toNat_of_lt i hi]; simp; omega))

theorem revKey_lt (r i hi : Nat) (t : Bool) (hhi : hi < 2 ^ 64) (hr : r < 2 ^ 64)
    (hi' : i < 2 ^ 64) :
    go.GoStringLt (revBytes ⟨W64 r, W64 i⟩ t) (revBytes ⟨W64 hi, W64 0⟩ false) ↔ r < hi := by
  constructor
  · intro h
    rcases Nat.lt_or_ge r hi with hlt | hge
    · exact hlt
    · exact absurd ((revKey_ge hi r i t hhi hr hi').2 hge) (goStringLe_of_lt_not h)
  · intro h
    exact revBytes_lt_main _ _ _ _ (by
      simp only; rw [w64_toNat_of_lt r hr, w64_toNat_of_lt hi hhi]; omega)

/-! ## The bucket's entries -/

theorem zipIdx_map_range {α β : Type} (l : List α) (d : α) (g : α × Nat → β) :
    l.zipIdx.map g = (List.range l.length).map fun i => g (l.getD i d, i) := by
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp only [List.getElem_map, List.getElem_zipIdx, List.getElem_range, Nat.zero_add]
  simp only [List.length_map, List.length_zipIdx] at h1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]; rfl

theorem zipIdx_filterMap_range {α β : Type} (l : List α) (d : α) (g : α × Nat → Option β) :
    l.zipIdx.filterMap g = (List.range l.length).filterMap fun i => g (l.getD i d, i) := by
  rw [show l.zipIdx.filterMap g = (l.zipIdx.map g).filterMap id by rw [List.filterMap_map]; rfl,
    zipIdx_map_range l d g, List.filterMap_map]
  rfl

theorem entsOfRev_range (r : Nat) (b : List EtcdKv) (cs : List Change) :
    entsOfRev r b cs = (List.range cs.length).filterMap fun i =>
      (changeKv (W64 r) b cs i).map fun kv => ⟨⟨W64 r, W64 i⟩, (cs.getD i (.del [])).isDel, kv⟩ :=
  zipIdx_filterMap_range cs (.del []) _

theorem mem_entsOfRev (r : Nat) (b : List EtcdKv) (cs : List Change) (e : KvEnt) :
    e ∈ entsOfRev r b cs ↔ ∃ i c kv, cs[i]? = some c ∧ changeKv (W64 r) b cs i = some kv ∧
      e = ⟨⟨W64 r, W64 i⟩, c.isDel, kv⟩ := by
  unfold entsOfRev
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨c, i⟩, hm, he⟩
    rw [List.mem_zipIdx_iff_getElem?] at hm
    simp only at he hm
    cases hk : changeKv (W64 r) b cs i with
    | none => rw [hk] at he; cases he
    | some kv =>
      rw [hk] at he
      simp only [Option.map_some, Option.some.injEq] at he
      exact ⟨i, c, kv, hm, hk, he.symm⟩
  · rintro ⟨i, c, kv, hc, hk, rfl⟩
    refine ⟨(c, i), List.mem_zipIdx_iff_getElem?.2 hc, ?_⟩
    show (changeKv (W64 r) b cs i).map _ = _
    rw [hk]; rfl

theorem mem_logEnts (log : Log) (a b : Nat) (e : KvEnt) :
    e ∈ logEnts log a b ↔ ∃ j, a ≤ j ∧ j < b ∧
      e ∈ entsOfRev j (stateAt log (j - 1)) (log.getD j []) := by
  unfold logEnts
  simp only [List.mem_flatten, List.mem_map, List.mem_range']
  constructor
  · rintro ⟨l, ⟨j, ⟨k, hk, rfl⟩, rfl⟩, hev⟩
    exact ⟨a + 1 * k, by omega, by omega, hev⟩
  · rintro ⟨j, h1, h2, hev⟩
    exact ⟨_, ⟨j, ⟨j - a, by omega, by omega⟩, rfl⟩, hev⟩

/-- An entry of `logEnts`: of a revision `j` of the log, at a change `i` of it. -/
theorem logEnts_entry (log : Log) (a b : Nat) (e : KvEnt) (he : e ∈ logEnts log a b) :
    ∃ j i c kv, a ≤ j ∧ j < b ∧ j < log.length ∧ log[j]? = some (log.getD j []) ∧
      e ∈ entsOfRev j (stateAt log (j - 1)) (log.getD j []) ∧
      (log.getD j [])[i]? = some c ∧
      changeKv (W64 j) (stateAt log (j - 1)) (log.getD j []) i = some kv ∧
      e = ⟨⟨W64 j, W64 i⟩, c.isDel, kv⟩ := by
  obtain ⟨j, h1, h2, he⟩ := (mem_logEnts log a b e).1 he
  have he' := he
  obtain ⟨i, c, kv, hc, hk, rfl⟩ := (mem_entsOfRev _ _ _ _).1 he
  have hj : j < log.length := by
    rcases Nat.lt_or_ge j log.length with hj | hj
    · exact hj
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (l := log) (by omega)] at hc
      simp at hc
  refine ⟨j, i, c, kv, h1, h2, hj, ?_, he', hc, hk, rfl⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl

/-- The entries' revisions are non-negative (what `BytesToRev` needs). -/
theorem logEnts_bounds (log : Log) (hlen : log.length < 2 ^ 63)
    (hcs : ∀ cs ∈ log, cs.length < 2 ^ 63) (lo hi : Nat) (hhi : hi ≤ log.length) :
    ∀ e ∈ logEnts log lo hi, 0 ≤ sint.Z e.rev.main ∧ 0 ≤ sint.Z e.rev.sub := by
  intro e he
  obtain ⟨j, i, c, kv, -, -, hj, hgj, -, hc, -, rfl⟩ := logEnts_entry log lo hi e he
  have hcl := hcs _ (List.mem_of_getElem? hgj)
  have hil : i < (log.getD j []).length := (List.getElem?_eq_some_iff.1 hc).1
  simp only
  constructor <;> word

theorem bucketOf_logEnts (log : Log) : bucketOf log = (logEnts log 0 log.length).map KvEnt.pair := by
  unfold bucketOf logEnts
  rw [zipIdx_map_range log [] _, List.map_flatten, List.map_map, Nat.sub_zero,
    ← List.range_eq_range']
  congr 1
  apply List.map_congr_left
  intro m _
  simp only [Function.comp_apply, bucketOfRev, entsOfRev, List.map_filterMap]
  congr 1
  funext p
  cases changeKv (W64 m) (stateAt log (m - 1)) (log.getD m []) p.2 <;> rfl

theorem bucketMap_lookup_iff (log : Log) (hlen : log.length < 2 ^ 63)
    (hcs : ∀ cs ∈ log, cs.length < 2 ^ 63) (k v : GoString) :
    bucketMap log !! k = some v ↔ (k, v) ∈ bucketOf log := by
  constructor
  · intro h
    change (bucketMap log).lookup k = some v at h
    unfold bucketMap at h
    rw [lookup_foldl_insert] at h
    cases hf : (bucketOf log).reverse.find? (fun p => decide (p.1 = k)) with
    | none => rw [hf] at h; cases h
    | some p =>
      rw [hf] at h
      cases h
      have hp := List.mem_reverse.1 (List.mem_of_find?_eq_some hf)
      have hk : p.1 = k := by simpa using List.find?_some hf
      rw [← hk]; exact hp
  · intro h
    exact bucketMap_lookup_of_mem log k v h (fun p hp hk =>
      bucketOf_fun log hlen hcs p hp (k, v) h hk)

theorem getD_len_bound (log : Log) (hcs : ∀ cs ∈ log, cs.length < 2 ^ 63) (j : Nat) :
    (log.getD j []).length < 2 ^ 63 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : log[j]? with
  | none => simp
  | some cs => exact hcs cs (List.mem_of_getElem? h)

theorem entsOfRev_main (log : Log) (j : Nat) (e : KvEnt)
    (he : e ∈ entsOfRev j (stateAt log (j - 1)) (log.getD j [])) :
    j < log.length ∧ e.rev.main = W64 j := by
  obtain ⟨i, c, kv, hc, -, rfl⟩ := (mem_entsOfRev _ _ _ _).1 he
  refine ⟨?_, rfl⟩
  rcases Nat.lt_or_ge j log.length with hj | hj
  · exact hj
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (l := log) (by omega)] at hc
    simp at hc

/-- The keys of `logEnts` are strictly increasing. -/
theorem logEnts_keys_sorted (log : Log) (hlen : log.length < 2 ^ 63)
    (hcs : ∀ cs ∈ log, cs.length < 2 ^ 63) (lo hi : Nat) :
    (logEnts log lo hi).Pairwise
      (fun e e' => go.GoStringLt (revBytes e.rev e.tomb) (revBytes e'.rev e'.tomb)) := by
  unfold logEnts
  rw [List.pairwise_flatten, List.pairwise_map]
  constructor
  · intro l hl
    rw [List.mem_map] at hl
    obtain ⟨j, -, rfl⟩ := hl
    rw [entsOfRev_range]
    apply List.Pairwise.filterMap (R := (· < ·)) _ _ List.pairwise_lt_range
    intro i i' hii e he e' he'
    have hb := getD_len_bound log hcs j
    cases hk : changeKv (W64 j) (stateAt log (j - 1)) (log.getD j []) i' with
    | none => rw [hk] at he'; cases he'
    | some kv' =>
      have hi' : i' < (log.getD j []).length := by
        unfold changeKv at hk
        cases hc : (log.getD j [])[i']? with
        | none => rw [hc] at hk; cases hk
        | some _ => exact (List.getElem?_eq_some_iff.1 hc).1
      cases hk0 : changeKv (W64 j) (stateAt log (j - 1)) (log.getD j []) i with
      | none => rw [hk0] at he; cases he
      | some kv =>
        rw [hk0] at he; rw [hk] at he'
        simp only [Option.map_some, Option.some.injEq] at he he'
        subst he; subst he'
        exact revBytes_lt_sub _ _ _ _ rfl (by
          simp only; rw [w64_toNat_of_lt i (by omega), w64_toNat_of_lt i' (by omega)]; exact hii)
  · apply (List.pairwise_lt_range' (s := lo) (n := hi - lo)).imp_of_mem
    intro j j' _ _ hjj x hx y hy
    have hx' := entsOfRev_main log j x hx
    have hy' := entsOfRev_main log j' y hy
    exact revBytes_lt_main _ _ _ _ (by
      rw [hx'.2, hy'.2, w64_toNat_of_lt j (by omega), w64_toNat_of_lt j' (by omega)]; exact hjj)

/-- **A range read of the bucket of a well-formed log**, from revision `lo` to `hi` (both
`{Main: _}`: sub `0`, no tombstone mark), returns the entries of the revisions `[lo, hi)` in
revision order. -/
theorem bucketRange_logEnts (log : Log) (hwf : LogWf' log) (hlen : log.length < 2 ^ 63)
    (hcs : ∀ cs ∈ log, cs.length < 2 ^ 63) (lo hi : Nat) (hlohi : lo ≤ hi)
    (hhi : hi ≤ log.length) :
    bucketRange (bucketMap log) (revBytes ⟨W64 lo, W64 0⟩ false) (revBytes ⟨W64 hi, W64 0⟩ false) =
      (logEnts log lo hi).map KvEnt.pair := by
  rw [bucketRange_eq_iff]
  constructor
  · rw [List.map_map, List.pairwise_map]
    exact logEnts_keys_sorted log hlen hcs lo hi
  · intro k v
    rw [bucketMap_lookup_iff log hlen hcs, bucketOf_logEnts]
    simp only [List.mem_map]
    constructor
    · rintro ⟨e, he, hpe⟩
      obtain ⟨j, i, c, kv, h1, h2, hj, hgj, hej, hc, hk, rfl⟩ := logEnts_entry log lo hi e he
      have hil : i < (log.getD j []).length := (List.getElem?_eq_some_iff.1 hc).1
      have hb := getD_len_bound log hcs j
      simp only [KvEnt.pair, Prod.mk.injEq] at hpe
      obtain ⟨rfl, rfl⟩ := hpe
      refine ⟨⟨_, (mem_logEnts log 0 log.length _).2 ⟨j, by omega, hj, hej⟩, rfl⟩,
        (revKey_ge lo j i _ (by omega) (by omega) (by omega)).2 h1,
        (revKey_lt j i hi _ (by omega) (by omega) (by omega)).2 h2⟩
    · rintro ⟨⟨e, he, hpe⟩, hk1, hk2⟩
      obtain ⟨j, i, c, kv, -, -, hj, hgj, hej, hc, hk, rfl⟩ := logEnts_entry log 0 log.length e he
      have hil : i < (log.getD j []).length := (List.getElem?_eq_some_iff.1 hc).1
      have hb := getD_len_bound log hcs j
      simp only [KvEnt.pair, Prod.mk.injEq] at hpe
      obtain ⟨rfl, rfl⟩ := hpe
      have h1 := (revKey_ge lo j i _ (by omega) (by omega) (by omega)).1 hk1
      have h2 := (revKey_lt j i hi _ (by omega) (by omega) (by omega)).1 hk2
      exact ⟨_, (mem_logEnts log lo hi _).2 ⟨j, h1, h2, hej⟩, rfl⟩

/-! ## The entries' events -/

/-- Every key-value of a state has a create revision (not `0`). -/
def CrPos (s : List EtcdKv) : Prop := ∀ kv ∈ s, kv.createRev ≠ W64 0

theorem findKey_mem {k : GoString} {s : List EtcdKv} {kv : EtcdKv} (h : findKey k s = some kv) :
    kv ∈ s := List.mem_of_find?_eq_some h

theorem CrPos.applyChange {s : List EtcdKv} (hs : CrPos s) (r : w64) (hr : r ≠ W64 0)
    (c : Change) : CrPos (applyChange r s c) := by
  cases c with
  | put k v l =>
    intro kv hkv
    simp only [mvcc.applyChange, putKv] at hkv
    rcases btInsert_mem (less := etcdKvLess) hkv with h | h
    · subst h
      cases hf : s.find? (fun v => decide (v.key = k)) with
      | none => exact hr
      | some old => exact hs old (List.mem_of_find?_eq_some hf)
    · exact hs kv h
  | del k =>
    intro kv hkv
    simp only [mvcc.applyChange, List.mem_filter] at hkv
    exact hs kv hkv.1

theorem CrPos.applyChanges {s : List EtcdKv} (hs : CrPos s) (r : w64) (cs : List Change)
    (hr : cs = [] ∨ r ≠ W64 0) : CrPos (applyChanges r s cs) := by
  rcases hr with rfl | hr
  · exact hs
  · unfold mvcc.applyChanges
    induction cs generalizing s with
    | nil => exact hs
    | cons c cs ih => exact ih (hs.applyChange r hr c)

theorem CrPos.stateAfter (L : Log) (hL : L ≠ [] → L[0]? = some []) (hlen : L.length < 2 ^ 63) :
    CrPos (stateAfter L) := by
  unfold mvcc.stateAfter
  have hps : ∀ p ∈ L.zipIdx, p.1 = [] ∨ W64 (p.2 : Int) ≠ W64 0 := by
    intro p hp
    rw [List.mem_zipIdx_iff_getElem?] at hp
    have hlt : p.2 < L.length := (List.getElem?_eq_some_iff.1 hp).1
    by_cases h0 : p.2 = 0
    · left
      rw [h0, hL (by intro h; rw [h] at hlt; simp at hlt)] at hp
      exact (Option.some.inj hp).symm
    · right
      intro h
      have := W64_inj_of_lt (a := p.2) (b := 0) (by omega) (by omega) h
      omega
  generalize L.zipIdx = ps at hps
  have h0 : CrPos ([] : List EtcdKv) := fun _ h => by cases h
  generalize ([] : List EtcdKv) = s0 at h0
  induction ps generalizing s0 with
  | nil => exact h0
  | cons p ps ih =>
    rw [List.foldl_cons]
    exact ih (fun q hq => hps q (List.mem_cons_of_mem _ hq)) _
      (h0.applyChanges _ _ (hps p (List.mem_cons_self)))

theorem CrPos.stateAt (log : Log) (hwf : LogWf' log) (hlen : log.length < 2 ^ 63) (n : Nat) :
    CrPos (stateAt log n) := by
  unfold mvcc.stateAt
  apply CrPos.stateAfter
  · intro hne
    have hlog : log ≠ [] := by intro h; rw [h] at hne; simp at hne
    have h0 := hwf.1 hlog
    rw [List.getElem?_take, if_pos (by omega)]; exact h0
  · rw [List.length_take]; omega

/-- **The entries' events are the log's** (`kvsToEvents` makes a tombstone a `DELETE`, as `End`
makes a key-value with no create revision one: a put's create revision is positive). -/
theorem logEnts_events (log : Log) (hwf : LogWf' log) (hlen : log.length < 2 ^ 63)
    (hcs : ∀ cs ∈ log, cs.length < 2 ^ 63) (lo hi : Nat) (hhi : hi ≤ log.length) :
    (logEnts log lo hi).map KvEnt.ev = logEvents log lo hi := by
  unfold logEnts logEvents
  rw [List.map_flatten, List.map_map]
  congr 1
  apply List.map_congr_left
  intro m _
  simp only [Function.comp_apply]
  rw [entsOfRev_range, List.map_filterMap]
  unfold evsOfRevM
  congr 1
  funext i
  have hb := getD_len_bound log hcs m
  cases hk : changeKv (W64 m) (stateAt log (m - 1)) (log.getD m []) i with
  | none => rfl
  | some kv =>
    simp only [Option.map_some, Option.some.injEq]
    rcases changeKv_cases _ _ (stateAt_sorted _ _) _ i kv hk with
      ⟨k, hc, rfl⟩ | ⟨k, v, l, hc, hmod, hcr⟩
    · rw [List.getD_eq_getElem?_getD, hc]
      rfl
    · rw [List.getD_eq_getElem?_getD, hc]
      -- the put's key-value has a create revision
      have hm0 : m ≠ 0 := by
        rintro rfl
        have : (log.getD 0 []) = [] := by
          rw [List.getD_eq_getElem?_getD]
          cases h : log[0]? with
          | none => rfl
          | some cs =>
            have hne : log ≠ [] := by intro h'; rw [h'] at h; simp at h
            rw [hwf.1 hne] at h; cases h; rfl
        rw [this] at hc; simp at hc
      have hmlen : m < log.length := by
        rcases Nat.lt_or_ge m log.length with h | h
        · exact h
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (l := log) (by omega)] at hc
          simp at hc
      have hW : (W64 (m : Int)) ≠ W64 0 := by
        intro h
        have := W64_inj_of_lt (a := m) (b := 0) (by omega) (by omega) h
        omega
      have hpos : kv.createRev ≠ W64 0 := by
        rw [hcr]
        cases hf : findKey k (applyChanges (W64 m) (stateAt log (m - 1)) ((log.getD m []).take i)) with
        | none => exact hW
        | some old =>
          exact (CrPos.stateAt log hwf hlen (m - 1)).applyChanges _ _ (Or.inr hW) old (findKey_mem hf)
      unfold KvEnt.ev evOfKv
      rw [if_neg hpos]
      rfl

end mvcc
end EtcdGrove
end Perennial
