/-
Lean-first (no Rocq counterpart). Trace-check's S5, Draft (2026-11-09): the simulation invariant's
per-server facts (`notes/trace-validation-sim.md`, "The invariants", route (a): for every server `j`,
the persistent raft facts `σ.s j` stands for) and the specification's invariants derived from them.

- `srvFacts γ C j v`: server `v` (node `j`'s in `σ`) is raft's log `es` read by `logAbs` (the
  bootstrap the `|C|` configuration entries), with `es`'s records (`logRecs`), its committed prefix
  committed (`isCommitted`), its commit index's certificate (`commitIn`), and, a leader, raft's
  leader of its term (`isLeader`) with `es` its full log of the term (`leadFull`); its numbers in
  range.
- `allFacts γ C σ`: every voter's.

Derived so far: `MoreThanOneLeaderInv` (from `isLeader_unique`).
-/
module

public import Proof.go_etcd_io.raft.v3.TraceSimInv
public import Proof.go_etcd_io.raft.v3.Protocol.Ghost

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section pure
variable [GooseExts]

theorem mem_confAbs_inv (C : List w64) (x : Etcdraft.ID) (h : x ∈ confAbs C) : ∃ w ∈ C, x = idAbs w := by
  unfold confAbs at h; rw [setIds_mk_mem, List.mem_map] at h
  obtain ⟨w, hw, e⟩ := h; exact ⟨w, hw, e.symm⟩

theorem logAbs_take (C : List w64) (bl f : Nat) (l : List EntryM) (n : Nat) :
    (logAbs C bl f l).take n = logAbs C bl f (l.take n) := by
  unfold logAbs
  apply List.ext_getElem?
  intro k
  simp only [List.getElem?_take, List.getElem?_mapIdx]
  split <;> simp_all

theorem logAbs_prefix (C : List w64) (bl f : Nat) (l1 l2 : List EntryM) (h : l1 <+: l2) :
    logAbs C bl f l1 <+: logAbs C bl f l2 := by
  obtain ⟨r, rfl⟩ := h
  refine ⟨(logAbs C bl f (l1 ++ r)).drop l1.length, ?_⟩
  have : logAbs C bl f l1 = (logAbs C bl f (l1 ++ r)).take l1.length := by
    rw [logAbs_take, List.take_left' rfl]
  rw [this, List.take_append_drop]

theorem isPrefix_of_prefix (s t : List Etcdraft.Entry) (h : s <+: t) : Etcdraft.isPrefix s t = true := by
  unfold Etcdraft.isPrefix
  obtain ⟨r, rfl⟩ := h
  simp

/-- An abstract entry is its position's and its term's. -/
theorem entAbs_eq (C : List w64) (bl k : Nat) (e1 e2 : EntryM) (h : e1.Term' = e2.Term') :
    entAbs C bl k e1 = entAbs C bl k e2 := by
  unfold entAbs; split <;> simp [h]

/-- **Log matching on the abstract logs** (from raft's records' agreement, `plog_match_down`): two
logs with the same term at a position agree up to it. -/
theorem logAbs_match (C : List w64) (es1 es2 : List EntryM)
    (hb1 : BootTerms C.length 1 es1) (hb2 : BootTerms C.length 1 es2)
    (hw1 : PlogWfR (entryID.mk (W64 0) (W64 0)) es1) (hw2 : PlogWfR (entryID.mk (W64 0) (W64 0)) es2)
    (hl1 : es1.length < 2 ^ 63) (_hl2 : es2.length < 2 ^ 63)
    (hra : RecsAgree (entryID.mk (W64 0) (W64 0)) es1 (entryID.mk (W64 0) (W64 0)) es2)
    (n : Nat) (hn1 : n < es1.length) (hn2 : n < es2.length)
    (ht : ((logAbs C C.length 1 es1)[n]?).map Etcdraft.Entry.term = ((logAbs C C.length 1 es2)[n]?).map Etcdraft.Entry.term) :
    (logAbs C C.length 1 es1).take (n + 1) = (logAbs C C.length 1 es2).take (n + 1) := by
  rw [logAbs_take, logAbs_take]
  -- the raft terms agree at every position up to `n`
  have hT : ∀ k, k ≤ n → es1[k]?.map EntryM.Term' = es2[k]?.map EntryM.Term' := by
    have hn : es1[n]?.map EntryM.Term' = es2[n]?.map EntryM.Term' := by
      simp only [logAbs, List.getElem?_mapIdx, List.getElem?_eq_getElem hn1, List.getElem?_eq_getElem hn2,
        Option.map_some] at ht
      simp only [List.getElem?_eq_getElem hn1, List.getElem?_eq_getElem hn2, Option.map_some, Option.some.injEq] at ht ⊢
      by_cases hk : 1 + n ≤ C.length
      · rw [hb1 n _ hk (List.getElem?_eq_getElem hn1), hb2 n _ hk (List.getElem?_eq_getElem hn2)]
      · rw [entAbs_term C C.length _ _ (fun h => absurd h hk), entAbs_term C C.length _ _ (fun h => absurd h hk)] at ht
        exact uint_Z_inj.mp ht
    have hi : 0 < uint.Z (W64 ((n : Int) + 1)) := by word
    have hin : uint.nat (W64 ((n : Int) + 1)) - 1 = n := by word
    have hS : (plogTermAt (entryID.mk (W64 0) (W64 0)) es1 (W64 ((n : Int) + 1))).isSome := by
      rw [plogTermAt_base0 _ _ hi, hin, List.getElem?_eq_getElem hn1]; rfl
    have hE : plogTermAt (entryID.mk (W64 0) (W64 0)) es1 (W64 ((n : Int) + 1)) =
        plogTermAt (entryID.mk (W64 0) (W64 0)) es2 (W64 ((n : Int) + 1)) := by
      rw [plogTermAt_base0 _ _ hi, plogTermAt_base0 _ _ hi, hin, hn]
    have hd := plog_match_down _ es1 _ es2 _ hw1 hw2 hra hS hE
    intro k hk
    have hk1 : 0 < uint.Z (W64 ((k : Int) + 1)) := by word
    have hkn : uint.nat (W64 ((k : Int) + 1)) - 1 = k := by word
    have := hd (W64 ((k : Int) + 1)) (by simp) (by simp) (by word)
    rw [plogTermAt_base0 _ _ hk1, plogTermAt_base0 _ _ hk1, hkn] at this
    exact this
  apply List.ext_getElem?
  intro k
  simp only [logAbs, List.getElem?_mapIdx, List.getElem?_take]
  split
  · rename_i hk
    have := hT k (by omega)
    have hk1 : k < es1.length := by omega
    have hk2 : k < es2.length := by omega
    rw [List.getElem?_eq_getElem hk1, List.getElem?_eq_getElem hk2] at this ⊢
    simp only [Option.map_some, Option.some.injEq] at this ⊢
    exact entAbs_eq C C.length _ _ _ this
  · rfl

/-! ### `ElectionSafetyInv` by a specification invariant (route (b)) -/

/-- **The leaders' term entries** (route (b) of the notes' `ElectionSafetyInv`): for every leader `i`
of term `T`, every term-`T` entry anywhere (a log, or a message in either bag at its index) is at a
position where `i`'s log has a term-`T` entry. Only `T`'s leader creates such entries, at the end of
its log, which it never truncates while it leads. -/
def LeaderEntries (σ : Etcdraft.State) : Prop :=
  ∀ i ∈ σ.server, (σ.s i).state = Etcdraft.leader →
    (∀ j ∈ σ.server, ∀ (k : Nat) (e : Etcdraft.Entry), (σ.s j).log[k]? = some e →
      e.term = (σ.s i).currentTerm → ((σ.s i).log[k]?).map Etcdraft.Entry.term = some e.term) ∧
    (∀ m ∈ σ.messages.domain ++ σ.pendingMessages.domain, ∀ (k : Nat) (e : Etcdraft.Entry),
      m.entries[k]? = some e → e.term = (σ.s i).currentTerm →
      ((σ.s i).log[(m.prevLogIndex.toNat + k)]?).map Etcdraft.Entry.term = some e.term)

theorem maxIndexOfTerm_ge (xlog : List Etcdraft.Entry) (t : Int) (k : Nat)
    (hk : (xlog[k]?).map Etcdraft.Entry.term = some t) : k + 1 ≤ Etcdraft.maxIndexOfTerm xlog t := by
  unfold Etcdraft.maxIndexOfTerm
  have hkl : k < xlog.length := by
    rcases Nat.lt_or_ge k xlog.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hk; cases hk
  suffices ∀ N acc, k < N → N ≤ xlog.length →
      k + 1 ≤ (List.range N).foldl (fun (acc : Nat) n => if ((xlog[n]?).map Etcdraft.Entry.term) == some t then n + 1 else acc) acc by
    exact this _ 0 hkl (Nat.le_refl _)
  intro N
  induction N with
  | zero => intro acc h; omega
  | succ N ih =>
    intro acc hkN hN
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rcases Nat.lt_or_ge k N with h | h
    · have := ih acc h (by omega)
      split
      · omega
      · exact this
    · have : k = N := by omega
      subst this; simp [hk]

theorem maxIndexOfTerm_cases (xlog : List Etcdraft.Entry) (t : Int) :
    Etcdraft.maxIndexOfTerm xlog t = 0 ∨
      ∃ k, Etcdraft.maxIndexOfTerm xlog t = k + 1 ∧ (xlog[k]?).map Etcdraft.Entry.term = some t := by
  unfold Etcdraft.maxIndexOfTerm
  suffices ∀ N, (List.range N).foldl (fun (acc : Nat) n => if ((xlog[n]?).map Etcdraft.Entry.term) == some t then n + 1 else acc) 0 = 0 ∨
      ∃ k, (List.range N).foldl (fun (acc : Nat) n => if ((xlog[n]?).map Etcdraft.Entry.term) == some t then n + 1 else acc) 0 = k + 1 ∧
        (xlog[k]?).map Etcdraft.Entry.term = some t by
    exact this _
  intro N
  induction N with
  | zero => left; rfl
  | succ N ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    split
    · rename_i h; right; exact ⟨N, rfl, by simpa using h⟩
    · exact ih

/-- **`ElectionSafetyInv` from the leaders' term entries.** -/
theorem electionSafety_of_leaderEntries (σ : Etcdraft.State) (h : LeaderEntries σ) :
    σ.electionSafetyInv = true := by
  unfold Etcdraft.State.electionSafetyInv
  rw [List.all_eq_true]
  intro i hi
  by_cases hl : (σ.s i).state = Etcdraft.leader
  · have hli := (h i hi hl).1
    simp only [hl, bne_self_eq_false, Bool.false_or, List.all_eq_true, decide_eq_true_eq]
    intro j hj
    rcases maxIndexOfTerm_cases (σ.s j).log (σ.s i).currentTerm with h0 | ⟨k, hk, hkt⟩
    · rw [h0]; omega
    · rw [hk]
      obtain ⟨e, he⟩ : ∃ e, (σ.s j).log[k]? = some e := by
        cases hx : (σ.s j).log[k]? with
        | none => rw [hx] at hkt; cases hkt
        | some e => exact ⟨e, rfl⟩
      rw [he] at hkt
      simp only [Option.map_some, Option.some.injEq] at hkt
      exact maxIndexOfTerm_ge _ _ k (by rw [hli j hj k e he hkt, hkt])
  · simp [hl]

/-! ### `CommittedIsDurableInv` by a specification invariant (route (b)) -/

/-- **A leader's durable bound** (route (b) of the notes' `CommittedIsDurableInv`): for every leader
`i` of term `T`, its commit index, its match indices, the append requests of term `T` it has handed
out (in `messages`: only a `Ready` moves them there, after persisting the whole log) and the
successful responses of term `T` addressed to it are within its durable log. -/
def DurInv (σ : Etcdraft.State) : Prop :=
  ∀ i ∈ σ.server, (σ.s i).state = Etcdraft.leader →
    let d : Int := (σ.s i).durable.log.length
    (σ.s i).commitIndex ≤ d ∧ (∀ j ∈ σ.server, (σ.s i).matchIndex j ≤ d) ∧
    (∀ m ∈ σ.messages.domain, m.source = i → m.type = .appendEntriesRequest →
      m.term = (σ.s i).currentTerm → m.prevLogIndex + m.entries.length ≤ d) ∧
    (∀ m ∈ σ.messages.domain ++ σ.pendingMessages.domain, m.dest = i → m.type = .appendEntriesResponse →
      m.term = (σ.s i).currentTerm → m.success = true → m.matchIndex ≤ d)

/-- **`CommittedIsDurableInv` from the durable bound.** -/
theorem durable_of_durInv (σ : Etcdraft.State) (h : DurInv σ) : σ.committedIsDurableInv = true := by
  unfold Etcdraft.State.committedIsDurableInv
  rw [List.all_eq_true]
  intro i hi
  by_cases hl : (σ.s i).state = Etcdraft.leader
  · simp [hl, (h i hi hl).1]
  · simp [hl]

end pure

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A server's facts**: node `j`'s server `v` in the simulation's state. -/
def srvFacts (γ : RaftNames) (C : List w64) (j : w64) (v : Etcdraft.Server) : IProp GF :=
  iprop(∃ es : List EntryM,
    ⌜v.log = logAbs C C.length 1 es ∧ BootTerms C.length 1 es ∧
      PlogWfR (entryID.mk (W64 0) (W64 0)) es ∧ es.length < 2 ^ 63 ∧
      0 ≤ v.commitIndex ∧ v.commitIndex ≤ es.length ∧ 0 ≤ v.currentTerm ∧ v.currentTerm < 2 ^ 63⌝ ∗
    logRecs γ ⟨W64 0, W64 0⟩ es ∗ isCommitted γ (es.take v.commitIndex.toNat) ∗
    (if v.state = Etcdraft.leader then iprop(isLeader γ j (W64 v.currentTerm) ∗ leadFull γ (W64 v.currentTerm) es)
     else iprop(True)) ∗
    commitIn γ es (W64 v.commitIndex) (W64 v.currentTerm))

instance srvFacts_persistent (γ : RaftNames) (C : List w64) (j : w64) (v : Etcdraft.Server) :
    Persistent (srvFacts (GF := GF) γ C j v) := by
  unfold srvFacts; split <;> infer_instance

/-- **Every voter's facts** in state `σ`. -/
def allFacts (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) : IProp GF :=
  iprop(□ ∀ j, ⌜j ∈ C⌝ → srvFacts γ C j (σ.s (idAbs j)))

instance allFacts_persistent (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) :
    Persistent (allFacts (GF := GF) γ C σ) := by
  unfold allFacts; infer_instance

/-- A leader's term's word. -/
theorem w64_of_int_inj (a b : Int) (ha : 0 ≤ a) (ha' : a < 2 ^ 63) (hb : 0 ≤ b) (hb' : b < 2 ^ 63)
    (h : W64 a = W64 b) : a = b := by
  have h1 : uint.Z (W64 a) = a := by word
  have h2 : uint.Z (W64 b) = b := by word
  rw [← h1, ← h2, h]

/-- **`MoreThanOneLeaderInv` from the facts** (`isLeader_unique`). -/
theorem allFacts_oneLeader (γ : RaftNames) (C : List w64) (σ : Etcdraft.State)
    (hsrv : σ.server = confAbs C) :
    allFacts (GF := GF) γ C σ ⊢ ⌜σ.moreThanOneLeaderInv = true⌝ := by
  iintro #H
  iunfold allFacts at H
  by_cases hc : σ.moreThanOneLeaderInv = true
  · ipureintro; exact hc
  -- a pair of distinct leaders of one term
  have : ∃ i ∈ C, ∃ j ∈ C, (σ.s (idAbs i)).currentTerm = (σ.s (idAbs j)).currentTerm ∧
      (σ.s (idAbs i)).state = Etcdraft.leader ∧ (σ.s (idAbs j)).state = Etcdraft.leader ∧ i ≠ j := by
    unfold Etcdraft.State.moreThanOneLeaderInv at hc
    rw [hsrv, List.all_eq_true] at hc
    simp only [Classical.not_forall, List.all_eq_true] at hc
    obtain ⟨x, hx, hc⟩ := hc
    obtain ⟨y, hy, hc⟩ := hc
    obtain ⟨i, hi, rfl⟩ := mem_confAbs_inv C x hx
    obtain ⟨j, hj, rfl⟩ := mem_confAbs_inv C y hy
    refine ⟨i, hi, j, hj, ?_⟩
    by_cases h1 : (σ.s (idAbs i)).currentTerm = (σ.s (idAbs j)).currentTerm
    · by_cases h2 : (σ.s (idAbs i)).state = Etcdraft.leader
      · by_cases h3 : (σ.s (idAbs j)).state = Etcdraft.leader
        · refine ⟨h1, h2, h3, fun e => hc ?_⟩
          subst e; simp
        · exact absurd (by simp [h3]) hc
      · exact absurd (by simp [h2]) hc
    · exact absurd (by simp [h1]) hc
  obtain ⟨i, hi, j, hj, ht, hli, hlj, hne⟩ := this
  ihave Hfi := H $$ %i %hi
  ihave Hfj := H $$ %j %hj
  iunfold srvFacts at Hfi Hfj
  icases Hfi with ⟨%esi, %Hpi, -, -, Hli, -⟩
  icases Hfj with ⟨%esj, %Hpj, -, -, Hlj, -⟩
  simp only [hli, hlj, ite_true]
  rw [ht]
  icases Hli with ⟨Hli, -⟩
  icases Hlj with ⟨Hlj, -⟩
  icases isLeader_unique γ i j _ $$ Hli Hlj with %He
  exact absurd He hne

/-- A server's committed prefix, from its facts' log. -/
theorem committedL_abs (C : List w64) (σ : Etcdraft.State) (i : Etcdraft.ID) (es : List EntryM)
    (hlog : (σ.s i).log = logAbs C C.length 1 es) :
    committedL σ i = logAbs C C.length 1 (es.take (σ.s i).commitIndex.toNat) := by
  unfold committedL; rw [hlog, logAbs_take]

/-- **`LogInv`'s facts** (`isCommitted_agree`): any two voters' committed prefixes are prefixes one of
the other. -/
theorem allFacts_logInv (γ : RaftNames) (C : List w64) (σ : Etcdraft.State)
    (hsrv : σ.server = confAbs C) :
    allFacts (GF := GF) γ C σ ⊢ ⌜∀ i ∈ σ.server, ∀ j ∈ σ.server,
      (or (Etcdraft.isPrefix (committedL σ i) (committedL σ j))
        (Etcdraft.isPrefix (committedL σ j) (committedL σ i))) = true⌝ := by
  iintro #H
  iunfold allFacts at H
  by_cases hc : ∀ i ∈ σ.server, ∀ j ∈ σ.server,
      (or (Etcdraft.isPrefix (committedL σ i) (committedL σ j))
        (Etcdraft.isPrefix (committedL σ j) (committedL σ i))) = true
  · ipureintro; exact hc
  simp only [Classical.not_forall] at hc
  obtain ⟨x, hx, y, hy, hc⟩ := hc
  rw [hsrv] at hx hy
  obtain ⟨i, hi, rfl⟩ := mem_confAbs_inv C x hx
  obtain ⟨j, hj, rfl⟩ := mem_confAbs_inv C y hy
  ihave Hfi := H $$ %i %hi
  ihave Hfj := H $$ %j %hj
  iunfold srvFacts at Hfi Hfj
  icases Hfi with ⟨%esi, %Hpi, -, Hci, -, -⟩
  icases Hfj with ⟨%esj, %Hpj, -, Hcj, -, -⟩
  icases isCommitted_agree γ _ _ $$ Hci Hcj with %Hag
  exfalso
  apply hc
  rw [committedL_abs C σ _ esi Hpi.1, committedL_abs C σ _ esj Hpj.1]
  rcases Hag with h | h
  · simp [isPrefix_of_prefix _ _ (logAbs_prefix C C.length 1 _ _ h)]
  · simp [isPrefix_of_prefix _ _ (logAbs_prefix C C.length 1 _ _ h)]

/-- **`LogMatchingInv` from the facts** (`logRecs_agree`, then `logAbs_match`). -/
theorem allFacts_logMatching (γ : RaftNames) (C : List w64) (σ : Etcdraft.State)
    (hsrv : σ.server = confAbs C) :
    allFacts (GF := GF) γ C σ ⊢ ⌜σ.logMatchingInv = true⌝ := by
  iintro #H
  iunfold allFacts at H
  by_cases hc : σ.logMatchingInv = true
  · ipureintro; exact hc
  unfold Etcdraft.State.logMatchingInv at hc
  rw [hsrv, List.all_eq_true] at hc
  simp only [Classical.not_forall, List.all_eq_true] at hc
  obtain ⟨x, hx, y, hy, n, hn, hc⟩ := hc
  obtain ⟨i, hi, rfl⟩ := mem_confAbs_inv C x hx
  obtain ⟨j, hj, rfl⟩ := mem_confAbs_inv C y hy
  ihave Hfi := H $$ %i %hi
  ihave Hfj := H $$ %j %hj
  iunfold srvFacts at Hfi Hfj
  icases Hfi with ⟨%esi, %Hpi, Hri, -, -, -⟩
  icases Hfj with ⟨%esj, %Hpj, Hrj, -, -, -⟩
  icases logRecs_agree γ _ _ _ _ $$ Hri Hrj with %Hra
  exfalso
  apply hc
  obtain ⟨hli, hbi, hwi, hlni, -⟩ := Hpi
  obtain ⟨hlj, hbj, hwj, hlnj, -⟩ := Hpj
  rw [List.mem_range] at hn
  rw [hli, hlj] at hn ⊢
  rw [logAbs_length, logAbs_length] at hn
  by_cases ht : ((logAbs C C.length 1 esi)[n]?).map Etcdraft.Entry.term =
      ((logAbs C C.length 1 esj)[n]?).map Etcdraft.Entry.term
  · rw [logAbs_match C esi esj hbi hbj hwi hwj hlni hlnj Hra n (by omega) (by omega) ht]; simp
  · simp [ht]

/-- **`CommitOk` from the facts.** -/
theorem allFacts_commitOk (γ : RaftNames) (C : List w64) (σ : Etcdraft.State)
    (hsrv : σ.server = confAbs C) :
    allFacts (GF := GF) γ C σ ⊢ ⌜CommitOk σ⌝ := by
  iintro #H
  iunfold allFacts at H
  by_cases hc : CommitOk σ
  · ipureintro; exact hc
  unfold CommitOk at hc
  simp only [Classical.not_forall] at hc
  obtain ⟨x, hx, hc⟩ := hc
  rw [hsrv] at hx
  obtain ⟨i, hi, rfl⟩ := mem_confAbs_inv C x hx
  ihave Hfi := H $$ %i %hi
  iunfold srvFacts at Hfi
  icases Hfi with ⟨%esi, %Hpi, -, -, -, -⟩
  exfalso; apply hc
  obtain ⟨hl, -, -, -, h0, h1, -⟩ := Hpi
  rw [hl, logAbs_length]; exact ⟨h0, h1⟩

end ghost

end EtcdGrove
end Perennial
