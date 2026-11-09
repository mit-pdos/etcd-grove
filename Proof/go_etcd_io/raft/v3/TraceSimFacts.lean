/-
Lean-first (no Rocq counterpart). Trace-check's S5, Draft (2026-11-09): the simulation invariant's
per-server facts (`notes/trace-validation-sim.md`, "The invariants", route (a): for every server `j`,
the persistent raft facts `σ.s j` stands for) and the specification's invariants derived from them.

- `srvFacts γ C j v`: server `v` (node `j`'s in `σ`) is raft's recorded log `es`, followed at a
  leader by its pending entries `pend`, read by `logAbs` (the bootstrap the `|C|` configuration
  entries), with `es`'s records (`logRecs`), its committed prefix committed (`isCommitted`), its
  commit index (within `es`)'s certificate (`commitIn`), and, a leader, raft's leader of its term
  (`isLeader`) with `es` its full log of the term (`leadFull`); its numbers in range. The pending
  entries (2026-11-09, review finding A9) are those of the leader's `Replicate` lines, which raft
  appends, and so records, only after the hook (`appendEntry`, raft.go:849-852): of the leader's
  term, after its campaign log `F0` (`isCamp`) when `es` is `F0` or ends in an entry of the term
  (raft's `campOwn`). Without the last clause `LogMatchingInv` does not follow: `leadFull` is a
  lower bound, so another server's recorded entry of the term past `es` is not excluded, and
  `es` could extend `F0` by entries of earlier terms where that server has the leader's.
- `allFacts γ C σ`: every voter's.

Derived from them (with the vote table where it is needed): `MoreThanOneLeaderInv`
(`allFacts_oneLeader`), `LogInv`, `LogMatchingInv`, `CommitOk` and `LeaderCompletenessInv`. Route
(b)'s `CommitWithinLeader`, `LeaderEntries` and `DurInv` are here too, but `simFx` does not use them:
`DurInv` is false as stated, and `SpecInv` (`TraceSimSpecInv.lean`) replaces it.
-/
module

public import Proof.go_etcd_io.raft.v3.TraceSimInv
public import Proof.go_etcd_io.raft.v3.Protocol.Ghost
public import Proof.go_etcd_io.raft.v3.Protocol.LeaderCompleteness

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

/-- **Entries from terms**: two logs whose raft terms agree below `c` have the same abstract entries
there. -/
theorem logAbs_get_of_terms (C : List w64) (es1 es2 : List EntryM) (c idx : Nat)
    (hc1 : c ≤ es1.length) (hc2 : c ≤ es2.length)
    (hag : ∀ k, k < c → es1[k]?.map EntryM.Term' = es2[k]?.map EntryM.Term') (hidx : idx < c) :
    (logAbs C C.length 1 es1)[idx]? = some (((logAbs C C.length 1 es2)[idx]?).getD default) := by
  have h := hag idx hidx
  rw [List.getElem?_eq_getElem (by omega : idx < es1.length),
    List.getElem?_eq_getElem (by omega : idx < es2.length)] at h
  simp only [Option.map_some, Option.some.injEq] at h
  simp only [logAbs, List.getElem?_mapIdx, List.getElem?_eq_getElem (by omega : idx < es1.length),
    List.getElem?_eq_getElem (by omega : idx < es2.length), Option.map_some, Option.getD_some]
  rw [entAbs_eq C C.length _ _ _ h]

/-- Terms at `W64 (k + 1)` of an uncompacted log are its entries' terms at `k`. -/
theorem terms_of_plog (es1 es2 : List EntryM) (c : Nat) (hc : c < 2 ^ 63)
    (h : ∀ j : w64, uint.Z j ≤ (c : Int) →
      plogTermAt (entryID.mk (W64 0) (W64 0)) es1 j = plogTermAt (entryID.mk (W64 0) (W64 0)) es2 j) :
    ∀ k, k < c → es1[k]?.map EntryM.Term' = es2[k]?.map EntryM.Term' := by
  intro k hk
  have hk1 : 0 < uint.Z (W64 ((k : Int) + 1)) := by word
  have hkn : uint.nat (W64 ((k : Int) + 1)) - 1 = k := by word
  have := h (W64 ((k : Int) + 1)) (by word)
  rw [plogTermAt_base0 _ _ hk1, plogTermAt_base0 _ _ hk1, hkn] at this
  exact this

/-- An uncompacted log's term at `k + 1` is its `k`-th entry's. -/
theorem plogTermAt_succ (L : List EntryM) (k : Nat) (hk : (k : Int) + 1 < 2 ^ 63) :
    plogTermAt base0 L (W64 ((k : Int) + 1)) = L[k]?.map EntryM.Term' := by
  have hi : 0 < uint.Z (W64 ((k : Int) + 1)) := by word
  have hin : uint.nat (W64 ((k : Int) + 1)) - 1 = k := by word
  have := plogTermAt_base0 L _ hi
  rw [hin] at this
  exact this

theorem PlogWfR_append_left (b : entryID) (l1 l2 : List EntryM) (h : PlogWfR b (l1 ++ l2)) :
    PlogWfR b l1 := by
  intro k e hk hr
  exact h k e (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hk).1]; exact hk) hr

/-- **Raft's terms from the abstract ones**: two logs (from index 1, raft's bootstrap entries of
term 1) with the same abstract term at `n` have the same raft term there. -/
theorem terms_of_absTerms (C : List w64) (es1 es2 : List EntryM)
    (hb1 : BootTerms C.length 1 es1) (hb2 : BootTerms C.length 1 es2)
    (n : Nat) (hn1 : n < es1.length) (hn2 : n < es2.length)
    (ht : ((logAbs C C.length 1 es1)[n]?).map Etcdraft.Entry.term = ((logAbs C C.length 1 es2)[n]?).map Etcdraft.Entry.term) :
    es1[n]?.map EntryM.Term' = es2[n]?.map EntryM.Term' := by
  simp only [logAbs, List.getElem?_mapIdx, List.getElem?_eq_getElem hn1, List.getElem?_eq_getElem hn2,
    Option.map_some] at ht
  simp only [List.getElem?_eq_getElem hn1, List.getElem?_eq_getElem hn2, Option.map_some, Option.some.injEq] at ht ⊢
  by_cases hk : 1 + n ≤ C.length
  · rw [hb1 n _ hk (List.getElem?_eq_getElem hn1), hb2 n _ hk (List.getElem?_eq_getElem hn2)]
  · rw [entAbs_term C C.length _ _ (fun h => absurd h hk), entAbs_term C C.length _ _ (fun h => absurd h hk)] at ht
    exact uint_Z_inj.mp ht

/-- **Abstract prefixes from raft's terms**: two logs whose raft terms agree up to `n` have the same
abstract prefix up to it. -/
theorem logAbs_take_of_terms (C : List w64) (es1 es2 : List EntryM) (n : Nat)
    (hn1 : n < es1.length) (hn2 : n < es2.length)
    (hT : ∀ k, k ≤ n → es1[k]?.map EntryM.Term' = es2[k]?.map EntryM.Term') :
    (logAbs C C.length 1 es1).take (n + 1) = (logAbs C C.length 1 es2).take (n + 1) := by
  rw [logAbs_take, logAbs_take]
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

/-- **Log matching on raft's terms** (`plog_match_down`): two logs with records' agreement and the
same term at position `n` have the same terms below. -/
theorem terms_match_down (es1 es2 : List EntryM)
    (hw1 : PlogWfR base0 es1) (hw2 : PlogWfR base0 es2) (hl1 : es1.length < 2 ^ 63)
    (hra : RecsAgree base0 es1 base0 es2) (n : Nat) (hn1 : n < es1.length)
    (hn : es1[n]?.map EntryM.Term' = es2[n]?.map EntryM.Term') :
    ∀ k, k ≤ n → es1[k]?.map EntryM.Term' = es2[k]?.map EntryM.Term' := by
  have hS : (plogTermAt base0 es1 (W64 ((n : Int) + 1))).isSome := by
    rw [plogTermAt_succ _ _ (by omega), List.getElem?_eq_getElem hn1]; rfl
  have hE : plogTermAt base0 es1 (W64 ((n : Int) + 1)) = plogTermAt base0 es2 (W64 ((n : Int) + 1)) := by
    rw [plogTermAt_succ _ _ (by omega), plogTermAt_succ _ _ (by omega), hn]
  have hd := plog_match_down _ es1 _ es2 _ hw1 hw2 hra hS hE
  intro k hk
  have := hd (W64 ((k : Int) + 1)) (by rw [base0_index]; word) (by rw [base0_index]; word) (by word)
  rw [plogTermAt_succ _ _ (by omega), plogTermAt_succ _ _ (by omega)] at this
  exact this

/-- **A server's commit index within its term's leader's log** (the specification invariant
`LeaderCompletenessInv`'s same-term case needs: `notes/trace-validation-sim.md`, "The invariants from
the facts"). -/
def CommitWithinLeader (σ : Etcdraft.State) : Prop :=
  ∀ i ∈ σ.server, ∀ l ∈ σ.server, (σ.s l).state = Etcdraft.leader →
    (σ.s i).currentTerm = (σ.s l).currentTerm → (σ.s i).commitIndex ≤ (σ.s l).log.length

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
variable [GooseExts]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]

/-- **A server's facts**: node `j`'s server `v` in the simulation's state. Its log is raft's
recorded log `es` followed, at a leader, by its **pending entries** `pend`: the entries its
`Replicate` lines have announced, which raft appends (and so records) only after the hook
(`appendEntry`, raft.go:849-852; review finding A9). They are of the leader's term, and follow its
campaign log `F0` or an entry of its term (raft's `campOwn`; at `becomeLeader`'s own entry the
records are the campaign log). The records, the commit facts and the leader's facts are over
`es`. -/
def srvFacts (γ : RaftNames) (C : List w64) (j : w64) (v : Etcdraft.Server) : IProp GF :=
  iprop(∃ es pend : List EntryM,
    ⌜v.log = logAbs C C.length 1 (es ++ pend) ∧ BootTerms C.length 1 (es ++ pend) ∧
      PlogWfR (entryID.mk (W64 0) (W64 0)) (es ++ pend) ∧ (es ++ pend).length < 2 ^ 63 ∧
      0 ≤ v.commitIndex ∧ v.commitIndex ≤ es.length ∧ 0 ≤ v.currentTerm ∧ v.currentTerm < 2 ^ 63 ∧
      (v.state ≠ Etcdraft.leader → pend = []) ∧ (∀ e ∈ pend, e.Term' = W64 v.currentTerm)⌝ ∗
    logRecs γ base0 es ∗ isCommitted γ (es.take v.commitIndex.toNat) ∗
    (if v.state = Etcdraft.leader then
      iprop(isLeader γ j (W64 v.currentTerm) ∗ leadFull γ (W64 v.currentTerm) es ∗
        (⌜pend = []⌝ ∨ ∃ F0, isCamp γ j (W64 v.currentTerm) F0 ∗
          ⌜F0 <+: es ∧ (es = F0 ∨ es.getLast?.map EntryM.Term' = some (W64 v.currentTerm))⌝))
     else iprop(True)) ∗
    commitIn γ es (W64 v.commitIndex) (W64 v.currentTerm))

instance srvFacts_persistent (γ : RaftNames) (C : List w64) (j : w64) (v : Etcdraft.Server) :
    Persistent (srvFacts (GF := GF) γ C j v) := by
  unfold srvFacts; split <;> infer_instance

instance srvFacts_timeless (γ : RaftNames) (C : List w64) (j : w64) (v : Etcdraft.Server) :
    Timeless (srvFacts (GF := GF) γ C j v) := by
  unfold srvFacts; split <;> infer_instance

/-- **Every voter's facts** in state `σ`. -/
def allFacts (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) : IProp GF :=
  iprop(□ ∀ j, ⌜j ∈ C⌝ → srvFacts γ C j (σ.s (idAbs j)))

instance allFacts_persistent (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) :
    Persistent (allFacts (GF := GF) γ C σ) := by
  unfold allFacts; infer_instance

instance allFacts_timeless (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) :
    Timeless (allFacts (GF := GF) γ C σ) := by
  unfold allFacts; infer_instance

/-- A leader's term's word. -/
theorem w64_of_int_inj (a b : Int) (ha : 0 ≤ a) (ha' : a < 2 ^ 63) (hb : 0 ≤ b) (hb' : b < 2 ^ 63)
    (h : W64 a = W64 b) : a = b := by
  have h1 : uint.Z (W64 a) = a := by word
  have h2 : uint.Z (W64 b) = b := by word
  rw [← h1, ← h2, h]

/-- **A commit certificate in a leader's full log** (the three cases of `restart_ack_one`,
`Protocol/Enter.lean`): a log `es` with records and a commit certificate `commitIn γ es c tm`, and a
full log `G'` of a term `T ≥ tm` (`leadFull`), long enough to reach `c` when `T` is the certificate's
own term, agree on terms up to `c` (bootstrap: both start with the bootstrap log; a commit fact of
`T`: two full logs of one term; an earlier term: `lc_core`, with the vote table). -/
theorem commit_in_leader (γ : RaftNames) (es G' : List EntryM) (c tm T : w64)
    (hw : PlogWf base0 es) (hc : uint.Z c ≤ es.length) (htm : uint.Z tm ≤ uint.Z T)
    (hlen : tm = T → uint.Z c ≤ G'.length) :
    votesTbl (GF := GF) γ ∗ logRecs γ base0 es ∗ commitIn γ es c tm ∗ leadFull γ T G' ⊢
      ⌜∀ j : w64, uint.Z j ≤ uint.Z c → plogTermAt base0 G' j = plogTermAt base0 es j⌝ := by
  iintro ⟨Htbl, #Hr, #Hci, #HL⟩
  icases leadFull_wf γ T G' $$ HL with ⟨%HwL, #HrL⟩
  have HlenL : plogLastIndexZ base0 G' = (G'.length : Int) := by
    unfold plogLastIndexZ; rw [base0_index]; simp
  ihave #Hcj := commitIn_j γ es c tm $$ Hci
  unfold commitJ
  icases Hcj with (%Hb0 | ⟨%t, %n, %G, #Hq, %Hcn⟩)
  · -- the bootstrap log, which both start with
    icases logRecs_boot_termAt γ es hw $$ Hr with %Hbe
    icases logRecs_boot_termAt γ G' HwL.1 $$ HrL with %HbL
    icases leadFull_boot γ T G' $$ HL with %Hbt
    have HbG := Hbt.1.length_le
    ipureintro
    intro j hj
    rw [← HbL j (by omega) (by omega), ← Hbe j (by omega) (by omega)]
  obtain ⟨Hcn, Htt, HGe⟩ := Hcn
  icases cq_base γ t n G $$ Hq with ⟨%HGn, #HGl⟩
  icases leadFull_wf γ t G $$ HGl with ⟨%HwG, #HrG⟩
  have Hn := (plogTermAt_some_range _ _ _ _ HGn).2
  icases full_match γ G es c HwG.1 hw
      (plogTermAt_in_range _ _ _ ⟨by rw [base0_index]; exact uint_Z_nonneg _, by omega⟩) HGe
      $$ HrG Hr with %HGall
  by_cases hT : t = T
  · subst hT
    have hlen := hlen (uint_Z_inj.mp (by omega))
    icases leadFull_agree γ t G' G c
        (plogTermAt_in_range _ _ _ ⟨by rw [base0_index]; exact uint_Z_nonneg _, by rw [HlenL]; omega⟩)
        (plogTermAt_in_range _ _ _ ⟨by rw [base0_index]; exact uint_Z_nonneg _, by omega⟩)
        $$ HL HGl with %HLG
    icases full_match γ G' G c HwL.1 HwG.1
        (plogTermAt_in_range _ _ _ ⟨by rw [base0_index]; exact uint_Z_nonneg _, by rw [HlenL]; omega⟩) HLG
        $$ HrL HrG with %HLGall
    ipureintro
    intro j hj
    rw [HLGall j hj, HGall j hj]
  · have Hlt : uint.Z t < uint.Z T := by
      have : uint.Z t ≠ uint.Z T := fun h => hT (uint_Z_inj.mp h)
      omega
    icases leadFull_camp γ T G' $$ HL with ⟨%ldr, %F0, #Hl, #Hc0, %Hpre⟩
    icases isCamp_ok γ ldr T F0 $$ Hc0 with %Hcok
    have Hcl := camp_last T F0 Hcok
    icases lc_core γ ((uint.Z T).toNat + 1) T t n G ldr F0 G'
        (by have := uint_Z_nonneg T; omega) Hlt HwL.1
        (by rw [plogTermAt_prefix _ F0 _ _ Hpre (by rw [Hcl]; rfl)]; exact Hcl)
        $$ Htbl Hq Hl Hc0 HrL with %HnL
    icases full_match γ G' G n HwL.1 HwG.1 (by rw [HnL]; rfl) (by rw [HnL, HGn])
        $$ HrL HrG with %HLG
    ipureintro
    intro j hj
    rw [HLG j (by omega), HGall j hj]

/-- **A commit certificate in a leader's log with pending entries**: as `commit_in_leader`, for the
leader's recorded full log `G'` followed by its pending entries `pl` (of its term `T`), which reach
`c` when `T` is the certificate's term. Past `G'` (only in that case: the bootstrap and an earlier
term's certificate are within `G'`), the certificate's full log `G` of `T` has `T` from `G'`'s
campaign log on (`recs_chain`), and so has `es` (`full_match`). -/
theorem commit_in_leader_pend (γ : RaftNames) (es G' pl : List EntryM) (c tm T : w64)
    (hw : PlogWf base0 es) (hc : uint.Z c ≤ es.length) (hes : es.length < 2 ^ 63)
    (htm : uint.Z tm ≤ uint.Z T) (hpl : ∀ e ∈ pl, e.Term' = T)
    (hlen : tm = T → uint.Z c ≤ G'.length + pl.length) :
    votesTbl (GF := GF) γ ∗ logRecs γ base0 es ∗ commitIn γ es c tm ∗ leadFull γ T G' ⊢
      ⌜∀ k : Nat, (k : Int) < uint.Z c → (G' ++ pl)[k]?.map EntryM.Term' = es[k]?.map EntryM.Term'⌝ := by
  iintro ⟨Htbl, #Hr, #Hci, #HL⟩
  -- within `G'`: `commit_in_leader`
  have hwithin : (∀ j : w64, uint.Z j ≤ uint.Z c → plogTermAt base0 G' j = plogTermAt base0 es j) →
      ∀ k : Nat, (k : Int) < uint.Z c → (G' ++ pl)[k]?.map EntryM.Term' = es[k]?.map EntryM.Term' := by
    intro Hag k hk
    have h := terms_of_plog G' es (uint.Z c).toNat (by omega) (fun j hj => Hag j (by omega)) k (by omega)
    have hke : k < es.length := by omega
    have hkG : k < G'.length := by
      have h0 := h
      rw [List.getElem?_eq_getElem hke] at h0
      rcases Nat.lt_or_ge k G'.length with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none h'] at h0; cases h0
    rw [List.getElem?_append_left hkG, h]
  by_cases hcl : uint.Z c ≤ G'.length
  · icases commit_in_leader γ es G' c tm T hw hc htm (fun _ => hcl) $$ [$Htbl $Hr $Hci $HL] with %Hag
    ipureintro; exact hwithin Hag
  icases leadFull_wf γ T G' $$ HL with ⟨%HwL, #HrL⟩
  have HlenL : plogLastIndexZ base0 G' = (G'.length : Int) := by
    unfold plogLastIndexZ; rw [base0_index]; simp
  ihave #Hcj := commitIn_j γ es c tm $$ Hci
  unfold commitJ
  icases Hcj with (%Hb0 | ⟨%t, %n, %G, #Hq, %Hcn⟩)
  · -- the bootstrap log is within `G'`
    icases leadFull_boot γ T G' $$ HL with %Hbt
    have HbG := Hbt.1.length_le
    have := Hb0.1
    exfalso; omega
  obtain ⟨Hcn, Htt, HGe⟩ := Hcn
  icases cq_base γ t n G $$ Hq with ⟨%HGn, #HGl⟩
  icases leadFull_wf γ t G $$ HGl with ⟨%HwG, #HrG⟩
  have Hn := (plogTermAt_some_range _ _ _ _ HGn).2
  have HlenG : plogLastIndexZ base0 G = (G.length : Int) := by
    unfold plogLastIndexZ; rw [base0_index]; simp
  icases full_match γ G es c HwG.1 hw
      (plogTermAt_in_range _ _ _ ⟨by rw [base0_index]; exact uint_Z_nonneg _, by omega⟩) HGe
      $$ HrG Hr with %HGall
  by_cases hT : t = T
  · subst hT
    have htmT : tm = t := uint_Z_inj.mp (by omega)
    have hlen := hlen htmT
    have hGW : uint.Z (W64 (G'.length : Int)) = G'.length := by word
    -- `G'` and `G` agree up to `G'`'s end
    icases leadFull_agree γ t G' G (W64 (G'.length : Int))
        (plogTermAt_in_range _ _ _ ⟨by rw [base0_index]; exact uint_Z_nonneg _, by rw [HlenL, hGW]; exact Int.le_refl _⟩)
        (plogTermAt_in_range _ _ _ ⟨by rw [base0_index]; exact uint_Z_nonneg _, by rw [hGW]; omega⟩)
        $$ HL HGl with %HLG
    icases full_match γ G' G (W64 (G'.length : Int)) HwL.1 HwG.1
        (plogTermAt_in_range _ _ _ ⟨by rw [base0_index]; exact uint_Z_nonneg _, by rw [HlenL, hGW]; exact Int.le_refl _⟩) HLG
        $$ HrL HrG with %HLGall
    -- `G` has `t` from the campaign log on
    icases leadFull_camp γ t G' $$ HL with ⟨%ldr, %F0, #Hl, #Hc0, %Hpre⟩
    icases recs_chain γ G ldr t F0 HwG.1 $$ Hl Hc0 HrG with %Hch
    obtain ⟨-, -, Hall⟩ := Hch n (by omega) HGn
    have HF0 : plogLastIndexZ base0 F0 = (F0.length : Int) := by
      unfold plogLastIndexZ; rw [base0_index]; simp
    have HF0le := Hpre.length_le
    ipureintro
    intro k hk
    have hk1 := plogTermAt_succ es k (by omega)
    by_cases hkL : k < G'.length
    · rw [List.getElem?_append_left hkL, ← plogTermAt_succ G' k (by omega), ← hk1,
        HLGall _ (by word), HGall _ (by word)]
    · have hkp : k - G'.length < pl.length := by omega
      rw [List.getElem?_append_right (by omega), List.getElem?_eq_getElem hkp, Option.map_some,
        hpl _ (List.getElem_mem hkp), ← hk1, ← HGall _ (by word), Hall _ ⟨by rw [HF0]; word, by word⟩]
  · -- an earlier term's certificate: `lc_core` puts its index within `G'`
    have Hlt : uint.Z t < uint.Z T := by
      have : uint.Z t ≠ uint.Z T := fun h => hT (uint_Z_inj.mp h)
      omega
    icases leadFull_camp γ T G' $$ HL with ⟨%ldr, %F0, #Hl, #Hc0, %Hpre⟩
    icases isCamp_ok γ ldr T F0 $$ Hc0 with %Hcok
    have Hcl := camp_last T F0 Hcok
    icases lc_core γ ((uint.Z T).toNat + 1) T t n G ldr F0 G'
        (by have := uint_Z_nonneg T; omega) Hlt HwL.1
        (by rw [plogTermAt_prefix _ F0 _ _ Hpre (by rw [Hcl]; rfl)]; exact Hcl)
        $$ Htbl Hq Hl Hc0 HrL with %HnL
    have := (plogTermAt_some_range _ _ _ _ HnL).2
    exfalso; omega

/-- **Log matching past a leader's records**: a leader `ldr` of `T` with records `esa` (at its
campaign log `F0`, or ending in an entry of `T`) and pending entries `pa` of `T`, and a log `esb`
with records holding an entry of `T` at a position `n` past `esa`: their terms agree up to `n`.
`esb`'s entries of `T` are the leader's (`recs_chain`): `T` from `F0` on, `F0`'s below; so `esb`
agrees with `esa` at `esa`'s end, hence below (`full_match`), and with `pa`'s `T` past it. -/
theorem pend_match (γ : RaftNames) (ldr T : w64) (F0 esa pa esb pb : List EntryM) (n : Nat)
    (hwa : PlogWf base0 esa) (hwb : PlogWf base0 esb) (hla : esa.length < 2 ^ 63)
    (hlb : esb.length < 2 ^ 63) (hpa : ∀ e ∈ pa, e.Term' = T) (hF0 : F0 <+: esa)
    (hlast : esa = F0 ∨ esa.getLast?.map EntryM.Term' = some T)
    (hn : esa.length ≤ n) (hna : n < esa.length + pa.length) (hnb : n < esb.length)
    (htb : esb[n]?.map EntryM.Term' = some T) :
    isLeader (GF := GF) γ ldr T ∗ isCamp γ ldr T F0 ∗ logRecs γ base0 esa ∗ logRecs γ base0 esb ⊢
      ⌜∀ k, k ≤ n → (esa ++ pa)[k]?.map EntryM.Term' = (esb ++ pb)[k]?.map EntryM.Term'⌝ := by
  iintro ⟨#Hl, #Hc, #Hra, #Hrb⟩
  icases isCamp_ok γ ldr T F0 $$ Hc with %Hcok
  icases recs_chain γ esb ldr T F0 hwb $$ Hl Hc Hrb with %Hch
  obtain ⟨-, HbF0, Hall⟩ := Hch (W64 ((n : Int) + 1)) (by word)
    (by rw [plogTermAt_succ _ _ (by omega)]; exact htb)
  have HF0 : plogLastIndexZ base0 F0 = (F0.length : Int) := by
    unfold plogLastIndexZ; rw [base0_index]; simp
  have HF0le := hF0.length_le
  -- `esb`'s terms past `F0`
  have hbT : ∀ k, F0.length ≤ k → k ≤ n → esb[k]?.map EntryM.Term' = some T := by
    intro k hk1 hk2
    rw [← plogTermAt_succ _ _ (by omega)]
    exact Hall _ ⟨by rw [HF0]; word, by word⟩
  -- `esa` and `esb` agree at `esa`'s end
  have hanchor : (plogTermAt base0 esa (W64 (esa.length : Int))).isSome ∧
      plogTermAt base0 esa (W64 (esa.length : Int)) = plogTermAt base0 esb (W64 (esa.length : Int)) := by
    rcases hlast with he | hl
    · subst he
      have Hcl := camp_last T esa Hcok
      rw [HF0] at Hcl HbF0
      rw [Hcl, HbF0]; exact ⟨rfl, rfl⟩
    · have hne : esa ≠ [] := by intro h; rw [h] at hl; cases hl
      have hm : 0 < esa.length := List.length_pos_iff.mpr hne
      rw [List.getLast?_eq_getElem?] at hl
      have hF0lt : F0.length < esa.length := by
        rcases Nat.lt_or_ge F0.length esa.length with h | h
        · exact h
        · exfalso
          have heq : F0 = esa := hF0.eq_of_length (by omega)
          subst heq
          have := Hcok.2 (W64 ((((F0.length - 1 : Nat)) : Int) + 1)) T
            (by rw [plogTermAt_succ _ _ (by omega)]; exact hl)
          omega
      have hW : W64 (esa.length : Int) = W64 ((((esa.length - 1 : Nat)) : Int) + 1) := by
        congr 1; omega
      rw [hW, plogTermAt_succ _ _ (by omega), plogTermAt_succ _ _ (by omega), hl,
        hbT _ (by omega) (by omega)]
      exact ⟨rfl, rfl⟩
  icases full_match γ esa esb _ hwa hwb hanchor.1 hanchor.2 $$ Hra Hrb with %Hag
  have hbelow := terms_of_plog esa esb esa.length hla
    (fun j hj => Hag j (by rw [show uint.Z (W64 (esa.length : Int)) = esa.length by word]; exact hj))
  ipureintro
  intro k hk
  rw [List.getElem?_append_left (show k < esb.length by omega)]
  by_cases hka : k < esa.length
  · rw [List.getElem?_append_left hka]; exact hbelow k hka
  · have hkp : k - esa.length < pa.length := by omega
    rw [List.getElem?_append_right (by omega), List.getElem?_eq_getElem hkp, Option.map_some,
      hpa _ (List.getElem_mem hkp), hbT k (by omega) hk]

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
  icases Hfi with ⟨%esi, %pi, %Hpi, -, -, Hli, -⟩
  icases Hfj with ⟨%esj, %pj, %Hpj, -, -, Hlj, -⟩
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
  icases Hfi with ⟨%esi, %pi, %Hpi, -, Hci, -, -⟩
  icases Hfj with ⟨%esj, %pj, %Hpj, -, Hcj, -, -⟩
  icases isCommitted_agree γ _ _ $$ Hci Hcj with %Hag
  exfalso
  apply hc
  rw [committedL_abs C σ _ _ Hpi.1, committedL_abs C σ _ _ Hpj.1,
    List.take_append_of_le_length (by omega), List.take_append_of_le_length (by omega)]
  rcases Hag with h | h
  · simp [isPrefix_of_prefix _ _ (logAbs_prefix C C.length 1 _ _ h)]
  · simp [isPrefix_of_prefix _ _ (logAbs_prefix C C.length 1 _ _ h)]

/-- **`LogMatchingInv` from the facts**: two servers with the same term at a position agree on raft's
terms below it (`logAbs_take_of_terms`). Both entries recorded: `logRecs_agree`, `terms_match_down`.
One a leader's pending entry, the other recorded: `pend_match`. Both pending: one leader of the term
(`isLeader_unique`), so one server. -/
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
  icases Hfi with ⟨%esi, %pi, %Hpi, #Hri, -, #Hli, -⟩
  icases Hfj with ⟨%esj, %pj, %Hpj, #Hrj, -, #Hlj, -⟩
  have hc0 := hc
  obtain ⟨hli, hbi, hwi, hlni, -, -, hT0i, hT1i, hpli, hpti⟩ := Hpi
  obtain ⟨hlj, hbj, hwj, hlnj, -, -, hT0j, hT1j, hplj, hptj⟩ := Hpj
  rw [List.mem_range] at hn
  rw [hli, hlj] at hn hc
  rw [logAbs_length, logAbs_length, List.length_append, List.length_append] at hn
  have ht : ((logAbs C C.length 1 (esi ++ pi))[n]?).map Etcdraft.Entry.term =
      ((logAbs C C.length 1 (esj ++ pj))[n]?).map Etcdraft.Entry.term :=
    Classical.byContradiction fun ht => hc (by simp [ht])
  have hrt := terms_of_absTerms C _ _ hbi hbj n (by simp only [List.length_append]; omega)
    (by simp only [List.length_append]; omega) ht
  rw [List.length_append] at hlni hlnj
  have hwi' := PlogWfR_append_left _ _ _ hwi
  have hwj' := PlogWfR_append_left _ _ _ hwj
  have hWi : PlogWf base0 esi :=
    PlogWfR_wf _ _ hwi' (by unfold plogLastIndexZ; rw [base0_index]; simp; omega)
  have hWj : PlogWf base0 esj :=
    PlogWfR_wf _ _ hwj' (by unfold plogLastIndexZ; rw [base0_index]; simp; omega)
  -- a pending entry's term, and its server a leader
  have hpend : ∀ (es p : List EntryM) (v : Etcdraft.Server), es.length ≤ n → n < (es ++ p).length →
      (v.state ≠ Etcdraft.leader → p = []) → (∀ e ∈ p, e.Term' = W64 v.currentTerm) →
      v.state = Etcdraft.leader ∧ (es ++ p)[n]?.map EntryM.Term' = some (W64 v.currentTerm) := by
    intro es p v h1 h2 hpl hpt
    rw [List.length_append] at h2
    have hkp : n - es.length < p.length := by omega
    refine ⟨Classical.byContradiction fun h => ?_, ?_⟩
    · rw [hpl h] at hkp; simp at hkp
    · rw [List.getElem?_append_right h1, List.getElem?_eq_getElem hkp, Option.map_some,
        hpt _ (List.getElem_mem hkp)]
  ihave %hT : ⌜∀ k, k ≤ n → (esi ++ pi)[k]?.map EntryM.Term' = (esj ++ pj)[k]?.map EntryM.Term'⌝ $$ []
  · by_cases hni : n < esi.length
    · by_cases hnj : n < esj.length
      · -- both recorded
        icases logRecs_agree γ _ _ _ _ $$ Hri Hrj with %Hra
        ipureintro
        rw [List.getElem?_append_left hni, List.getElem?_append_left hnj] at hrt
        have := terms_match_down esi esj hwi' hwj' (by omega) Hra n hni hrt
        intro k hk
        rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
        exact this k hk
      · -- `j`'s pending entry, `i`'s recorded one: `j` leads its term
        obtain ⟨hlj', htj⟩ := hpend esj pj _ (by omega) (by rw [List.length_append]; omega) hplj hptj
        simp only [hlj', ite_true]
        icases Hlj with ⟨#HLj, -, (%Hnil | ⟨%F0, #Hc, %HF0⟩)⟩
        · subst Hnil; exfalso; simp at hn; omega
        rw [htj, List.getElem?_append_left hni] at hrt
        icases pend_match γ j _ F0 esj pj esi pi n hWj hWi (by omega) (by omega) hptj HF0.1 HF0.2
            (by omega) (by omega) hni hrt $$ [$HLj $Hc $Hrj $Hri] with %H
        ipureintro; intro k hk; exact (H k hk).symm
    · obtain ⟨hli', hti⟩ := hpend esi pi _ (by omega) (by rw [List.length_append]; omega) hpli hpti
      simp only [hli', ite_true]
      icases Hli with ⟨#HLi, -, (%Hnil | ⟨%F0, #Hc, %HF0⟩)⟩
      · subst Hnil; exfalso; simp at hn; omega
      by_cases hnj : n < esj.length
      · -- `i`'s pending entry, `j`'s recorded one
        rw [hti, List.getElem?_append_left hnj] at hrt
        iapply pend_match γ i _ F0 esi pi esj pj n hWi hWj (by omega) (by omega) hpti HF0.1 HF0.2
            (by omega) (by omega) hnj hrt.symm
        iframe HLi Hc Hri Hrj
      · -- both pending: one leader of the term
        obtain ⟨hlj', htj⟩ := hpend esj pj _ (by omega) (by rw [List.length_append]; omega) hplj hptj
        simp only [hlj', ite_true]
        icases Hlj with ⟨#HLj, -⟩
        rw [hti, htj] at hrt
        simp only [Option.some.injEq] at hrt
        rw [hrt]
        icases isLeader_unique γ i j _ $$ HLi HLj with %He
        subst He
        exfalso; apply hc0; simp
  exfalso
  apply hc
  rw [logAbs_take_of_terms C _ _ n (by simp only [List.length_append]; omega)
    (by simp only [List.length_append]; omega) hT]; simp

/-- **`LeaderCompletenessInv` from the facts** (with raft's vote table and `CommitWithinLeader`):
every committed entry of a server is in every leader's log of a term above the entry's and at least
the server's (`commit_in_leader`, then the entries from the terms). -/
theorem allFacts_leaderCompleteness (γ : RaftNames) (C : List w64) (σ : Etcdraft.State)
    (hsrv : σ.server = confAbs C) (hcw : CommitWithinLeader σ) :
    votesTbl (GF := GF) γ ∗ allFacts γ C σ ⊢
      ⌜∀ i ∈ σ.server, ∀ idx0 < (committedL σ i).length, ∀ l ∈ σ.currentLeaders,
        (σ.s l).currentTerm > (((σ.s i).log[idx0]?).getD default).term →
        (σ.s l).currentTerm ≥ (σ.s i).currentTerm →
        (σ.s l).log[idx0]? = some (((σ.s i).log[idx0]?).getD default)⌝ := by
  iintro ⟨Htbl, #H⟩
  iunfold allFacts at H
  by_cases hc : ∀ i ∈ σ.server, ∀ idx0 < (committedL σ i).length, ∀ l ∈ σ.currentLeaders,
        (σ.s l).currentTerm > (((σ.s i).log[idx0]?).getD default).term →
        (σ.s l).currentTerm ≥ (σ.s i).currentTerm →
        (σ.s l).log[idx0]? = some (((σ.s i).log[idx0]?).getD default)
  · ipureintro; exact hc
  simp only [Classical.not_forall] at hc
  obtain ⟨x, hx, idx0, hidx, y, hy, -, hge, hne⟩ := hc
  have hy' : y ∈ σ.server := (List.mem_filter.1 hy).1
  have hyl : (σ.s y).state = Etcdraft.leader := by simpa using (List.mem_filter.1 hy).2
  have hcw' := hcw x hx y hy' hyl
  rw [hsrv] at hx hy'
  obtain ⟨i, hi, rfl⟩ := mem_confAbs_inv C x hx
  obtain ⟨l, hl, rfl⟩ := mem_confAbs_inv C y hy'
  ihave Hfi := H $$ %i %hi
  ihave Hfl := H $$ %l %hl
  iunfold srvFacts at Hfi Hfl
  icases Hfi with ⟨%esi, %pi, %Hpi, #Hri, -, -, #Hci⟩
  icases Hfl with ⟨%esl, %pl, %Hpl, -, -, Hll, -⟩
  simp only [hyl, ite_true]
  icases Hll with ⟨-, #HL, -⟩
  obtain ⟨hli, hbi, hwi, hlni, hc0, hc1, ht0, ht1, -⟩ := Hpi
  obtain ⟨hll, hbl, hwl, hlnl, -, -, hT0, hT1, -, hptl⟩ := Hpl
  rw [List.length_append] at hlni hlnl
  have hwi' : PlogWf base0 esi := PlogWfR_wf _ _ (PlogWfR_append_left _ _ _ hwi)
    (by unfold plogLastIndexZ; rw [base0_index]; simp; omega)
  have hcZ : uint.Z (W64 (σ.s (idAbs i)).commitIndex) = (σ.s (idAbs i)).commitIndex := by word
  have hcN : ((σ.s (idAbs i)).commitIndex.toNat : Int) = (σ.s (idAbs i)).commitIndex := by omega
  have htZ : uint.Z (W64 (σ.s (idAbs i)).currentTerm) = (σ.s (idAbs i)).currentTerm := by word
  have hTZ : uint.Z (W64 (σ.s (idAbs l)).currentTerm) = (σ.s (idAbs l)).currentTerm := by word
  icases commit_in_leader_pend γ esi esl pl (W64 (σ.s (idAbs i)).commitIndex) (W64 (σ.s (idAbs i)).currentTerm)
      (W64 (σ.s (idAbs l)).currentTerm) hwi' (by rw [hcZ]; omega) (by omega) (by rw [htZ, hTZ]; omega) hptl
      (fun he => by
        have := w64_of_int_inj _ _ ht0 ht1 hT0 hT1 he
        rw [hcZ]; have := hcw' this; rw [hll, logAbs_length, List.length_append] at this
        push_cast at this; exact this)
      $$ [$Htbl $Hri $Hci $HL] with %Hag
  exfalso
  apply hne
  -- the committed prefix's length is the commit index
  have hlen : (committedL σ (idAbs i)).length = (σ.s (idAbs i)).commitIndex.toNat := by
    unfold committedL; rw [List.length_take, hli, logAbs_length, List.length_append]; omega
  rw [hlen] at hidx
  have hag : ∀ k, k < (σ.s (idAbs i)).commitIndex.toNat →
      (esl ++ pl)[k]?.map EntryM.Term' = (esi ++ pi)[k]?.map EntryM.Term' := by
    intro k hk
    rw [Hag k (by rw [hcZ]; omega), List.getElem?_append_left (by omega)]
  -- `l`'s log reaches the commit index
  have hcl : (σ.s (idAbs i)).commitIndex.toNat ≤ (esl ++ pl).length := by
    have h1 := hag ((σ.s (idAbs i)).commitIndex.toNat - 1) (by omega)
    rw [List.getElem?_eq_getElem (by rw [List.length_append]; omega :
      (σ.s (idAbs i)).commitIndex.toNat - 1 < (esi ++ pi).length)] at h1
    rcases Nat.lt_or_ge ((σ.s (idAbs i)).commitIndex.toNat - 1) (esl ++ pl).length with h | h
    · omega
    · rw [List.getElem?_eq_none h] at h1; cases h1
  rw [hll, hli]
  exact logAbs_get_of_terms C (esl ++ pl) (esi ++ pi) _ idx0 hcl (by rw [List.length_append]; omega) hag hidx

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
  icases Hfi with ⟨%esi, %pi, %Hpi, -, -, -, -⟩
  exfalso; apply hc
  obtain ⟨hl, -, -, -, h0, h1, -⟩ := Hpi
  rw [hl, logAbs_length, List.length_append]; exact ⟨h0, by omega⟩

end ghost

end EtcdGrove
end Perennial
