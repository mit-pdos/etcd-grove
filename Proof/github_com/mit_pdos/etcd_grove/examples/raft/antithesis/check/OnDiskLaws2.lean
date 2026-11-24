/-
Lean-first (no Rocq counterpart). #33 S3b W4b (2026-11-23): `State.onDisk` in sections, for its
budget law (`Within/OnDisk.lean`) and its Go proof (`State__OnDisk.lean`).

`State.onDisk` is one `do` block whose `if`s without `else` become join points; unfolded whole, its
term is too large for `simp`/`split`. Here it is cut at each join point into a definition that
takes the rest as a continuation `K` (`OnDisk.onDisk_eq`, by `rfl`), so each section is taken
apart on its own with the rest atomic.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Laws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.OnDiskLaws

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntCheck
namespace OnDiskLaws2

variable (x : OnDisk)

/-! ## The sections (B 290-436, verbatim from `State.onDisk`) -/

/-- The guards up to `elect`'s. -/
def g1 (K : EvalM (Option State)) : EvalM (Option State) := do
  let s := x.s
  let n := x.n
  let w := x.w
  let me := s.cfg.server[n]!
  if x.more && (s.undo[n]!).isNone then return none
  if (← andM x.isApp (notM (do sendableIn x.ld x.ll x.ch x.tl (← x.fm)))) then return none
  if !decide ((← x.T1) ≥ x.T0) then return none
  if (← x.T1) != x.T0 && x.ro[n]! == leader then return none
  if (← andM x.elect (notM (andM (do pure ((← x.T1) == x.T0 + 1)) (fieldEq w.vote me)))) then
    return none
  K

/-- `adopt`'s guards. -/
def g2 (K : EvalM (Option State)) : EvalM (Option State) := do
  let s := x.s
  let n := x.n
  if (← x.adopt) then
    if !(← andM (pure x.hasM) (do pure ((← (← x.m).term_) == (← x.T1)))) then return none
    let t1 ← x.T1
    if !(List.range s.cfg.server.length).any (fun j => j != n && decide (s.currentTerm[j]! ≥ t1)) then
      return none
  K

/-- The vote's guards. -/
def g3 (K : EvalM (Option State)) : EvalM (Option State) := do
  let s := x.s
  let n := x.n
  let w := x.w
  if (← x.voted) then
    if (← x.V1) != [] then return none
    if !(← x.elect) then
      let ok ← andM (pure x.hasM) <| andM (do pure ((← (← x.m).typ) == go!"vote")) <|
        andM (do pure ((← (← x.m).from_) == (← need w.vote))) <|
        andM (do pure ((← (← x.m).term_) == (← x.T1))) <|
        andM (do pure (s.msgs.contains (← voteFact (← x.m))))
          (do pure (s.upToDate (← voteFact (← x.m)) n))
      if !ok then return none
  K

/-- A snapshot's guards. -/
def g4 (K : EvalM (Option State)) : EvalM (Option State) := do
  let w := x.w
  if x.snaps then
    let ok ← andM (notM x.leads) <| andM (pure x.hasM) <|
      andM (do pure ((← (← x.m).typ) == go!"snap")) <| andM x.stores <|
      andM (do pure ((← need w.snap).index == (← (← x.m).index_))) <|
      andM (do pure ((← need w.snap).term == (← (← x.m).logTerm_)))
        (do pure ((← need w.commit) == (← (← x.m).index_)))
    if !ok then return none
  K

/-- The entries' guards. -/
def g5 (K : EvalM (Option State)) : EvalM (Option State) := do
  let s := x.s
  let n := x.n
  let ld := x.ld
  let ll := x.ll
  let ch := x.ch
  let tl := x.tl
  if (← x.stores) then
    if (← x.leads) then
      if !(← andM (do pure ((← x.T1) == x.T0)) <|
            andM (do pure ((← x.first) == (x.L0.length : Int) + 1)) (do sendableIn ld ll ch tl (← x.f))) then
        return none
    else
      if !(← andM (pure x.hasM) <|
            andM (orM (do pure ((← (← x.m).typ) == go!"app")) (do pure ((← (← x.m).typ) == go!"snap")))
              (do pure ((← (← x.m).term_) == (← x.T1)))) then return none
      if (← andM (do pure ((← (← x.m).typ) == go!"snap")) (pure !x.snaps)) then return none
      if !(← andM (do snapOk ll (← x.m)) (do sendableIn ld ll ch tl (← x.f))) then return none
      if !(← s.prevOk n (← x.f)) then return none
      let k ← x.k
      let f ← x.f
      if !(decide (1 ≤ k) && decide (k ≤ f.entries.length)) then return none
      if !(← s.hasFirst n (← x.f) (k - 1)) then return none
      let f ← x.f
      if !(← entriesEqual (← x.es) (← subSeq f.entries k f.entries.length)) then return none
      let first ← x.first
      if first ≤ x.L0.length then
        if (← atE x.L0 first).term == (← atE (← x.es) 1).term then return none
      else if first != (x.L0.length : Int) + 1 then return none
  K

/-- The commit index's guards. -/
def g6 (K : EvalM (Option State)) : EvalM (Option State) := do
  let s := x.s
  let n := x.n
  let w := x.w
  let ld := x.ld
  let ll := x.ll
  let ch := x.ch
  let tl := x.tl
  if (← x.moved) then
    if !(← andM (do pure (decide ((← need w.commit) > s.commitIndex[n]!)))
          (do let c ← need w.commit; pure (decide (c ≤ (← x.L1).length)))) then return none
    if (← x.leads) then
      if !(← andM (do pure ((← x.T1) == x.T0)) (do sendableIn ld ll ch tl (← x.f))) then return none
    else
      if !(← andM (pure x.hasM) <| andM (do isReq (← x.m))
            (do pure ((← (← x.m).term_) == (← x.T1)))) then return none
      if !(← andM (do snapOk ll (← x.m)) (do sendableIn ld ll ch tl (← x.f))) then return none
      if !decide ((← need w.commit) ≤ (← x.f).commit) then return none
      if (← orM (do pure ((← (← x.m).typ) == go!"app")) (do pure ((← (← x.m).typ) == go!"snap"))) then
        if !(← andM (do s.prevOk n (← x.f))
              (orM x.stores (do let f ← x.f; s.hasFirst n f f.entries.length))) then return none
  K

/-- The successor: term and vote. -/
def u0 (K : Int → Bool → State → EvalM (Option State)) : EvalM (Option State) := do
  let s := x.s
  let n := x.n
  let w := x.w
  let t1 ← x.T1
  let voted ← x.voted
  let mut ns := { s with currentTerm := s.currentTerm.set n t1 }
  if voted then
    ns := { ns with voteTerm := s.voteTerm.set n t1, voteFor := s.voteFor.set n (← need w.vote) }
  K t1 voted ns

/-- The successor: log, commit index, role, confirmed; `elect`'s vote request. -/
def u1 (t1 : Int) (ns : State) (K : State → List Fact → EvalM (Option State)) : EvalM (Option State) := do
  let s := x.s
  let n := x.n
  let w := x.w
  let mut ns := ns
  ns := { ns with log := s.log.set n (← x.L1), commitIndex := s.commitIndex.set n (← need w.commit),
                  role := x.ro, confirmed := s.confirmed.set n (← x.conf1) }
  let mut msgs := s.msgs
  if (← x.elect) then msgs := lset.add msgs (s.voteRequest n t1)
  K ns msgs

/-- The successor: the ack. -/
def u2 (t1 : Int) (msgs : List Fact) (K : List Fact → EvalM (Option State)) : EvalM (Option State) := do
  let me := x.s.cfg.server[x.n]!
  let mut msgs := msgs
  if (← x.acks) then msgs := lset.add msgs (ackFact me (← x.f).src t1 (← x.ackAt))
  K msgs

/-- The successor: the vote record. -/
def u3 (t1 : Int) (voted : Bool) (K : List VoteRec → EvalM (Option State)) : EvalM (Option State) := do
  let s := x.s
  let w := x.w
  let me := s.cfg.server[x.n]!
  let mut votes := s.votes
  if voted then votes := lset.add votes { voter := me, term := t1, cand := ← need w.vote }
  K votes

/-- `pre`'s kept prefix. -/
def u4 (pre : Pre) (K : Pre → EvalM (Option State)) : EvalM (Option State) := do
  let mut pre := pre
  if (← x.stores) then
    pre := { pre with keep := (← x.first) - 1,
                      suffix := ← subSeq x.L0 (← x.first) x.L0.length }
  else
    pre := { pre with keep := x.L0.length }
  K pre

/-- `pre`'s ack. -/
def u5 (t1 : Int) (pre : Pre) (K : Pre → EvalM (Option State)) : EvalM (Option State) := do
  let me := x.s.cfg.server[x.n]!
  let mut pre := pre
  if (← x.acks) then pre := { pre with acks := [ackFact me (← x.f).src t1 (← x.ackAt)] }
  K pre

/-- `pre`'s low. -/
def u6 (pre : Pre) (K : Pre → EvalM (Option State)) : EvalM (Option State) := do
  let mut pre := pre
  if (← x.stores) then pre := { pre with low := ← x.first }
  K pre

/-- `undo`. -/
def u7 (ns : State) (pre : Pre) (K : State → EvalM (Option State)) : EvalM (Option State) := do
  let s := x.s
  let n := x.n
  let mut ns := ns
  if !x.more then
    ns := { ns with undo := s.undo.set n (some pre) }
  else
    let u := (s.undo[n]!).getD {}
    let suffix ← if pre.keep ≥ u.keep then pure u.suffix
      else do pure ((← subSeq x.L0 (pre.keep + 1) u.keep) ++ u.suffix)
    let nu := { u with keep := imin u.keep pre.keep, suffix, msgs := lset.union u.msgs pre.msgs,
                       votes := lset.union u.votes pre.votes, acks := lset.union u.acks pre.acks,
                       low := lowest u.low pre.low }
    ns := { ns with undo := s.undo.set n (some nu) }
  K ns

/-- `chain`, `termLen`. -/
def u8 (t1 : Int) (ns : State) (K : State → EvalM (Option State)) : EvalM (Option State) := do
  let tl := x.tl
  let mut ns := ns
  ns := { ns with chain := ← x.ch1 }
  if (← x.adv) then
    ns := { ns with termLen := tl.with t1 (imax (← x.old) (← x.newC).length) }
  else
    ns := { ns with termLen := tl }
  K ns

/-- Safety (B 422-436): `CommitSafety`. -/
def v1 (K : SSet → EvalM (Option State)) : EvalM (Option State) := do
  let mut viol := x.vi
  if (← andM x.adv (notM (do comparable x.ch (← x.newC)))) then viol := setAdd viol go!"CommitSafety"
  K viol

/-- `LeaderCompleteness`. -/
def v2 (t1 : Int) (viol : SSet) (K : SSet → EvalM (Option State)) : EvalM (Option State) := do
  let mut viol := viol
  if (← x.adv) then
    if (← anyM x.ll (fun p => andM (pure (decide (p.1 > t1))) (notM (do isPrefix (← x.newC) p.2)))) then
      viol := setAdd viol go!"LeaderCompleteness"
  K viol

/-- `LogMatching`. -/
def v3 (viol : SSet) (K : List Entry → Bool → SSet → EvalM (Option State)) : EvalM (Option State) := do
  let s := x.s
  let n := x.n
  let mut viol := viol
  let l1 ← x.L1
  let l0 := x.L0
  let changed := !(← entriesEqual l1 l0)
  if changed then
    if (← anyM (List.range s.cfg.server.length)
          (fun b => andM (pure (b != n)) (notM (matching l1 (s.log[b]!))))) then
      viol := setAdd viol go!"LogMatching"
  K l1 changed viol

/-- `CommittedEntriesPreserved`. -/
def v4 (l1 : List Entry) (changed : Bool) (viol : SSet) (K : SSet → EvalM (Option State)) :
    EvalM (Option State) := do
  let mut viol := viol
  if (← andM (orM (pure changed) x.adv)
        (notM (do isPrefix (← subSeq (← x.ch1) 1 (← need x.w.commit)) l1))) then
    viol := setAdd viol go!"CommittedEntriesPreserved"
  K viol

/-- `CommitBeyondConfirmed`, and the successor. -/
def v5 (t1 : Int) (ns : State) (viol : SSet) : EvalM (Option State) := do
  let mut viol := viol
  let c1 ← x.conf1
  if (← andM x.adv (do pure ((c1.term != t1) || decide ((← need x.w.commit) > c1.index)))) then
    viol := setAdd viol go!"CommitBeyondConfirmed"
  return some { ns with viol }

/-- Safety (B 422-436): `viol`. -/
def u9 (t1 : Int) (ns : State) : EvalM (Option State) :=
  v1 x fun viol => v2 x t1 viol fun viol => v3 x viol fun l1 changed viol =>
  v4 x l1 changed viol fun viol => v5 x t1 ns viol

/-- `pre` before its updates (B 349-352). -/
def pre0 (ns : State) : Pre :=
  { term := x.T0, voteTerm := x.s.voteTerm[x.n]!, voteFor := x.s.voteFor[x.n]!,
    commit := x.s.commitIndex[x.n]!, confirmed := x.s.confirmed[x.n]!,
    msgs := lset.minus ns.msgs x.s.msgs, votes := lset.minus ns.votes x.s.votes }

/-- The successor, from the sections. -/
def succ : EvalM (Option State) :=
  u0 x fun t1 voted ns =>
  u1 x t1 ns fun ns msgs =>
  u2 x t1 msgs fun msgs =>
  u3 x t1 voted fun votes =>
  let ns := { ns with msgs := msgs, votes := votes, leaders := x.ld, ledLog := x.ll }
  u4 x (pre0 x ns) fun pre =>
  u5 x t1 pre fun pre =>
  u6 x pre fun pre =>
  u7 x ns pre fun ns =>
  u8 x t1 ns fun ns =>
  u9 x t1 ns

set_option maxHeartbeats 4000000 in
/-- **`State.onDisk` in sections.** -/
theorem onDisk_eq (s : State) (n : Nat) (q : QItem) (more : Bool) (ro : List Str) (ld : List LeaderRec)
    (ll : TermFn (List Entry)) (ch : List Entry) (tl : TermFn Int) (vi : SSet) :
    s.onDisk n q more ro ld ll ch tl vi =
      let x : OnDisk := { s, n, q, more, ro, ld, ll, ch, tl, vi }
      g1 x (g2 x (g3 x (g4 x (g5 x (g6 x (succ x)))))) := rfl

/-! ## Taking a section apart (goal form: `apply` fails cleanly where a pattern does not match) -/

theorem w_bind {α β : Type} {m : EvalM α} {f : α → EvalM β} {r : β} {P : Prop}
    (k : ∀ v, m = .ok v → f v = .ok r → P) : (m >>= f) = .ok r → P := fun h => by
  obtain ⟨v, hv, h⟩ := bind_ok h; exact k v hv h

theorem w_ite {α : Type} {c : Prop} [Decidable c] {a b : EvalM α} {r : α} {P : Prop}
    (ka : c → a = .ok r → P) (kb : ¬c → b = .ok r → P) : (if c then a else b) = .ok r → P := fun h => by
  by_cases hc : c
  · simp only [hc, ite_true] at h; exact ka hc h
  · simp only [hc, ite_false] at h; exact kb hc h

theorem w_none {s' : State} {P : Prop} : (pure none : EvalM (Option State)) = .ok (some s') → P := fun h => by
  cases h

/-- Takes a guard section apart: every path ends in `return none` or in the continuation. -/
macro "od_walk" : tactic => `(tactic| repeat' (first
  | (with_reducible apply w_bind; intro _ _)
  | (with_reducible apply w_ite <;> intro _)
  | (with_reducible apply w_none)
  | (with_reducible exact fun h => h)))

/-! ## The guards pass a successor on -/

variable {x}

theorem g1_some {K : EvalM (Option State)} {s' : State} (h : g1 x K = .ok (some s')) : K = .ok (some s') := by
  unfold g1 at h
  dsimp only at h
  split at h
  · cases h
  obtain ⟨_, -, h⟩ := bind_ok h
  split at h
  · cases h
  obtain ⟨_, -, h⟩ := bind_ok h
  split at h
  · cases h
  obtain ⟨_, -, h⟩ := bind_ok h
  split at h
  · cases h
  obtain ⟨_, -, h⟩ := bind_ok h
  split at h
  · cases h
  exact h

theorem g2_some {K : EvalM (Option State)} {s' : State} (h : g2 x K = .ok (some s')) : K = .ok (some s') := by
  unfold g2 at h
  dsimp only at h
  obtain ⟨ad, -, h⟩ := bind_ok h
  split at h
  · obtain ⟨_, -, h⟩ := bind_ok h
    split at h
    · cases h
    obtain ⟨_, -, h⟩ := bind_ok h
    split at h
    · cases h
    exact h
  · exact h

theorem g3_some {K : EvalM (Option State)} {s' : State} (h : g3 x K = .ok (some s')) : K = .ok (some s') := by
  unfold g3 at h
  dsimp only at h
  obtain ⟨_, -, h⟩ := bind_ok h
  split at h
  · obtain ⟨_, -, h⟩ := bind_ok h
    split at h
    · cases h
    obtain ⟨_, -, h⟩ := bind_ok h
    split at h
    · obtain ⟨_, -, h⟩ := bind_ok h
      split at h
      · cases h
      exact h
    · exact h
  · exact h

theorem g4_some {K : EvalM (Option State)} {s' : State} (h : g4 x K = .ok (some s')) : K = .ok (some s') := by
  unfold g4 at h
  dsimp only at h
  split at h
  · obtain ⟨_, -, h⟩ := bind_ok h
    split at h
    · cases h
    exact h
  · exact h

theorem g6_some {K : EvalM (Option State)} {s' : State} (h : g6 x K = .ok (some s')) : K = .ok (some s') := by
  unfold g6 at h
  dsimp only at h
  obtain ⟨_, -, h⟩ := bind_ok h
  split at h
  · obtain ⟨_, -, h⟩ := bind_ok h
    split at h
    · cases h
    obtain ⟨_, -, h⟩ := bind_ok h
    split at h
    · obtain ⟨_, -, h⟩ := bind_ok h
      split at h
      · cases h
      exact h
    · obtain ⟨_, -, h⟩ := bind_ok h
      split at h
      · cases h
      obtain ⟨_, -, h⟩ := bind_ok h
      split at h
      · cases h
      obtain ⟨_, -, h⟩ := bind_ok h
      obtain ⟨_, -, h⟩ := bind_ok h
      split at h
      · cases h
      obtain ⟨_, -, h⟩ := bind_ok h
      split at h
      · obtain ⟨_, -, h⟩ := bind_ok h
        split at h
        · cases h
        exact h
      · exact h
  · exact h

theorem ite_bool {α : Type} {b : Bool} {a c : EvalM α} {r : α} (h : (if b = true then a else c) = .ok r) :
    (b = true ∧ a = .ok r) ∨ (b = false ∧ c = .ok r) := by
  cases b
  · exact .inr ⟨rfl, by simpa using h⟩
  · exact .inl ⟨rfl, by simpa using h⟩

theorem andM_true {a b : EvalM Bool} (h : andM a b = .ok true) : a = .ok true ∧ b = .ok true := by
  obtain ⟨v, hv, h1, h2⟩ := andM_ok h
  cases v
  · exact absurd (h2 rfl) (by simp)
  · exact ⟨hv, h1 rfl⟩

theorem sendable_len {ld : List LeaderRec} {ll : TermFn (List Entry)} {ch : List Entry} {tl : TermFn Int}
    {f : AppendFact} (h : sendableIn ld ll ch tl f = .ok true) :
    ∃ p ∈ ll, f.prevLogIndex + f.entries.length ≤ p.2.length := by
  unfold sendableIn at h
  dsimp only at h
  split at h
  · cases h
  split at h
  · cases h
  obtain ⟨l, hl, h⟩ := bind_ok h
  split at h
  · cases h
  rename_i hle
  obtain ⟨p, hp, -, hp2⟩ := TermFn.get_mem hl
  refine ⟨p, hp, ?_⟩
  rw [hp2]
  simpa using hle

theorem f_leads {f : AppendFact} (hl : x.leads = .ok true) (hs : x.stores = .ok true) (hf : x.f = .ok f) :
    ∃ fi es, x.first = .ok fi ∧ x.es = .ok es ∧ f.prevLogIndex = fi - 1 ∧ f.entries = es := by
  unfold OnDisk.f at hf
  obtain ⟨ld, hld, hf⟩ := bind_ok hf
  rw [hl] at hld; cases hld
  dsimp only at hf
  simp only [ite_true] at hf
  obtain ⟨t1, -, hf⟩ := bind_ok hf
  obtain ⟨es, hes, hf⟩ := bind_ok hf
  obtain ⟨st, hst, hf⟩ := bind_ok hf
  rw [hs] at hst; cases hst
  simp only [ite_true] at hf
  obtain ⟨fi, hfi, hf⟩ := bind_ok hf
  refine ⟨fi, es, hfi, hes, ?_⟩
  obtain ⟨a, -, hf⟩ := bind_ok hf
  split at hf
  · obtain ⟨l, -, hf⟩ := bind_ok hf
    obtain ⟨fi2, -, hf⟩ := bind_ok hf
    obtain ⟨m, -, hf⟩ := bind_ok hf
    split at hf
    · obtain ⟨c, -, hf⟩ := bind_ok hf
      cases hf; exact ⟨rfl, rfl⟩
    · cases hf; exact ⟨rfl, rfl⟩
  · obtain ⟨m, -, hf⟩ := bind_ok hf
    split at hf
    · obtain ⟨c, -, hf⟩ := bind_ok hf
      cases hf; exact ⟨rfl, rfl⟩
    · cases hf; exact ⟨rfl, rfl⟩

theorem subSeq_len_eq {l r : List Entry} {m k : Int} (h1 : 1 ≤ m) (h2 : m ≤ k) (h : subSeq l m k = .ok r) :
    (r.length : Int) = k - m + 1 := by
  unfold subSeq at h
  split at h
  · omega
  split at h
  · cases h
  cases h
  simp only [List.length_take, List.length_drop]
  omega

theorem entriesEqual_len {a b : List Entry} (h : entriesEqual a b = .ok true) : a.length = b.length := by
  unfold entriesEqual at h
  split at h
  · cases h
  · rename_i h'; exact Classical.not_not.1 h'

theorem k_eq {k : Int} (h : x.k = .ok k) : ∃ fi f, x.first = .ok fi ∧ x.f = .ok f ∧ k = fi - f.prevLogIndex := by
  unfold OnDisk.k at h
  obtain ⟨fi, hfi, h⟩ := bind_ok h
  obtain ⟨f, hf, h⟩ := bind_ok h
  cases h
  exact ⟨fi, f, hfi, hf, rfl⟩

/-- The entries' guards pass a successor on, and where `stores`, the new entries end within a leader
log of `ll` (`SendableIn` of the request). -/
theorem g5_some {K : EvalM (Option State)} {s' : State} (h : g5 x K = .ok (some s')) :
    K = .ok (some s') ∧ (x.stores = .ok true → ∃ fi es, ∃ p ∈ x.ll, x.first = .ok fi ∧ x.es = .ok es ∧
      fi - 1 + es.length ≤ p.2.length) := by
  unfold g5 at h
  dsimp only at h
  obtain ⟨st, hst, h⟩ := bind_ok h
  rcases ite_bool h with ⟨hst1, h⟩ | ⟨hst1, h⟩
  · obtain ⟨ld, hld, h⟩ := bind_ok h
    rcases ite_bool h with ⟨hld1, h⟩ | ⟨hld1, h⟩
    · obtain ⟨c, hc, h⟩ := bind_ok h
      split at h
      · cases h
      rename_i hc1
      refine ⟨h, fun _ => ?_⟩
      have hc' : c = true := by simpa using hc1
      subst hc'
      obtain ⟨-, h2⟩ := andM_true hc
      obtain ⟨h3, h4⟩ := andM_true h2
      obtain ⟨fi, hfi, h3⟩ := bind_ok h3
      obtain ⟨f, hf, h4⟩ := bind_ok h4
      have hld' : x.leads = .ok true := by rw [hld, hld1]
      have hst' : x.stores = .ok true := by rw [hst, hst1]
      obtain ⟨fi', es, hfi', hes, hp, he⟩ := f_leads hld' hst' hf
      rw [hfi] at hfi'; cases hfi'
      obtain ⟨p, hpm, hlen⟩ := sendable_len h4
      refine ⟨fi, es, p, hpm, hfi, hes, ?_⟩
      rw [hp, he] at hlen; omega
    · obtain ⟨_, -, h⟩ := bind_ok h
      split at h
      · cases h
      obtain ⟨_, -, h⟩ := bind_ok h
      split at h
      · cases h
      obtain ⟨c3, hc3, h⟩ := bind_ok h
      split at h
      · cases h
      rename_i hc31
      have hc3' : c3 = true := by simpa using hc31
      subst hc3'
      obtain ⟨-, h4⟩ := andM_true hc3
      obtain ⟨f, hf, h4⟩ := bind_ok h4
      obtain ⟨_, -, h⟩ := bind_ok h
      obtain ⟨_, -, h⟩ := bind_ok h
      split at h
      · cases h
      obtain ⟨k, hk, h⟩ := bind_ok h
      obtain ⟨f', hf', h⟩ := bind_ok h
      rw [hf] at hf'; cases hf'
      split at h
      · cases h
      rename_i h5
      obtain ⟨_, -, h⟩ := bind_ok h
      obtain ⟨_, -, h⟩ := bind_ok h
      split at h
      · cases h
      obtain ⟨f', hf', h⟩ := bind_ok h
      rw [hf] at hf'; cases hf'
      obtain ⟨es, hes, h⟩ := bind_ok h
      obtain ⟨sub, hsub, h⟩ := bind_ok h
      obtain ⟨e, he, h⟩ := bind_ok h
      split at h
      · cases h
      rename_i h7
      have he' : e = true := by simpa using h7
      subst he'
      refine ⟨?_, fun _ => ?_⟩
      · obtain ⟨_, -, h⟩ := bind_ok h
        split at h
        · obtain ⟨_, -, h⟩ := bind_ok h
          obtain ⟨_, -, h⟩ := bind_ok h
          obtain ⟨_, -, h⟩ := bind_ok h
          split at h
          · cases h
          exact h
        · split at h
          · cases h
          exact h
      · obtain ⟨fi, f', hfi, hf', hk'⟩ := k_eq hk
        rw [hf] at hf'; cases hf'
        have h5' : 1 ≤ k ∧ k ≤ f.entries.length := by simpa using h5
        have hl1 := entriesEqual_len he
        have hl2 := subSeq_len_eq h5'.1 h5'.2 hsub
        obtain ⟨p, hpm, hlen⟩ := sendable_len h4
        refine ⟨fi, es, p, hpm, hfi, hes, ?_⟩
        omega
  · refine ⟨h, fun h' => ?_⟩
    rw [hst] at h'; cases h'; cases hst1

/-! ## The successor's sections -/

/-- The successor's term and vote (`u0`). -/
def ns0 (x : OnDisk) (t1 : Int) (voted : Bool) (vf : List Str) : State :=
  { x.s with currentTerm := x.s.currentTerm.set x.n t1,
             voteTerm := if voted then x.s.voteTerm.set x.n t1 else x.s.voteTerm, voteFor := vf }

theorem u0_ok {K : Int → Bool → State → EvalM (Option State)} {r : Option State} (h : u0 x K = .ok r) :
    ∃ t1 voted vf, x.T1 = .ok t1 ∧ x.voted = .ok voted ∧
      K t1 voted (ns0 x t1 voted vf) = .ok r := by
  unfold u0 at h
  obtain ⟨t1, ht1, h⟩ := bind_ok h
  obtain ⟨vd, hvd, h⟩ := bind_ok h
  rcases ite_bool h with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · obtain ⟨v, -, h⟩ := bind_ok h
    exact ⟨t1, true, _, ht1, hvd, h⟩
  · exact ⟨t1, false, _, ht1, hvd, h⟩

theorem u1_ok {t1 : Int} {ns : State} {K : State → List Fact → EvalM (Option State)} {r : Option State}
    (h : u1 x t1 ns K = .ok r) :
    ∃ L1 c c1 el, x.L1 = .ok L1 ∧ need x.w.commit = .ok c ∧ x.conf1 = .ok c1 ∧ x.elect = .ok el ∧
      K { ns with log := x.s.log.set x.n L1, commitIndex := x.s.commitIndex.set x.n c, role := x.ro,
                  confirmed := x.s.confirmed.set x.n c1 }
        (if el then lset.add x.s.msgs (x.s.voteRequest x.n t1) else x.s.msgs) = .ok r := by
  unfold u1 at h
  obtain ⟨L1, hL1, h⟩ := bind_ok h
  obtain ⟨c, hc, h⟩ := bind_ok h
  obtain ⟨c1, hc1, h⟩ := bind_ok h
  obtain ⟨el, hel, h⟩ := bind_ok h
  rcases ite_bool h with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · exact ⟨L1, c, c1, true, hL1, hc, hc1, hel, h⟩
  · exact ⟨L1, c, c1, false, hL1, hc, hc1, hel, h⟩

theorem u2_ok {t1 : Int} {msgs : List Fact} {K : List Fact → EvalM (Option State)} {r : Option State}
    (h : u2 x t1 msgs K = .ok r) :
    ∃ msgs', K msgs' = .ok r ∧ ((x.acks = .ok false ∧ msgs' = msgs) ∨
      ∃ f a, x.acks = .ok true ∧ x.f = .ok f ∧ x.ackAt = .ok a ∧
        msgs' = lset.add msgs (ackFact (x.s.cfg.server[x.n]!) f.src t1 a)) := by
  unfold u2 at h
  obtain ⟨ac, hac, h⟩ := bind_ok h
  rcases ite_bool h with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · obtain ⟨f, hf, h⟩ := bind_ok h
    obtain ⟨a, ha, h⟩ := bind_ok h
    exact ⟨_, h, .inr ⟨f, a, hac, hf, ha, rfl⟩⟩
  · exact ⟨_, h, .inl ⟨hac, rfl⟩⟩

theorem u3_ok {t1 : Int} {voted : Bool} {K : List VoteRec → EvalM (Option State)} {r : Option State}
    (h : u3 x t1 voted K = .ok r) :
    ∃ votes', K votes' = .ok r ∧ ((voted = false ∧ votes' = x.s.votes) ∨
      ∃ v, voted = true ∧ votes' = lset.add x.s.votes { voter := x.s.cfg.server[x.n]!, term := t1, cand := v }) := by
  unfold u3 at h
  rcases ite_bool h with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · obtain ⟨v, -, h⟩ := bind_ok h
    exact ⟨_, h, .inr ⟨v, rfl, rfl⟩⟩
  · exact ⟨_, h, .inl ⟨rfl, rfl⟩⟩

theorem u4_ok {pre : Pre} {K : Pre → EvalM (Option State)} {r : Option State} (h : u4 x pre K = .ok r) :
    ∃ pre', K pre' = .ok r ∧ ((x.stores = .ok false ∧ pre' = { pre with keep := x.L0.length }) ∨
      ∃ fi suf, x.stores = .ok true ∧ x.first = .ok fi ∧ subSeq x.L0 fi x.L0.length = .ok suf ∧
        pre' = { pre with keep := fi - 1, suffix := suf }) := by
  unfold u4 at h
  obtain ⟨st, hst, h⟩ := bind_ok h
  rcases ite_bool h with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · obtain ⟨fi, hfi, h⟩ := bind_ok h
    obtain ⟨fi', hfi', h⟩ := bind_ok h
    rw [hfi] at hfi'; cases hfi'
    obtain ⟨suf, hsuf, h⟩ := bind_ok h
    exact ⟨_, h, .inr ⟨fi, suf, hst, hfi, hsuf, rfl⟩⟩
  · exact ⟨_, h, .inl ⟨hst, rfl⟩⟩

theorem u5_ok {t1 : Int} {pre : Pre} {K : Pre → EvalM (Option State)} {r : Option State}
    (h : u5 x t1 pre K = .ok r) :
    ∃ pre', K pre' = .ok r ∧ ((x.acks = .ok false ∧ pre' = pre) ∨
      ∃ f a, x.acks = .ok true ∧ x.f = .ok f ∧ x.ackAt = .ok a ∧
        pre' = { pre with acks := [ackFact (x.s.cfg.server[x.n]!) f.src t1 a] }) := by
  unfold u5 at h
  obtain ⟨ac, hac, h⟩ := bind_ok h
  rcases ite_bool h with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · obtain ⟨f, hf, h⟩ := bind_ok h
    obtain ⟨a, ha, h⟩ := bind_ok h
    exact ⟨_, h, .inr ⟨f, a, hac, hf, ha, rfl⟩⟩
  · exact ⟨_, h, .inl ⟨hac, rfl⟩⟩

theorem u6_ok {pre : Pre} {K : Pre → EvalM (Option State)} {r : Option State} (h : u6 x pre K = .ok r) :
    ∃ pre', K pre' = .ok r ∧ ((x.stores = .ok false ∧ pre' = pre) ∨
      ∃ fi, x.stores = .ok true ∧ x.first = .ok fi ∧ pre' = { pre with low := fi }) := by
  unfold u6 at h
  obtain ⟨st, hst, h⟩ := bind_ok h
  rcases ite_bool h with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · obtain ⟨fi, hfi, h⟩ := bind_ok h
    exact ⟨_, h, .inr ⟨fi, hst, hfi, rfl⟩⟩
  · exact ⟨_, h, .inl ⟨hst, rfl⟩⟩

/-- The merged write `undo[n]` takes when `more` (B 409-418). -/
def nuOf (u pre : Pre) (suffix : List Entry) : Pre :=
  { u with keep := imin u.keep pre.keep, suffix, msgs := lset.union u.msgs pre.msgs,
           votes := lset.union u.votes pre.votes, acks := lset.union u.acks pre.acks,
           low := lowest u.low pre.low }

theorem u7_ok {ns : State} {pre : Pre} {K : State → EvalM (Option State)} {r : Option State}
    (h : u7 x ns pre K = .ok r) :
    ∃ p, K { ns with undo := x.s.undo.set x.n (some p) } = .ok r ∧ ((x.more = false ∧ p = pre) ∨
      ∃ suf, x.more = true ∧ p = nuOf ((x.s.undo[x.n]!).getD {}) pre suf ∧
        ((pre.keep ≥ ((x.s.undo[x.n]!).getD {}).keep ∧ suf = ((x.s.undo[x.n]!).getD {}).suffix) ∨
         (pre.keep < ((x.s.undo[x.n]!).getD {}).keep ∧ ∃ l, subSeq x.L0 (pre.keep + 1)
            ((x.s.undo[x.n]!).getD {}).keep = .ok l ∧ suf = l ++ ((x.s.undo[x.n]!).getD {}).suffix))) := by
  unfold u7 at h
  cases hm : x.more
  · rw [hm] at h
    simp only [Bool.not_false, ite_true] at h
    exact ⟨pre, h, .inl ⟨rfl, rfl⟩⟩
  · rw [hm] at h
    simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h
    split at h
    · rename_i hk
      exact ⟨_, h, .inr ⟨_, rfl, rfl, .inl ⟨hk, rfl⟩⟩⟩
    · rename_i hk
      obtain ⟨l, hl, h⟩ := bind_ok h
      exact ⟨_, h, .inr ⟨_, rfl, rfl, .inr ⟨by omega, l, hl, rfl⟩⟩⟩

theorem u8_ok {t1 : Int} {ns : State} {K : State → EvalM (Option State)} {r : Option State}
    (h : u8 x t1 ns K = .ok r) :
    ∃ c1 tl', x.ch1 = .ok c1 ∧ K { ns with chain := c1, termLen := tl' } = .ok r ∧
      ((x.adv = .ok false ∧ tl' = x.tl) ∨
       ∃ o nc, x.adv = .ok true ∧ x.old = .ok o ∧ x.newC = .ok nc ∧ tl' = x.tl.with t1 (imax o nc.length)) := by
  unfold u8 at h
  obtain ⟨c1, hc1, h⟩ := bind_ok h
  obtain ⟨ad, had, h⟩ := bind_ok h
  rcases ite_bool h with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · obtain ⟨o, ho, h⟩ := bind_ok h
    obtain ⟨nc, hnc, h⟩ := bind_ok h
    exact ⟨c1, _, hc1, h, .inr ⟨o, nc, had, ho, hnc, rfl⟩⟩
  · exact ⟨c1, _, hc1, h, .inl ⟨had, rfl⟩⟩

theorem v1_ok {K : SSet → EvalM (Option State)} {r : Option State} (h : v1 x K = .ok r) : ∃ v, K v = .ok r := by
  unfold v1 at h
  obtain ⟨_, -, h⟩ := bind_ok h
  rcases ite_bool h with ⟨-, h⟩ | ⟨-, h⟩ <;> exact ⟨_, h⟩

theorem v2_ok {t1 : Int} {viol : SSet} {K : SSet → EvalM (Option State)} {r : Option State}
    (h : v2 x t1 viol K = .ok r) : ∃ v, K v = .ok r := by
  unfold v2 at h
  obtain ⟨_, -, h⟩ := bind_ok h
  rcases ite_bool h with ⟨-, h⟩ | ⟨-, h⟩
  · obtain ⟨_, -, h⟩ := bind_ok h
    rcases ite_bool h with ⟨-, h⟩ | ⟨-, h⟩ <;> exact ⟨_, h⟩
  · exact ⟨_, h⟩

theorem v3_ok {viol : SSet} {K : List Entry → Bool → SSet → EvalM (Option State)} {r : Option State}
    (h : v3 x viol K = .ok r) : ∃ l c v, K l c v = .ok r := by
  unfold v3 at h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨_, -, h⟩ := bind_ok h
  rcases ite_bool h with ⟨-, h⟩ | ⟨-, h⟩
  · obtain ⟨_, -, h⟩ := bind_ok h
    rcases ite_bool h with ⟨-, h⟩ | ⟨-, h⟩ <;> exact ⟨_, _, _, h⟩
  · exact ⟨_, _, _, h⟩

theorem v4_ok {l1 : List Entry} {c : Bool} {viol : SSet} {K : SSet → EvalM (Option State)} {r : Option State}
    (h : v4 x l1 c viol K = .ok r) : ∃ v, K v = .ok r := by
  unfold v4 at h
  obtain ⟨_, -, h⟩ := bind_ok h
  rcases ite_bool h with ⟨-, h⟩ | ⟨-, h⟩ <;> exact ⟨_, h⟩

theorem v5_some {t1 : Int} {ns s' : State} {viol : SSet} (h : v5 x t1 ns viol = .ok (some s')) :
    s' = { ns with viol := s'.viol } := by
  unfold v5 at h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨_, -, h⟩ := bind_ok h
  rcases ite_bool h with ⟨-, h⟩ | ⟨-, h⟩ <;> cases h <;> rfl

theorem u9_some {t1 : Int} {ns s' : State} (h : u9 x t1 ns = .ok (some s')) :
    s' = { ns with viol := s'.viol } := by
  unfold u9 at h
  obtain ⟨_, h⟩ := v1_ok h
  obtain ⟨_, h⟩ := v2_ok h
  obtain ⟨_, _, _, h⟩ := v3_ok h
  obtain ⟨_, h⟩ := v4_ok h
  exact v5_some h

/-! ## The values within the budget -/

section values
variable {b E : Nat}

/-- What `g5_some` gives: where `stores`, the new entries end within a leader log of `ll`. -/
def StoresFit (x : OnDisk) : Prop :=
  x.stores = .ok true → ∃ fi es, ∃ p ∈ x.ll, x.first = .ok fi ∧ x.es = .ok es ∧ fi - 1 + es.length ≤ p.2.length

theorem bigOk_zero : bigOk 0 := by unfold bigOk; omega

theorem T1_bigOk (hW : x.Within b E) {t : Int} (h : x.T1 = .ok t) : bigOk t := by
  have hn := hW.2.1.1.1
  unfold OnDisk.T1 at h
  rw [show x.w = x.q.ev from rfl, need_ok h] at *
  rw [need_ok h] at hn
  exact numOk_bigOk hn

theorem commit_bigOk (hW : x.Within b E) {c : Int} (h : need x.w.commit = .ok c) : bigOk c := by
  have hn := hW.2.1.1.2.1
  rw [show x.w = x.q.ev from rfl] at h
  rw [need_ok h] at hn
  exact numOk_bigOk hn

theorem subSeq_mem {l r : List Entry} {a c : Int} (h : subSeq l a c = .ok r) {e : Entry} (he : e ∈ r) : e ∈ l := by
  unfold subSeq at h
  split at h
  · cases h; cases he
  split at h
  · cases h
  cases h
  exact List.mem_of_mem_drop (List.mem_of_mem_take he)

theorem ll_within (hW : x.Within b E) {p : Int × List Entry} (hp : p ∈ x.ll) : bigOk p.1 ∧ logWithin b E p.2 :=
  hW.2.2.2.2.2.2.2.1 p hp

theorem L0_within (hW : x.Within b E) : logWithin b E x.L0 := by
  unfold OnDisk.L0
  exact getElem!_mem' hW.1.2.2.2.2.2.2.2.2.2.1 (show logWithin b E [] by simp [logWithin])

theorem fm_entries (hW : x.Within b E) {f : AppendFact} (h : x.fm = .ok f) :
    ∀ e ∈ f.entries, bigOk e.term ∧ e.chgSize ≤ E := by
  unfold OnDisk.fm at h
  obtain ⟨m, hm, h⟩ := bind_ok h
  have hmw := OnDisk.m_within hW hm
  unfold reqFactIn at h
  obtain ⟨ty, -, h⟩ := bind_ok h
  split at h
  · obtain ⟨t, -, h⟩ := bind_ok h
    dsimp only at h
    split at h
    · obtain ⟨l, hl, h⟩ := bind_ok h
      obtain ⟨k', -, h⟩ := bind_ok h
      obtain ⟨es, hes, h⟩ := bind_ok h
      obtain ⟨p, hp, -, hp2⟩ := TermFn.get_mem hl
      obtain ⟨src, -, h⟩ := bind_ok h
      obtain ⟨dst, -, h⟩ := bind_ok h
      obtain ⟨t', -, h⟩ := bind_ok h
      obtain ⟨k, -, h⟩ := bind_ok h
      cases h
      intro e he
      have := (ll_within hW hp).2.2 e (by rw [hp2]; exact subSeq_mem hes he)
      exact this
    · obtain ⟨es, hes, h⟩ := bind_ok h
      cases hes
      obtain ⟨src, -, h⟩ := bind_ok h
      obtain ⟨dst, -, h⟩ := bind_ok h
      obtain ⟨t', -, h⟩ := bind_ok h
      obtain ⟨k, -, h⟩ := bind_ok h
      cases h
      intro e he; cases he
  · unfold toAppendFact at h
    obtain ⟨src, -, h⟩ := bind_ok h
    obtain ⟨dst, -, h⟩ := bind_ok h
    obtain ⟨t, -, h⟩ := bind_ok h
    obtain ⟨p, -, h⟩ := bind_ok h
    obtain ⟨pt, -, h⟩ := bind_ok h
    obtain ⟨es, hes, h⟩ := bind_ok h
    obtain ⟨c, -, h⟩ := bind_ok h
    cases h
    have h4 := need_ok hes
    intro e he
    refine ⟨numOk_bigOk (hmw.1.2.2.2.2 es h4 e he), ?_⟩
    exact hmw.2.2 _ (by unfold Msg.entryLists; rw [h4]; simp) e he

theorem es_entries (hW : x.Within b E) {es : List Entry} (h : x.es = .ok es) :
    ∀ e ∈ es, bigOk e.term ∧ e.chgSize ≤ E := by
  unfold OnDisk.es at h
  obtain ⟨c, -, h⟩ := bind_ok h
  split at h
  · obtain ⟨fm, hfm, h⟩ := bind_ok h
    obtain ⟨k, -, h⟩ := bind_ok h
    exact fun e he => fm_entries hW hfm e (subSeq_mem h he)
  · split at h
    · cases h; intro e he; cases he
    · have h4 := need_ok h
      intro e he
      have hn := hW.2.1.1.2.2.2.2.2.2.2.2.2.2.1 es h4 e he
      refine ⟨numOk_bigOk hn, ?_⟩
      exact hW.2.1.2.2 _ (by unfold Event.entryLists; rw [show x.w = x.q.ev from rfl] at h4; rw [h4]; simp) e he

theorem stores_eq {st : Bool} (h : x.stores = .ok st) : ∃ es, x.es = .ok es ∧ st = (es.length != 0) := by
  unfold OnDisk.stores at h
  obtain ⟨es, hes, h⟩ := bind_ok h
  cases h
  exact ⟨es, hes, rfl⟩

theorem L1_within (hW : x.Within b E) (hS : StoresFit x) {l : List Entry} (h : x.L1 = .ok l) :
    logWithin b E l := by
  unfold OnDisk.L1 at h
  obtain ⟨st, hst, h⟩ := bind_ok h
  cases st
  · simp at h; subst h; exact L0_within hW
  · simp only [ite_true] at h
    obtain ⟨fi, hfi, h⟩ := bind_ok h
    obtain ⟨sub, hsub, h⟩ := bind_ok h
    obtain ⟨es, hes, h⟩ := bind_ok h
    cases h
    obtain ⟨fi', es', p, hp, hfi', hes', hlen⟩ := hS hst
    rw [hfi] at hfi'; cases hfi'
    rw [hes] at hes'; cases hes'
    have hpb := (ll_within hW hp).2.1
    have hesb := OnDisk.es_le hW hes
    have hsubl : (sub.length : Int) ≤ max 0 (fi - 1) := by
      by_cases h1 : 1 ≤ fi - 1
      · have := subSeq_len_eq (Int.le_refl 1) h1 hsub
        omega
      · unfold subSeq at hsub
        rw [if_pos (by omega)] at hsub
        cases hsub; simp; omega
    refine ⟨?_, fun e he => ?_⟩
    · simp only [List.length_append]; omega
    · rcases List.mem_append.1 he with he | he
      · exact (L0_within hW).2 e (subSeq_mem hsub he)
      · exact es_entries hW hes e he

theorem f_leads_gen {f : AppendFact} (hl : x.leads = .ok true) (hf : x.f = .ok f) :
    ∃ es st, x.es = .ok es ∧ x.stores = .ok st ∧ f.entries = es ∧
      ((st = false ∧ f.prevLogIndex = 0) ∨ (st = true ∧ ∃ fi, x.first = .ok fi ∧ f.prevLogIndex = fi - 1)) := by
  unfold OnDisk.f at hf
  obtain ⟨ld, hld, hf⟩ := bind_ok hf
  rw [hl] at hld; cases hld
  dsimp only at hf
  simp only [ite_true] at hf
  obtain ⟨t1, -, hf⟩ := bind_ok hf
  obtain ⟨es, hes, hf⟩ := bind_ok hf
  obtain ⟨st, hst, hf⟩ := bind_ok hf
  refine ⟨es, st, hes, hst, ?_⟩
  cases st
  · simp only [Bool.false_eq_true, ite_false] at hf
    suffices H : f.entries = es ∧ f.prevLogIndex = 0 from ⟨H.1, .inl ⟨rfl, H.2⟩⟩
    obtain ⟨a, -, hf⟩ := bind_ok hf
    split at hf
    · obtain ⟨l, -, hf⟩ := bind_ok hf
      obtain ⟨fi2, -, hf⟩ := bind_ok hf
      obtain ⟨m, -, hf⟩ := bind_ok hf
      split at hf
      · obtain ⟨c, -, hf⟩ := bind_ok hf
        cases hf; exact ⟨rfl, rfl⟩
      · cases hf; exact ⟨rfl, rfl⟩
    · obtain ⟨m, -, hf⟩ := bind_ok hf
      split at hf
      · obtain ⟨c, -, hf⟩ := bind_ok hf
        cases hf; exact ⟨rfl, rfl⟩
      · cases hf; exact ⟨rfl, rfl⟩
  · simp only [ite_true] at hf
    obtain ⟨fi, hfi, hf⟩ := bind_ok hf
    suffices H : f.entries = es ∧ f.prevLogIndex = fi - 1 from ⟨H.1, .inr ⟨rfl, fi, hfi, H.2⟩⟩
    obtain ⟨a, -, hf⟩ := bind_ok hf
    split at hf
    · obtain ⟨l, -, hf⟩ := bind_ok hf
      obtain ⟨fi2, -, hf⟩ := bind_ok hf
      obtain ⟨m, -, hf⟩ := bind_ok hf
      split at hf
      · obtain ⟨c, -, hf⟩ := bind_ok hf
        cases hf; exact ⟨rfl, rfl⟩
      · cases hf; exact ⟨rfl, rfl⟩
    · obtain ⟨m, -, hf⟩ := bind_ok hf
      split at hf
      · obtain ⟨c, -, hf⟩ := bind_ok hf
        cases hf; exact ⟨rfl, rfl⟩
      · cases hf; exact ⟨rfl, rfl⟩

theorem f_notLeads (hl : x.leads = .ok false) : x.f = x.fm := by
  unfold OnDisk.f; rw [hl]; rfl

theorem last_bigOk (hW : x.Within b E) (hb : ((b + 1 : Nat) : Int) < numBound) (hS : StoresFit x)
    {f : AppendFact} (hf : x.f = .ok f) : bigOk (f.prevLogIndex + f.entries.length) := by
  unfold numBound at hb
  cases hl : x.leads with
  | error e => unfold OnDisk.f at hf; rw [hl] at hf; cases hf
  | ok ld =>
    cases ld
    · rw [f_notLeads hl] at hf
      have := OnDisk.fm_within hW hf
      unfold numOk numBound at this; unfold bigOk; omega
    · obtain ⟨es, st, hes, hst, hfe, hcase⟩ := f_leads_gen hl hf
      rcases hcase with ⟨rfl, hp⟩ | ⟨rfl, fi, hfi, hp⟩
      · have := OnDisk.es_le hW hes
        rw [hp, hfe]; unfold bigOk; omega
      · obtain ⟨fi', es', p, hpm, hfi', hes', hlen⟩ := hS hst
        rw [hfi] at hfi'; cases hfi'
        rw [hes] at hes'; cases hes'
        have := (ll_within hW hpm).2.1
        have := OnDisk.first_bounds hb hW hfi
        rw [hp, hfe]; unfold bigOk; omega

theorem getElem!_bigOk {l : List Int} {n : Nat} (h : ∀ y ∈ l, bigOk y) : bigOk l[n]! :=
  getElem!_mem' h bigOk_zero

theorem ackAt_bigOk (hW : x.Within b E) (hb : ((b + 1 : Nat) : Int) < numBound) (hS : StoresFit x)
    {a : Int} (h : x.ackAt = .ok a) : bigOk a := by
  unfold OnDisk.ackAt at h
  obtain ⟨bl, -, h⟩ := bind_ok h
  cases bl
  · simp only [Bool.false_eq_true, ite_false] at h
    unfold OnDisk.last at h
    obtain ⟨f, hf, h⟩ := bind_ok h
    cases h
    exact last_bigOk hW hb hS hf
  · simp only [ite_true] at h
    cases h
    exact getElem!_bigOk hW.1.2.2.2.2.2.1

theorem last_ok_bigOk (hW : x.Within b E) (hb : ((b + 1 : Nat) : Int) < numBound) (hS : StoresFit x)
    {a : Int} (h : x.last = .ok a) : bigOk a := by
  unfold OnDisk.last at h
  obtain ⟨f, hf, h⟩ := bind_ok h
  cases h
  exact last_bigOk hW hb hS hf

theorem imax_bigOk {a c : Int} (ha : bigOk a) (hc : bigOk c) : bigOk (imax a c) := by
  unfold imax; split <;> assumption

theorem conf1_bigOk (hW : x.Within b E) (hb : ((b + 1 : Nat) : Int) < numBound) (hS : StoresFit x)
    {c : Confirmed} (h : x.conf1 = .ok c) : bigOk c.term ∧ bigOk c.index := by
  unfold OnDisk.conf1 at h
  obtain ⟨st, -, h⟩ := bind_ok h
  cases st
  · simp only [Bool.false_eq_true, ite_false] at h
    obtain ⟨a, -, h⟩ := bind_ok h
    cases a
    · simp only [Bool.false_eq_true, ite_false] at h
      cases h
      exact getElem!_mem' hW.1.2.2.2.2.2.2.2.2.1 ⟨bigOk_zero, bigOk_zero⟩
    · simp only [ite_true] at h
      obtain ⟨t1, ht1, h⟩ := bind_ok h
      have hc0 := getElem!_mem' (n := x.n) hW.1.2.2.2.2.2.2.2.2.1 ⟨bigOk_zero, bigOk_zero⟩
      split at h
      · obtain ⟨t1', ht1', h⟩ := bind_ok h
        obtain ⟨l, hl, h⟩ := bind_ok h
        cases h
        exact ⟨T1_bigOk hW ht1', imax_bigOk hc0.2 (last_ok_bigOk hW hb hS hl)⟩
      · obtain ⟨t1', ht1', h⟩ := bind_ok h
        obtain ⟨l, hl, h⟩ := bind_ok h
        cases h
        exact ⟨T1_bigOk hW ht1', last_ok_bigOk hW hb hS hl⟩
  · simp only [ite_true] at h
    obtain ⟨t1, ht1, h⟩ := bind_ok h
    obtain ⟨l, hl, h⟩ := bind_ok h
    cases h
    exact ⟨T1_bigOk hW ht1, last_ok_bigOk hW hb hS hl⟩

theorem newC_within (hW : x.Within b E) (hS : StoresFit x) {l : List Entry} (h : x.newC = .ok l) :
    logWithin b E l := by
  unfold OnDisk.newC at h
  obtain ⟨l1, hl1, h⟩ := bind_ok h
  obtain ⟨c, -, h⟩ := bind_ok h
  have := L1_within hW hS hl1
  exact ⟨Nat.le_trans (subSeq_length_le h) this.1, fun e he => this.2 e (subSeq_mem h he)⟩

theorem ch1_within (hW : x.Within b E) (hS : StoresFit x) {l : List Entry} (h : x.ch1 = .ok l) :
    logWithin b E l := by
  unfold OnDisk.ch1 at h
  obtain ⟨a, -, h⟩ := bind_ok h
  cases a
  · simp at h; subst h; exact hW.2.2.2.2.2.2.2.2.1
  · simp only [ite_true] at h; exact newC_within hW hS h

theorem old_bigOk (hW : x.Within b E) {o : Int} (h : x.old = .ok o) : bigOk o := by
  unfold OnDisk.old at h
  obtain ⟨t, -, h⟩ := bind_ok h
  split at h
  · obtain ⟨p, hp, -, hp2⟩ := TermFn.get_mem h
    rw [← hp2]; exact (hW.2.2.2.2.2.2.2.2.2.1.2 p hp).2
  · cases h; exact bigOk_zero

theorem first_bigOk (hW : x.Within b E) (hb : ((b + 1 : Nat) : Int) < numBound) {fi : Int}
    (h : x.first = .ok fi) : bigOk fi ∧ bigOk (fi - 1) := by
  have := OnDisk.first_bounds hb hW h
  unfold bigOk; omega

theorem termAt_bigOk {l : List Entry} {k : Int} (h : ∀ e ∈ l, bigOk e.term) : bigOk (termAt l k) := by
  unfold termAt
  split
  · rename_i hk
    have hi : (k - 1).toNat < l.length := by omega
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact h _ (List.getElem_mem hi)
  · exact bigOk_zero

theorem voteRequest_nums (hW : x.Within b E) (hb : ((b + 1 : Nat) : Int) < numBound) {t : Int} (ht : bigOk t) :
    (x.s.voteRequest x.n t).NumsOk := by
  unfold numBound at hb
  have hl := L0_within hW
  unfold OnDisk.L0 at hl
  unfold State.voteRequest Fact.NumsOk State.lastTerm
  refine ⟨ht, ?_, termAt_bigOk (fun e he => (hl.2 e he).1), bigOk_zero⟩
  have := hl.1
  show bigOk ((x.s.log[x.n]!).length : Int)
  unfold bigOk; omega

theorem ackFact_nums {src dst : Str} {t a : Int} (ht : bigOk t) (ha : bigOk a) : (ackFact src dst t a).NumsOk :=
  ⟨ht, bigOk_zero, bigOk_zero, ha⟩

end values

/-! ## Sets as lists -/

theorem lset_add_len {α : Type} [DecidableEq α] (l : List α) (a : α) : (lset.add l a).length ≤ l.length + 1 := by
  unfold lset.add; split <;> simp

theorem lset_add_mem {α : Type} [DecidableEq α] {l : List α} {a y : α} (h : y ∈ lset.add l a) : y ∈ l ∨ y = a := by
  unfold lset.add at h; split at h
  · exact .inl h
  · simpa using h

theorem lset_union_len {α : Type} [DecidableEq α] (s t : List α) : (lset.union s t).length ≤ s.length + t.length := by
  unfold lset.union
  induction t generalizing s with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.length_cons]
    have := ih (lset.add s a); have := lset_add_len s a; omega

theorem lset_union_mem {α : Type} [DecidableEq α] {s t : List α} {y : α} (h : y ∈ lset.union s t) : y ∈ s ∨ y ∈ t := by
  unfold lset.union at h
  induction t generalizing s with
  | nil => exact .inl h
  | cons a t ih =>
    simp only [List.foldl_cons] at h
    rcases ih h with h' | h'
    · rcases lset_add_mem h' with h'' | h''
      · exact .inl h''
      · exact .inr (h'' ▸ List.mem_cons_self)
    · exact .inr (List.mem_cons_of_mem _ h')

theorem lset_minus_len {α : Type} [DecidableEq α] (s t : List α) : (lset.minus s t).length ≤ s.length := by
  unfold lset.minus; exact List.length_filter_le _ _

theorem lset_minus_mem {α : Type} [DecidableEq α] {s t : List α} {y : α} (h : y ∈ lset.minus s t) : y ∈ s := by
  unfold lset.minus at h; exact (List.mem_filter.1 h).1

theorem lset_minus_self {α : Type} [DecidableEq α] (s : List α) : lset.minus s s = [] := by
  unfold lset.minus; simp

theorem lset_minus_add {α : Type} [DecidableEq α] (l t : List α) (a : α) :
    (lset.minus (lset.add l a) t).length ≤ (lset.minus l t).length + 1 := by
  unfold lset.add; split
  · omega
  · unfold lset.minus; rw [List.filter_append]; simp only [List.length_append]
    have := List.length_filter_le (fun x => !t.contains x) [a]; simp at this ⊢; omega



/-! ## What the successor keeps -/

/-- The sections of `onDisk`, through to the successor's last section (`u9`). -/
theorem chain_some {s' : State} (h : g1 x (g2 x (g3 x (g4 x (g5 x (g6 x (succ x)))))) = .ok (some s')) :
    succ x = .ok (some s') ∧ StoresFit x := by
  obtain ⟨h5, hS⟩ := g5_some (g4_some (g3_some (g2_some (g1_some h))))
  exact ⟨g6_some h5, hS⟩

theorem keeps_of {s' : State} (h : g1 x (g2 x (g3 x (g4 x (g5 x (g6 x (succ x)))))) = .ok (some s')) :
    s'.cfg = x.s.cfg ∧ s'.queue = x.s.queue ∧ s'.pending = x.s.pending ∧ s'.i = x.s.i := by
  have h := (chain_some h).1
  unfold succ at h
  obtain ⟨t1, voted, vf, -, -, h⟩ := u0_ok h
  obtain ⟨L1, c, c1, el, -, -, -, -, h⟩ := u1_ok h
  obtain ⟨msgs', h, -⟩ := u2_ok h
  obtain ⟨votes', h, -⟩ := u3_ok h
  obtain ⟨pre1, h, -⟩ := u4_ok h
  obtain ⟨pre2, h, -⟩ := u5_ok h
  obtain ⟨pre3, h, -⟩ := u6_ok h
  obtain ⟨p, h, -⟩ := u7_ok h
  obtain ⟨ch1, tl', -, h, -⟩ := u8_ok h
  have hs' := u9_some h
  rw [hs']
  exact ⟨rfl, rfl, rfl, rfl⟩

end OnDiskLaws2

/-- **`OnDisk` keeps the configuration, the queues, the pending messages and `i`.** -/
theorem State.onDisk_keeps : ∀ (s : State) (n : Nat) (q : QItem) (more : Bool) (ro : List Str)
    (ld : List LeaderRec) (ll : TermFn (List Entry)) (ch : List Entry) (tl : TermFn Int) (vi : SSet)
    (ns : State), s.onDisk n q more ro ld ll ch tl vi = .ok (some ns) →
      ns.cfg = s.cfg ∧ ns.queue = s.queue ∧ ns.pending = s.pending ∧ ns.i = s.i := by
  intro s n q more ro ld ll ch tl vi ns h
  rw [OnDiskLaws2.onDisk_eq] at h
  exact OnDiskLaws2.keeps_of h

namespace OnDiskLaws2
end OnDiskLaws2
end AntCheck
end EtcdGrove
end Perennial
