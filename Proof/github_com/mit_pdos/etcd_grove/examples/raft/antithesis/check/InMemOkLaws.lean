/-
Lean-first (no Rocq counterpart). #33 S3b W3a (2026-11-23): pure laws for the proof of `x.ok()`
(B 231-253, `InMem.ok`): `ok` cut into its stages as the Go's blocks run (`InMem.ok_eq`, by
definition), and the premises of the operators it calls: `Granted`'s and `Acked`'s sets no larger
than the server set, the configurations it passes to `IsQuorum`/`Legal` within `2^61`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.InMemLaws

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

set_option linter.unusedSimpArgs false

namespace InMem
variable (x : InMem)

/-! ## `ok`'s stages (each the rest of `ok` from one of the Go's blocks on) -/

def okTail : EvalM Bool := do
  if (← andM x.leads (do pure (decide ((← x.c) > 0)))) then
    if (← x.cmt) then return isQuorum (x.s.acked x.n (← x.T) (← x.c)) (← (← x.lc1).get (← x.T))
    return (← recordedIn x.s.chain x.s.termLen (← x.L) (← x.c) (← x.T))
  return true
def okBad (es : List Entry) (q : Nat) : EvalM Bool := do
  let e := es[q]!
  if !isConf e then return false
  if !(← x.s.allSwitched x.n (← (← x.ll1).get (← x.T))) then return true
  if (List.range q).any (fun r => isConf (es[r]!)) then return true
  return !(← legal (x.s.config[x.n]!) e.value)
def okEs : EvalM Bool := do
  let es ← x.es
  if (← anyM es (fun e => do pure (e.term != (← x.T)))) then return false
  let bad ← anyM (List.range es.length) (x.okBad es)
  if bad then return false
  x.okTail
def okApp : EvalM Bool := do
  if (← x.app) then
    if x.ev.first.isSome then
      let f ← need x.ev.first
      if f != ((← (← x.ll1).get (← x.T)).length : Int) + 1 then return false
    x.okEs
  else x.okTail
def okLeads : EvalM Bool := do
  if (← x.leads) then
    if !(← andM (do pure (x.s.currentTerm[x.n]! == (← x.T))) <|
          andM (do pure ((← x.ll1).has (← x.T))) (do let c ← x.c; pure (decide (c ≤ (← x.L).length)))) then
      return false
  x.okApp
def okWins : EvalM Bool := do
  if (← x.wins) then
    if !(← andM (pure (x.s.role[x.n]! == candidate)) (do pure (x.s.currentTerm[x.n]! == (← x.T)))) then
      return false
    if x.s.ledLog.has (← x.T) then return false
    if !isQuorum (x.s.granted x.n) (x.s.config[x.n]!) then return false
    if !(← x.s.oneWaiting x.n (x.s.log[x.n]!)) then return false
    if !(← orM (pure (x.s.confAt[x.n]! == 0))
          (do recordedIn x.s.chain x.s.termLen (x.s.log[x.n]!) (x.s.confAt[x.n]!) ((← x.T) - 1))) then
      return false
  x.okLeads
def okSnap : EvalM Bool := do
  if x.snapsM then
    if !(← andM (do pure ((← need x.ev.role) != leader)) <| andM (pure (x.s.role[x.n]! != leader))
          (do pure (decide ((← need x.ev.snap).index ≤ x.s.chain.length)))) then return false
  x.okWins
def okRoleOk (r : Str) : Bool := or (or (or (r == follower) (r == candidate)) (r == leader)) (r == go!"precandidate")
def validByOk (bv : Str) : Bool := (or (or (or (or (or (or (or (or (or (bv == go!"recv") (bv == go!"tick")) (bv == go!"campaign")) (bv == go!"propose")) (bv == go!"write")) (bv == go!"apply")) (bv == go!"boot")) (bv == go!"transfer")) (bv == go!"snapstatus")) (bv == go!"read"))
/-- `ok`, by its stages. -/
theorem ok_eq : x.ok = (do
    let bv ← need x.ev.byE
    if !(validByOk bv) then return false
    let r ← need x.ev.role
    if !(okRoleOk r) then return false
    x.okSnap) := by
  rfl

/-- `validBy`'s answer (Go) is `ok`'s test. -/
theorem validBy_contains (bv : Str) :
    ([go!"recv", go!"tick", go!"campaign", go!"propose", go!"write", go!"apply", go!"boot", go!"transfer", go!"snapstatus", go!"read"] : List Str).contains bv = validByOk bv := by
  unfold validByOk
  simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_assoc]

end InMem

/-! ## The operators' premises -/

/-- A fold that at each `j` keeps the set or adds `j`, and keeps it where `q j` fails, adds at
most the elements satisfying `q`. -/
theorem foldl_condAdd_length_le (q : Str → Bool) (f : SSet → Str → SSet)
    (hf : ∀ out j, (q j = false → f out j = out) ∧ (f out j = out ∨ f out j = setAdd out j)) (t s : List Str) :
    (t.foldl f s).length ≤ s.length + (t.filter q).length := by
  induction t generalizing s with
  | nil => simp
  | cons y t ih =>
    simp only [List.foldl_cons, List.filter_cons]
    cases hq : q y
    · rw [(hf s y).1 hq]; simpa using ih s
    · have := ih (f s y)
      have : (f s y).length ≤ s.length + 1 := by
        rcases (hf s y).2 with h | h <;> rw [h]
        · omega
        · exact setAdd_length_le s y
      simp; omega

/-- `Granted(i)`: no larger than the server set (the fold skips `i` itself, added at most once). -/
theorem State.granted_length_le (s : State) {i : Nat} (hi : i < s.cfg.server.length) :
    (s.granted i).length ≤ s.cfg.server.length := by
  have hlt : (s.cfg.server.filter (fun j => j != s.cfg.server[i]!)).length < s.cfg.server.length :=
    List.length_filter_lt_length_iff_exists.mpr ⟨_, getElem!_mem hi, by simp⟩
  unfold State.granted
  simp only
  split
  · refine Nat.le_trans (setAdd_length_le _ _) (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt
      (foldl_condAdd_length_le (fun j => j != s.cfg.server[i]!) _ ?_ _ []) (by simpa using hlt)))
    intro out j
    refine ⟨fun h => ?_, ?_⟩
    · simp only [h, Bool.false_and, Bool.false_eq_true, ite_false]
    · split <;> simp
  · refine Nat.le_trans (foldl_condAdd_length_le (fun j => j != s.cfg.server[i]!) _ ?_ _ []) (by simp only [List.length_nil, Nat.zero_add]; exact Nat.le_of_lt hlt)
    intro out j
    refine ⟨fun h => ?_, ?_⟩
    · simp only [h, Bool.false_and, Bool.false_eq_true, ite_false]
    · split <;> simp

/-- `Acked(i, t, c)`: no larger than the server set. -/
theorem State.acked_length_le (s : State) (i : Nat) (t c : Int) :
    (s.acked i t c).length ≤ s.cfg.server.length := by
  unfold State.acked
  simp only
  refine Nat.le_trans (foldl_condAdd_length_le (fun _ => true) _ ?_ _ []) (by simp only [List.length_nil, Nat.zero_add]; exact List.length_filter_le _ _)
  intro out j
  refine ⟨fun h => by simp at h, ?_⟩
  split <;> simp

/-- A configuration within budget is within `IsQuorum`'s bound. -/
theorem confWithin_lt {V b E w : Nat} {c : Conf} (hc : confWithin V b E c)
    (hE : ((V + (b + w + 1) * E : Nat) : Int) < 2 ^ 61) :
    (c.cin.length : Int) < 2 ^ 61 ∧ (c.cout.length : Int) < 2 ^ 61 := by
  unfold confWithin at hc
  have h1 : b * E ≤ (b + w + 1) * E := Nat.mul_le_mul_right _ (by omega)
  constructor <;> omega

namespace InMem
variable {x : InMem} {b E : Nat}

/-- `lc1`: the leader configurations, with the winner's at `T`, within budget. -/
theorem lc1_within (hW : x.s.Within b E) {l : TermFn Conf} (h : x.lc1 = .ok l) :
    ∀ q ∈ l, confWithin x.s.cfg.initVoters.length b E q.2 := by
  unfold InMem.lc1 at h
  obtain ⟨w, -, h⟩ := bind_ok h
  cases w
  · simp only [Bool.false_eq_true, ite_false, pure_ok, Except.ok.injEq] at h
    subst h
    exact fun q hq => (hW.ledConf q hq).2
  · simp only [ite_true] at h
    obtain ⟨t, -, h⟩ := bind_ok h
    simp only [pure_ok, Except.ok.injEq] at h
    subst h
    intro q hq
    rcases TermFn.mem_with hq with h' | h'
    · subst h'
      exact getElem!_mem' hW.config ⟨Nat.zero_le _, Nat.zero_le _⟩
    · exact (hW.ledConf q h').2

theorem lc1_get_within (hW : x.s.Within b E) {l : TermFn Conf} (h : x.lc1 = .ok l)
    {t : Int} {c : Conf} (hg : l.get t = .ok c) : confWithin x.s.cfg.initVoters.length b E c :=
  lc1_within hW h _ (TermFn.mem_of_get hg)

end InMem

end AntCheck
end EtcdGrove
end Perennial
