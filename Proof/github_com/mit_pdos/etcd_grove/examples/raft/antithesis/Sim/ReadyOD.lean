/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: `OnDisk` of a `ready` report, per kind (#33 S4)

`OnDisk` (B 290-436) of a `ready` report (`evReady`, its `entries` present, `more` false) evaluated
for each kind of `Ready` raft makes (`notes/antithesis-rawnode-design.md` §3.3). Unfolding
`State.onDisk` and simplifying flat inlines its do-block's join points before their branches are
decided (exponential, past `simp`'s step limit). Instead: `onDiskB` is the same body with the
`OnDisk` record `x` an argument (`onDisk_eq`, by `rfl`); a kind's proof (`od_run`) generalizes `x`,
rewrites its LET definitions with the small lemmas `od_*`/`ox_*` with `zeta := false` (every guard
decided, the joins kept), then inlines the joins. Each kind's successor is `odS`; `ready_of` puts
`InMemory` and `OnDisk` together. Done: a campaign (`onDisk_camp`), a vote granted at the node's
term or with the request's term adopted (`onDisk_grant`), a role change only (`onDisk_same`), a
term adopted only (`onDisk_adopt`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.ReadyEval

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Perennial
namespace EtcdGrove
namespace AntCheck
end AntCheck

namespace AntCheck

/-- `State.onDisk`'s body (B 290-436) with its `OnDisk` record `x`, its report `w` and the node's
name `me` as arguments (`onDisk_eq`), so that a kind's proof can name `x`'s pieces. -/
def onDiskB (s : State) (n : Nat) (more : Bool) (ro : List Str) (ld : List LeaderRec)
    (ll : TermFn (List Entry)) (ch : List Entry) (tl : TermFn Int) (vi : SSet) (x : OnDisk) (w : Event)
    (me : Str) : EvalM (Option State) := do
  if more && (s.undo[n]!).isNone then return none
  if (← andM x.isApp (notM (do sendableIn ld ll ch tl (← x.fm)))) then return none
  -- The term.
  if !decide ((← x.T1) ≥ x.T0) then return none
  if (← x.T1) != x.T0 && ro[n]! == leader then return none
  if (← andM x.elect (notM (andM (do pure ((← x.T1) == x.T0 + 1)) (fieldEq w.vote me)))) then
    return none
  if (← x.adopt) then
    if !(← andM (pure x.hasM) (do pure ((← (← x.m).term_) == (← x.T1)))) then return none
    let t1 ← x.T1
    if !(List.range s.cfg.server.length).any (fun j => j != n && decide (s.currentTerm[j]! ≥ t1)) then
      return none
  -- The vote.
  if (← x.voted) then
    if (← x.V1) != [] then return none
    if !(← x.elect) then
      let ok ← andM (pure x.hasM) <| andM (do pure ((← (← x.m).typ) == go!"vote")) <|
        andM (do pure ((← (← x.m).from_) == (← need w.vote))) <|
        andM (do pure ((← (← x.m).term_) == (← x.T1))) <|
        andM (do pure (s.msgs.contains (← voteFact (← x.m))))
          (do pure (s.upToDate (← voteFact (← x.m)) n))
      if !ok then return none
  -- The entries.
  if x.snaps then
    let ok ← andM (notM x.leads) <| andM (pure x.hasM) <|
      andM (do pure ((← (← x.m).typ) == go!"snap")) <| andM x.stores <|
      andM (do pure ((← need w.snap).index == (← (← x.m).index_))) <|
      andM (do pure ((← need w.snap).term == (← (← x.m).logTerm_)))
        (do pure ((← need w.commit) == (← (← x.m).index_)))
    if !ok then return none
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
  -- The commit index.
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
  -- The successor.
  let t1 ← x.T1
  let voted ← x.voted
  let mut ns := { s with currentTerm := s.currentTerm.set n t1 }
  if voted then
    ns := { ns with voteTerm := s.voteTerm.set n t1, voteFor := s.voteFor.set n (← need w.vote) }
  ns := { ns with log := s.log.set n (← x.L1), commitIndex := s.commitIndex.set n (← need w.commit),
                  role := ro, confirmed := s.confirmed.set n (← x.conf1) }
  let mut msgs := s.msgs
  if (← x.elect) then msgs := lset.add msgs (s.voteRequest n t1)
  if (← x.acks) then msgs := lset.add msgs (ackFact me (← x.f).src t1 (← x.ackAt))
  ns := { ns with msgs }
  let mut votes := s.votes
  if voted then votes := lset.add votes { voter := me, term := t1, cand := ← need w.vote }
  ns := { ns with votes, leaders := ld, ledLog := ll }
  -- pre (B 349-359), with msgs' and votes' as just given.
  let vt := s.voteTerm[n]!
  let vf := s.voteFor[n]!
  let cm := s.commitIndex[n]!
  let cf := s.confirmed[n]!
  let mut pre : Pre := { term := x.T0, voteTerm := vt, voteFor := vf, commit := cm, confirmed := cf,
                         msgs := lset.minus ns.msgs s.msgs, votes := lset.minus ns.votes s.votes }
  if (← x.stores) then
    pre := { pre with keep := (← x.first) - 1,
                      suffix := ← subSeq x.L0 (← x.first) x.L0.length }
  else
    pre := { pre with keep := x.L0.length }
  if (← x.acks) then pre := { pre with acks := [ackFact me (← x.f).src t1 (← x.ackAt)] }
  if (← x.stores) then pre := { pre with low := ← x.first }
  if !more then
    ns := { ns with undo := s.undo.set n (some pre) }
  else
    let u := (s.undo[n]!).getD {}
    let suffix ← if pre.keep ≥ u.keep then pure u.suffix
      else do pure ((← subSeq x.L0 (pre.keep + 1) u.keep) ++ u.suffix)
    let nu := { u with keep := imin u.keep pre.keep, suffix, msgs := lset.union u.msgs pre.msgs,
                       votes := lset.union u.votes pre.votes, acks := lset.union u.acks pre.acks,
                       low := lowest u.low pre.low }
    ns := { ns with undo := s.undo.set n (some nu) }
  -- Safety (B 422-436).
  ns := { ns with chain := ← x.ch1 }
  if (← x.adv) then
    ns := { ns with termLen := tl.with t1 (imax (← x.old) (← x.newC).length) }
  else
    ns := { ns with termLen := tl }
  let mut viol := vi
  if (← andM x.adv (notM (do comparable ch (← x.newC)))) then viol := setAdd viol go!"CommitSafety"
  if (← x.adv) then
    if (← anyM ll (fun p => andM (pure (decide (p.1 > t1))) (notM (do isPrefix (← x.newC) p.2)))) then
      viol := setAdd viol go!"LeaderCompleteness"
  let l1 ← x.L1
  let l0 := x.L0
  let changed := !(← entriesEqual l1 l0)
  if changed then
    if (← anyM (List.range s.cfg.server.length)
          (fun b => andM (pure (b != n)) (notM (matching l1 (s.log[b]!))))) then
      viol := setAdd viol go!"LogMatching"
  if (← andM (orM (pure changed) x.adv)
        (notM (do isPrefix (← subSeq (← x.ch1) 1 (← need w.commit)) l1))) then
    viol := setAdd viol go!"CommittedEntriesPreserved"
  let c1 ← x.conf1
  if (← andM x.adv (do pure ((c1.term != t1) || decide ((← need w.commit) > c1.index)))) then
    viol := setAdd viol go!"CommitBeyondConfirmed"
  return some { ns with viol }

theorem onDisk_eq (s : State) (n : Nat) (q : QItem) (more : Bool) (ro : List Str) (ld : List LeaderRec)
    (ll : TermFn (List Entry)) (ch : List Entry) (tl : TermFn Int) (vi : SSet) :
    s.onDisk n q more ro ld ll ch tl vi =
      onDiskB s n more ro ld ll ch tl vi ⟨s, n, q, more, ro, ld, ll, ch, tl, vi⟩ q.ev (s.cfg.server[n]!) := rfl

end AntCheck

namespace AntSim

open AntCheck

section pieces
variable [GooseExts]

/-- `OnDisk`'s arguments for a `ready` report. -/
abbrev odX (S : State) (n : Nat) (id : w64) (b : Str) (r : Role) (t v c : w64) (es : List EntryM)
    (M : List AntCheck.Msg) (ro : List Str) (ld : List LeaderRec) (ll : TermFn (List Entry)) (ch : List Entry)
    (tl : TermFn Int) (vi : SSet) : OnDisk :=
  { s := S, n := n, q := { ev := evReady id b r t v c es, m := M }, more := false, ro := ro, ld := ld,
    ll := ll, ch := ch, tl := tl, vi := vi }

variable (S : State) (n : Nat) (id : w64) (b : Str) (r : Role) (t v c : w64) (es : List EntryM)
  (M : List AntCheck.Msg) (ro : List Str) (ld : List LeaderRec) (ll : TermFn (List Entry)) (ch : List Entry)
  (tl : TermFn Int) (vi : SSet)

theorem ev_vote : (evReady id b r t v c es).vote = some (nameOf v) := rfl
theorem ev_commit : (evReady id b r t v c es).commit = some (uint.Z c) := rfl
theorem ev_term : (evReady id b r t v c es).term = some (uint.Z t) := rfl
theorem ev_role : (evReady id b r t v c es).role = some (roleOf r) := rfl
theorem ev_snap : (evReady id b r t v c es).snap = none := rfl
theorem ev_entries : (evReady id b r t v c es).entries = some (logOf es) := rfl
theorem cand_leader : (candidate == leader) = false := by decide
theorem fol_leader : (follower == leader) = false := by decide
theorem fol_cand : (follower == candidate) = false := by decide
theorem leader_cand : (leader == candidate) = false := by decide
theorem od_andM_ok (a b : Bool) : AntCheck.andM (.ok a) (.ok b) = .ok (a && b) := by cases a <;> rfl
theorem notM_ok (b : Bool) : AntCheck.notM (.ok b) = .ok !b := rfl
theorem beq_self_str (a : Str) : (a == a) = true := beq_self_eq_true a
theorem roleOf_beq_leader (r : Role) : (roleOf r == leader) = decide (r = .leader) := by cases r <;> decide
theorem roleOf_beq_cand (r : Role) : (roleOf r == candidate) = decide (r = .candidate) := by cases r <;> decide

theorem od_T1 : (odX S n id b r t v c es M ro ld ll ch tl vi).T1 = .ok (uint.Z t) := rfl
theorem od_T0 : (odX S n id b r t v c es M ro ld ll ch tl vi).T0 = S.currentTerm[n]! := rfl
theorem od_L0 : (odX S n id b r t v c es M ro ld ll ch tl vi).L0 = S.log[n]! := rfl
theorem od_bat : (odX S n id b r t v c es M ro ld ll ch tl vi).bat = false := rfl
theorem od_snaps : (odX S n id b r t v c es M ro ld ll ch tl vi).snaps = false := rfl
theorem od_hasM : (odX S n id b r t v c es M ro ld ll ch tl vi).hasM = (M != []) := rfl
theorem od_m : (odX S n id b r t v c es M ro ld ll ch tl vi).m = msgSeqHead M := rfl
theorem od_isApp : (odX S n id b r t v c es M ro ld ll ch tl vi).isApp = .ok false := rfl
theorem od_below : (odX S n id b r t v c es M ro ld ll ch tl vi).below = .ok false := rfl
theorem od_takes : (odX S n id b r t v c es M ro ld ll ch tl vi).takes = .ok false := rfl
theorem od_es : (odX S n id b r t v c es M ro ld ll ch tl vi).es = .ok (logOf es) := rfl
theorem od_first : (odX S n id b r t v c es M ro ld ll ch tl vi).first = .ok (firstOf es) := rfl
theorem od_stores :
    (odX S n id b r t v c es M ro ld ll ch tl vi).stores = .ok ((logOf es).length != 0) := rfl
theorem od_leads :
    (odX S n id b r t v c es M ro ld ll ch tl vi).leads = .ok (roleOf r == leader) := rfl
theorem od_moved :
    (odX S n id b r t v c es M ro ld ll ch tl vi).moved = .ok (uint.Z c != S.commitIndex[n]!) := rfl
theorem od_adv :
    (odX S n id b r t v c es M ro ld ll ch tl vi).adv = .ok (decide (uint.Z c > S.commitIndex[n]!)) := rfl
theorem od_elect : (odX S n id b r t v c es M ro ld ll ch tl vi).elect =
    .ok ((uint.Z t != S.currentTerm[n]!) && (roleOf r == candidate)) := by
  show AntCheck.andM (.ok _) (.ok _) = _; rw [od_andM_ok]; rfl
theorem od_adopt : (odX S n id b r t v c es M ro ld ll ch tl vi).adopt =
    .ok ((uint.Z t != S.currentTerm[n]!) && !(roleOf r == candidate)) := by
  show AntCheck.andM (.ok (uint.Z t != S.currentTerm[n]!))
    (AntCheck.notM (OnDisk.elect (odX S n id b r t v c es M ro ld ll ch tl vi))) = _
  rw [od_elect]; cases (uint.Z t != S.currentTerm[n]!) <;> cases (roleOf r == candidate) <;> rfl
theorem od_V1 : (odX S n id b r t v c es M ro ld ll ch tl vi).V1 =
    .ok (if uint.Z t != S.currentTerm[n]! then [] else S.vote n) := by
  show (if (uint.Z t != S.currentTerm[n]!) = true then pure [] else pure (S.vote n)) = _
  split <;> rfl
theorem od_voted : (odX S n id b r t v c es M ro ld ll ch tl vi).voted =
    .ok (nameOf v != (if uint.Z t != S.currentTerm[n]! then [] else S.vote n)) := by
  show (do let x ← need (some (nameOf v)); pure (x != (← OnDisk.V1 _))) = _
  rw [od_V1]; rfl
theorem od_old : (odX S n id b r t v c es M ro ld ll ch tl vi).old =
    (if tl.has (uint.Z t) then tl.get (uint.Z t) else .ok 0) := rfl

theorem od_w : (odX S n id b r t v c es M ro ld ll ch tl vi).w = evReady id b r t v c es := rfl
theorem od_L1_nil : (odX S n id b r t v c [] M ro ld ll ch tl vi).L1 = .ok (S.log[n]!) := rfl
theorem od_acks_nil (hm : (uint.Z c != S.commitIndex[n]!) = false) : (odX S n id b r t v c [] M ro ld ll ch tl vi).acks = .ok false := by
  unfold OnDisk.acks; rw [od_stores, od_moved, hm, od_takes, od_below]; rfl
theorem od_conf1_nil (hm : (uint.Z c != S.commitIndex[n]!) = false) :
    (odX S n id b r t v c [] M ro ld ll ch tl vi).conf1 = .ok (S.confirmed[n]!) := by
  unfold OnDisk.conf1; rw [od_stores, od_acks_nil (hm := hm)]; rfl
theorem od_ch1_noadv (ha : decide (uint.Z c > S.commitIndex[n]!) = false) : (odX S n id b r t v c es M ro ld ll ch tl vi).ch1 = .ok ch := by
  unfold OnDisk.ch1; rw [od_adv, ha]; rfl

/-! The pieces at an `OnDisk` named by its arguments (`generalize`d in a kind's proof). -/

variable {S n id b r t v c es M ro ld ll ch tl vi}

theorem ox_T1 {x : OnDisk} (hx : odX S n id b r t v c es M ro ld ll ch tl vi = x) :
    x.T1 = .ok (uint.Z t) := by
  subst hx; exact od_T1 ..
theorem ox_T0 {x : OnDisk} (hx : odX S n id b r t v c es M ro ld ll ch tl vi = x) :
    x.T0 = S.currentTerm[n]! := by
  subst hx; exact od_T0 ..
theorem ox_L0 {x : OnDisk} (hx : odX S n id b r t v c es M ro ld ll ch tl vi = x) :
    x.L0 = S.log[n]! := by
  subst hx; exact od_L0 ..
theorem ox_bat {x : OnDisk} (hx : odX S n id b r t v c es M ro ld ll ch tl vi = x) :
    x.bat = false := by
  subst hx; exact od_bat ..
theorem ox_snaps {x : OnDisk} (hx : odX S n id b r t v c es M ro ld ll ch tl vi = x) :
    x.snaps = false := by
  subst hx; exact od_snaps ..
theorem ox_hasM {x : OnDisk} (hx : odX S n id b r t v c es M ro ld ll ch tl vi = x) :
    x.hasM = (M != []) := by
  subst hx; exact od_hasM ..
theorem ox_m {x : OnDisk} (hx : odX S n id b r t v c es M ro ld ll ch tl vi = x) :
    x.m = msgSeqHead M := by
  subst hx; exact od_m ..
theorem ox_isApp {x : OnDisk} (hx : odX S n id b r t v c es M ro ld ll ch tl vi = x) :
    x.isApp = .ok false := by
  subst hx; exact od_isApp ..
theorem ox_below {x : OnDisk} (hx : odX S n id b r t v c es M ro ld ll ch tl vi = x) :
    x.below = .ok false := by
  subst hx; exact od_below ..
theorem ox_takes {x : OnDisk} (hx : odX S n id b r t v c es M ro ld ll ch tl vi = x) :
    x.takes = .ok false := by
  subst hx; exact od_takes ..
theorem ox_es {x : OnDisk} (hx : odX S n id b r t v c es M ro ld ll ch tl vi = x) :
    x.es = .ok (logOf es) := by
  subst hx; exact od_es ..
theorem ox_first {x : OnDisk} (hx : odX S n id b r t v c es M ro ld ll ch tl vi = x) :
    x.first = .ok (firstOf es) := by
  subst hx; exact od_first ..
theorem ox_stores {x : OnDisk} (hx : odX S n id b r t v c es M ro ld ll ch tl vi = x) :
    x.stores = .ok ((logOf es).length != 0) := by
  subst hx; exact od_stores ..
theorem ox_leads {x : OnDisk} (hx : odX S n id b r t v c es M ro ld ll ch tl vi = x) :
    x.leads = .ok (roleOf r == leader) := by
  subst hx; exact od_leads ..
theorem ox_moved {x : OnDisk} (hx : odX S n id b r t v c es M ro ld ll ch tl vi = x) :
    x.moved = .ok (uint.Z c != S.commitIndex[n]!) := by
  subst hx; exact od_moved ..
theorem ox_adv {x : OnDisk} (hx : odX S n id b r t v c es M ro ld ll ch tl vi = x) :
    x.adv = .ok (decide (uint.Z c > S.commitIndex[n]!)) := by
  subst hx; exact od_adv ..
theorem ox_elect {x : OnDisk} (hx : odX S n id b r t v c es M ro ld ll ch tl vi = x) :
    x.elect = .ok ((uint.Z t != S.currentTerm[n]!) && (roleOf r == candidate)) := by
  subst hx; exact od_elect ..
theorem ox_adopt {x : OnDisk} (hx : odX S n id b r t v c es M ro ld ll ch tl vi = x) :
    x.adopt = .ok ((uint.Z t != S.currentTerm[n]!) && !(roleOf r == candidate)) := by
  subst hx; exact od_adopt ..
theorem ox_V1 {x : OnDisk} (hx : odX S n id b r t v c es M ro ld ll ch tl vi = x) :
    x.V1 = .ok (if uint.Z t != S.currentTerm[n]! then [] else S.vote n) := by
  subst hx; exact od_V1 ..
theorem ox_voted {x : OnDisk} (hx : odX S n id b r t v c es M ro ld ll ch tl vi = x) :
    x.voted = .ok (nameOf v != (if uint.Z t != S.currentTerm[n]! then [] else S.vote n)) := by
  subst hx; exact od_voted ..
theorem ox_old {x : OnDisk} (hx : odX S n id b r t v c es M ro ld ll ch tl vi = x) :
    x.old = (if tl.has (uint.Z t) then tl.get (uint.Z t) else .ok 0) := by
  subst hx; exact od_old ..
theorem ox_w {x : OnDisk} (hx : odX S n id b r t v c es M ro ld ll ch tl vi = x) :
    x.w = evReady id b r t v c es := by
  subst hx; exact od_w ..
theorem ox_L1_nil {x : OnDisk} (hx : odX S n id b r t v c [] M ro ld ll ch tl vi = x) :
    x.L1 = .ok (S.log[n]!) := by
  subst hx; exact od_L1_nil ..

theorem ox_acks_nil {x : OnDisk} (hx : odX S n id b r t v c [] M ro ld ll ch tl vi = x) (hm : (uint.Z c != S.commitIndex[n]!) = false) :
    x.acks = .ok false := by subst hx; exact od_acks_nil _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hm
theorem ox_conf1_nil {x : OnDisk} (hx : odX S n id b r t v c [] M ro ld ll ch tl vi = x) (hm : (uint.Z c != S.commitIndex[n]!) = false) :
    x.conf1 = .ok (S.confirmed[n]!) := by subst hx; exact od_conf1_nil _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hm
theorem ox_ch1_noadv {x : OnDisk} (hx : odX S n id b r t v c es M ro ld ll ch tl vi = x) (ha : decide (uint.Z c > S.commitIndex[n]!) = false) :
    x.ch1 = .ok ch := by subst hx; exact od_ch1_noadv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ha

/-- What `Ready` keeps of `InMemory`'s result over `OnDisk`'s successor (B 446-447). -/
def rdS (ns : State) (r : MemResult) : State :=
  { ns with ledConf := r.ledConf, ledAt := r.ledAt, elAt := r.elAt, config := r.config, confAt := r.confAt }

/-- `Ready` (B 439-447) from `InMemory` and `OnDisk`. -/
theorem ready_of {S : State} {n : Nat} {ev : Event} {r : MemResult} {q : QItem} {ns : State}
    (hq0 : S.queue[n]! = []) (hm : S.inMemory n ev = .ok r) (hok : r.ok = true)
    (hqd : S.queued n ev = .ok q)
    (hod : S.onDisk n q false r.role r.leaders r.ledLog r.chain r.termLen r.viol = .ok (some ns)) :
    S.ready n ev = .ok (some (rdS ns r)) := by
  unfold State.ready
  simp only [hq0, bne_self_eq_false, Bool.false_eq_true, ite_false, hm, hok, Bool.not_true, hqd, hod,
    eok_bind]
  rfl

theorem queued_ready (S : State) (n : Nat) (id : w64) (b : Str) (r : Role) (t v c : w64)
    (es : List EntryM) :
    S.queued n (evReady id b r t v c es) =
      .ok { ev := evReady id b r t v c es, m := (if b = go!"recv" then S.pending[n]! else ([] : List AntCheck.Msg)) } := by
  unfold State.queued
  by_cases hb : b = go!"recv"
  · subst hb; simp only [evReady, need, eok_bind, epure, str_beq, decide_true, ite_true]
  · simp only [evReady, need, eok_bind, epure, str_beq, hb, decide_false, Bool.false_eq_true, ite_false]

/-- `OnDisk`'s successor (B 534-560, more false): at node `n` the term `t1`, a vote written `vo`
(at `t1`), the log `L1`, the commit `c`, the confirmation `cf`; the roles `ro`, the facts `msgs`,
`votes`, the leaders and leader logs given, the announced write `p`, `chain`, `termLen`, `viol`. -/
def odS (S : State) (n : Nat) (t1 : Int) (vo : Option Str) (L1 : List Entry) (c : Int)
    (ro : List Str) (cf : Confirmed) (msgs : List Fact) (votes : List VoteRec) (ld : List LeaderRec)
    (ll : TermFn (List Entry)) (p : Pre) (ch : List Entry) (tl : TermFn Int) (vi : SSet) : State :=
  { S with
    currentTerm := S.currentTerm.set n t1
    voteTerm := (match vo with | some _ => S.voteTerm.set n t1 | none => S.voteTerm)
    voteFor := (match vo with | some x => S.voteFor.set n x | none => S.voteFor)
    log := S.log.set n L1
    commitIndex := S.commitIndex.set n c
    role := ro
    confirmed := S.confirmed.set n cf
    msgs := msgs
    votes := votes
    leaders := ld
    ledLog := ll
    undo := S.undo.set n (some p)
    chain := ch
    termLen := tl
    viol := vi }

/-! ## A reported message's fields -/

section msgs
variable (m : Msg) (to : w64)
theorem mo_typ : (msgOf m to).typ = .ok (msgTypeStr m.ty) := rfl
theorem mo_from : (msgOf m to).from_ = .ok (nameOf m.src) := rfl
theorem mo_to : (msgOf m to).to_ = .ok (nameOf to) := rfl
theorem mo_term : (msgOf m to).term_ = .ok (uint.Z m.term) := rfl
theorem mo_index : (msgOf m to).index_ = .ok (uint.Z m.index) := rfl
theorem mo_logTerm : (msgOf m to).logTerm_ = .ok (uint.Z m.logterm) := rfl
theorem mo_entries : (msgOf m to).entries_ = .ok (logOf m.entries) := rfl
theorem mo_commit : (msgOf m to).commit_ = .ok (uint.Z m.commit) := rfl
theorem mo_reject : (msgOf m to).reject_ = .ok m.reject := rfl

/-- A vote request's fact (B 63-65). -/
def vfOf : Fact :=
  { type := go!"vote", src := nameOf m.src, term := uint.Z m.term, lastLogIndex := uint.Z m.index,
    lastLogTerm := uint.Z m.logterm }
theorem mo_voteFact : voteFact (msgOf m to) = .ok (vfOf m) := rfl
end msgs

set_option hygiene false in
/-- `OnDisk` of a `ready` report at node `n` (`hc : S.cfg = cfg3`) evaluated: `onDiskB` at a named
record `x` (`hX`), its pieces rewritten with the joins kept (`zeta := false`), then the joins
inlined. -/
local syntax "od_run" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

set_option hygiene false in
macro_rules
  | `(tactic| od_run [$hs,*]) => `(tactic|
    (rw [onDisk_eq, server_of hc n]
     generalize hX : (⟨_, _, _, false, _, _, _, _, _, _⟩ : OnDisk) = x
     unfold onDiskB
     simp (config := { zeta := false, decide := true }) only [$hs,*, ox_T1 hX, ox_T0 hX, ox_L0 hX,
       ox_snaps hX, ox_hasM hX, ox_m hX, ox_isApp hX, ox_below hX, ox_takes hX, ox_es hX, ox_first hX,
       ox_stores hX, ox_leads hX, ox_moved hX, ox_adv hX, ox_elect hX, ox_adopt hX, ox_V1 hX, ox_voted hX,
       ox_old hX, ox_w hX, ev_vote, ev_commit, ev_term, ev_role, ev_snap, ev_entries, cand_leader,
       fol_leader, fol_cand, leader_cand, beq_self_str, roleOf_beq_leader, roleOf_beq_cand, reduceCtorEq,
       decide_true, decide_false, notM_ok, bne_self_eq_false, eok_bind, epure, server_of hc n, andM_true,
       andM_false, orM_true, orM_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_true,
       ite_false, Bool.true_and, Bool.and_true, Bool.false_and, Bool.and_false, Bool.or_false,
       Bool.false_or, logOf, List.map_nil, List.length_nil, fieldEq, need, msgSeqHead, mo_typ, mo_from, mo_to,
       mo_term, mo_index, mo_logTerm, mo_entries, mo_commit, mo_reject, mo_voteFact, msgTypeStr,
       cons_bne_nil, isReq, beq_self_eq_true]
     simp only [$hs,*, eok_bind, epure, entriesEqual_self, Bool.not_true, Bool.false_eq_true, ite_false,
       ite_true, andM_false, orM_false, Bool.false_or, Bool.or_false, andM_true, Bool.not_false,
       beq_self_eq_true]))

theorem cons_bne_nil {α : Type} [BEq α] (x : α) (l : List α) : ((x :: l) != []) = true := rfl

/-- **A campaign's `OnDisk`** (`TickEnd`'s campaign, `elect`): the next term, the node's own vote,
nothing else written; its vote request and its vote recorded. -/
theorem onDisk_camp {S : State} (n : Fin 3) (hc : S.cfg = cfg3) (t c : w64)
    (ro : List Str) (ld : List LeaderRec) (ll : TermFn (List Entry)) (ch : List Entry)
    (tl : TermFn Int) (vi : SSet)
    (ht : uint.Z t = S.currentTerm[n.val]! + 1) (hcm : uint.Z c = S.commitIndex[n.val]!)
    (hro : ro[n.val]! = candidate) :
    ∃ p : Pre, p.made = false ∧
      S.onDisk n.val ⟨evReady (nodeId n) go!"tick" .candidate t (nodeId n) c [], []⟩ false ro ld ll ch tl vi
        = .ok (some (odS S n.val (uint.Z t) (some (nameOf (nodeId n))) (S.log[n.val]!) (uint.Z c) ro
            (S.confirmed[n.val]!) (lset.add S.msgs (S.voteRequest n.val (uint.Z t)))
            (lset.add S.votes { voter := nameOf (nodeId n), term := uint.Z t, cand := nameOf (nodeId n) })
            ld ll p ch tl vi)) := by
  have hne : (uint.Z t != S.currentTerm[n.val]!) = true := by
    rw [bne_iff_ne]; omega
  have hge : decide (uint.Z t ≥ S.currentTerm[n.val]!) = true := decide_eq_true (by omega)
  have hcm' : (uint.Z c != S.commitIndex[n.val]!) = false := by rw [hcm]; exact bne_self_eq_false _
  have hadv : decide (uint.Z c > S.commitIndex[n.val]!) = false := decide_eq_false (by omega)
  have hvn : (nameOf (nodeId n) != ([] : Str)) = true := ready_name_ne n
  have hst : (uint.Z t == S.currentTerm[n.val]! + 1) = true := by rw [ht]; exact beq_self_eq_true _
  od_run [ox_L1_nil hX, ox_acks_nil hX hcm', ox_conf1_nil hX hcm', ox_ch1_noadv hX hadv, hst, hne, hge,
    hcm', hadv, hvn, hro]
  exact ⟨_, rfl, rfl⟩

/-- **A vote granted** (`HandleEnd`'s grant, after the preamble): the vote for the request's sender
written at the request's term, which is the node's (`hT`: the same, `V1` then empty, or adopted from
the request, which a node of that term sent); nothing else written; the vote recorded. -/
theorem onDisk_grant {S : State} (n : Fin 3) (hc : S.cfg = cfg3) (t c : w64) (m : Msg)
    (ro : List Str) (ld : List LeaderRec) (ll : TermFn (List Entry)) (ch : List Entry)
    (tl : TermFn Int) (vi : SSet)
    (hty : m.ty = .vote) (hmt : m.term = t) (hsrc : nameOf m.src ≠ [])
    (hT : (uint.Z t = S.currentTerm[n.val]! ∧ S.vote n.val = []) ∨
      (S.currentTerm[n.val]! < uint.Z t ∧ ∃ j : Fin 3, j ≠ n ∧ uint.Z t ≤ S.currentTerm[j.val]!))
    (hcm : uint.Z c = S.commitIndex[n.val]!) (hro : ro[n.val]! = follower)
    (hf1 : S.msgs.contains (vfOf m) = true) (hf2 : S.upToDate (vfOf m) n.val = true) :
    ∃ p : Pre, p.made = false ∧
      S.onDisk n.val ⟨evReady (nodeId n) go!"recv" .follower t m.src c [], [msgOf m (nodeId n)]⟩ false ro ld
          ll ch tl vi
        = .ok (some (odS S n.val (uint.Z t) (some (nameOf m.src)) (S.log[n.val]!) (uint.Z c) ro
            (S.confirmed[n.val]!) S.msgs
            (lset.add S.votes { voter := nameOf (nodeId n), term := uint.Z t, cand := nameOf m.src })
            ld ll p ch tl vi)) := by
  subst hmt
  have hcm' : (uint.Z c != S.commitIndex[n.val]!) = false := by rw [hcm]; exact bne_self_eq_false _
  have hadv : decide (uint.Z c > S.commitIndex[n.val]!) = false := decide_eq_false (by omega)
  have hsrc' : (nameOf m.src != ([] : Str)) = true := by rw [bne_iff_ne]; exact hsrc
  rcases hT with ⟨ht, hv⟩ | ⟨ht, j, hj, htj⟩
  · have hne : (uint.Z m.term != S.currentTerm[n.val]!) = false := by rw [ht]; exact bne_self_eq_false _
    have hge : decide (uint.Z m.term ≥ S.currentTerm[n.val]!) = true := decide_eq_true (by omega)
    od_run [ox_L1_nil hX, ox_acks_nil hX hcm', ox_conf1_nil hX hcm', ox_ch1_noadv hX hadv, hne, hge,
      hcm', hadv, hsrc', hro, hv, hty, hf1, hf2]
    exact ⟨_, rfl, rfl⟩
  · have hne : (uint.Z m.term != S.currentTerm[n.val]!) = true := by rw [bne_iff_ne]; omega
    have hge : decide (uint.Z m.term ≥ S.currentTerm[n.val]!) = true := decide_eq_true (by omega)
    have hany : ((List.range (List.length S.cfg.server)).any fun k =>
        k != n.val && decide (S.currentTerm[k]! ≥ uint.Z m.term)) = true := by
      rw [List.any_eq_true]
      refine ⟨j.val, ?_, ?_⟩
      · rw [List.mem_range, hc, cfg3_server]; simp [namesL]
      · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
        exact ⟨fun h => hj (Fin.ext h), htj⟩
    od_run [ox_L1_nil hX, ox_acks_nil hX hcm', ox_conf1_nil hX hcm', ox_ch1_noadv hX hadv, hne, hge,
      hcm', hadv, hsrc', hro, hty, hf1, hf2, hany]
    exact ⟨_, rfl, rfl⟩

/-- **A role change only** (`HandleEnd`'s loss, `padoptLeader` at the node's term with nothing
stored or committed): the term, vote, log and commit as they were. -/
theorem onDisk_same {S : State} (n : Fin 3) (hc : S.cfg = cfg3) (b : Str) (r : Role) (t v c : w64)
    (M : List AntCheck.Msg) (ro : List Str) (ld : List LeaderRec) (ll : TermFn (List Entry))
    (ch : List Entry) (tl : TermFn Int) (vi : SSet) (hr : r ≠ .leader)
    (ht : uint.Z t = S.currentTerm[n.val]!) (hv : nameOf v = S.vote n.val)
    (hcm : uint.Z c = S.commitIndex[n.val]!) (hro : ro[n.val]! = roleOf r) :
    ∃ p : Pre, p.made = false ∧
      S.onDisk n.val ⟨evReady (nodeId n) b r t v c [], M⟩ false ro ld ll ch tl vi
        = .ok (some (odS S n.val (uint.Z t) none (S.log[n.val]!) (uint.Z c) ro (S.confirmed[n.val]!)
            S.msgs S.votes ld ll p ch tl vi)) := by
  have hcm' : (uint.Z c != S.commitIndex[n.val]!) = false := by rw [hcm]; exact bne_self_eq_false _
  have hadv : decide (uint.Z c > S.commitIndex[n.val]!) = false := decide_eq_false (by omega)
  have hne : (uint.Z t != S.currentTerm[n.val]!) = false := by rw [ht]; exact bne_self_eq_false _
  have hge : decide (uint.Z t ≥ S.currentTerm[n.val]!) = true := decide_eq_true (by omega)
  have hv' : (nameOf v != S.vote n.val) = false := by rw [hv]; exact bne_self_eq_false _
  have hrl : (roleOf r == leader) = false := by rw [roleOf_beq_leader]; exact decide_eq_false hr
  od_run [ox_L1_nil hX, ox_acks_nil hX hcm', ox_conf1_nil hX hcm', ox_ch1_noadv hX hadv, hne, hge,
    hcm', hadv, hv', hro, hrl]
  exact ⟨_, rfl, rfl⟩

/-- **A term adopted only** (`PreEnd`'s `pbecomeFollower` at the handled message's term, no vote,
nothing stored or committed; a node of that term sent it, `hj`). -/
theorem onDisk_adopt {S : State} (n : Fin 3) (hc : S.cfg = cfg3) (t c : w64) (m : Msg)
    (ro : List Str) (ld : List LeaderRec) (ll : TermFn (List Entry)) (ch : List Entry)
    (tl : TermFn Int) (vi : SSet) (hmt : m.term = t)
    (ht : S.currentTerm[n.val]! < uint.Z t) (hj : ∃ j : Fin 3, j ≠ n ∧ uint.Z t ≤ S.currentTerm[j.val]!)
    (hcm : uint.Z c = S.commitIndex[n.val]!) (hro : ro[n.val]! = follower) :
    ∃ p : Pre, p.made = false ∧
      S.onDisk n.val ⟨evReady (nodeId n) go!"recv" .follower t (W64 0) c [], [msgOf m (nodeId n)]⟩ false ro ld
          ll ch tl vi
        = .ok (some (odS S n.val (uint.Z t) none (S.log[n.val]!) (uint.Z c) ro (S.confirmed[n.val]!)
            S.msgs S.votes ld ll p ch tl vi)) := by
  subst hmt
  obtain ⟨j, hj, htj⟩ := hj
  have hcm' : (uint.Z c != S.commitIndex[n.val]!) = false := by rw [hcm]; exact bne_self_eq_false _
  have hadv : decide (uint.Z c > S.commitIndex[n.val]!) = false := decide_eq_false (by omega)
  have hne : (uint.Z m.term != S.currentTerm[n.val]!) = true := by rw [bne_iff_ne]; omega
  have hge : decide (uint.Z m.term ≥ S.currentTerm[n.val]!) = true := decide_eq_true (by omega)
  have h0 : nameOf (W64 0) = [] := by simp [nameOf]
  have hany : ((List.range (List.length S.cfg.server)).any fun k =>
      k != n.val && decide (S.currentTerm[k]! ≥ uint.Z m.term)) = true := by
    rw [List.any_eq_true]
    refine ⟨j.val, ?_, ?_⟩
    · rw [List.mem_range, hc, cfg3_server]; simp [namesL]
    · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
      exact ⟨fun h => hj (Fin.ext h), htj⟩
  od_run [ox_L1_nil hX, ox_acks_nil hX hcm', ox_conf1_nil hX hcm', ox_ch1_noadv hX hadv, hne, hge,
    hcm', hadv, hro, hany, h0]
  exact ⟨_, rfl, rfl⟩

end pieces

end AntSim
end EtcdGrove
end Perennial
