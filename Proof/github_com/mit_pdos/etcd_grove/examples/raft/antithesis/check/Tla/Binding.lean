/-
Lean-first (no Rocq counterpart).

# Antithesis's TLA+ model of raft in Lean: the binding (#33 S3b)

The operators and actions of `EtcdBinding.tla` (B; Go: `binding.go`). An action is
`EvalM (Option State)`: `some` its successor, `none` where the TLA+ action is false, an error
where TLC stops with an evaluation error. See `Types.lean` for the conventions; as there, a
conjunction's later conjuncts are evaluated (`andM`, `orM`, nested `do` blocks) only where the
TLA+ evaluates them, so that this definition errs exactly where the Go panics.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Tla.Raft

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntCheck

/-- `~a`. -/
def notM (a : EvalM Bool) : EvalM Bool := do pure !(← a)

/-- `\E x \in xs : f(x)`, evaluated in order, stopping at the first `x` that holds (Go: a loop
with `break`). -/
def anyM {α : Type} : List α → (α → EvalM Bool) → EvalM Bool
  | [], _ => pure false
  | x :: xs, f => do if (← f x) then pure true else anyM xs f

/-- The elements of `xs` satisfying `f`, in order (Go: a loop appending). -/
def filterM {α : Type} (xs : List α) (f : α → EvalM Bool) : EvalM (List α) :=
  xs.foldlM (fun out x => do if (← f x) then pure (out ++ [x]) else pure out) []

/-- `x == v` for a report's field `x` (an error if absent). -/
def fieldEq {α : Type} [BEq α] (x : Option α) (v : α) : EvalM Bool := do pure ((← need x) == v)

/-! ## Message accessors (Go: `Msg.typ`, ...) -/

def Msg.typ (m : Msg) : EvalM Str := need m.type
def Msg.from_ (m : Msg) : EvalM Str := need m.frm
def Msg.to_ (m : Msg) : EvalM Str := need m.to
def Msg.term_ (m : Msg) : EvalM Int := need m.term
def Msg.index_ (m : Msg) : EvalM Int := need m.index
def Msg.logTerm_ (m : Msg) : EvalM Int := need m.logTerm
def Msg.entries_ (m : Msg) : EvalM (List Entry) := need m.entries
def Msg.commit_ (m : Msg) : EvalM Int := need m.commit
def Msg.reject_ (m : Msg) : EvalM Bool := need m.reject

/-! ## Facts from reported messages (B 61-100) -/

/-- B 63-65 `VoteFact(m)`. -/
def voteFact (m : Msg) : EvalM Fact := do
  let src ← m.from_
  let term ← m.term_
  let lli ← m.index_
  let llt ← m.logTerm_
  pure { type := go!"vote", src, term, lastLogIndex := lli, lastLogTerm := llt }

/-- B 68-71 `AppendFact(m)` (Go: `ToAppendFact`). -/
def toAppendFact (m : Msg) : EvalM AppendFact := do
  let src ← m.from_
  let dst ← m.to_
  let term ← m.term_
  let p ← m.index_
  let pt ← m.logTerm_
  let es ← m.entries_
  let c ← m.commit_
  pure { src, dst, term, prevLogIndex := p, prevLogTerm := pt, entries := es, commit := c }

/-- B 73 `AckFact`. -/
def ackFact (src dst : Str) (t k : Int) : Fact :=
  { type := go!"ack", src, dst, term := t, index := k }

/-- B 75 `IsReq(m) == m.type \in {"app", "hb", "snap"}`. -/
def isReq (m : Msg) : EvalM Bool := do
  let t ← m.typ
  pure (t == go!"app" || t == go!"hb" || t == go!"snap")

/-- B 80-83 `SnapOk(ll, m)`. -/
def snapOk (ll : TermFn (List Entry)) (m : Msg) : EvalM Bool := do
  if (← m.typ) != go!"snap" then return true
  let t ← m.term_
  if !ll.has t then return false
  let k ← m.index_
  let l ← ll.get t
  if !decide (k ≤ l.length) then return false
  return termAt l k == (← m.logTerm_)

/-- B 85-91 `ReqFactIn(ll, m)`: a snapshot as a request to append the leader log's prefix. -/
def reqFactIn (ll : TermFn (List Entry)) (m : Msg) : EvalM AppendFact := do
  if (← m.typ) == go!"snap" then
    let t ← m.term_
    let es ← if ll.has t then do subSeq (← ll.get t) 1 (← m.index_) else pure []
    let src ← m.from_
    let dst ← m.to_
    let t ← m.term_
    let k ← m.index_
    return { src, dst, term := t, prevLogIndex := 0, prevLogTerm := 0, entries := es, commit := k }
  toAppendFact m

/-- B 96 `BootTerm`. -/
def State.bootTerm (s : State) : Int := if s.cfg.bootstrapped then 1 else 0

/-- B 99 `VoteOf(vt, vf, t)`. -/
def State.voteOf (s : State) (vt : Int) (vf : Str) (t : Int) : Str :=
  if vt == t && decide (t > s.bootTerm) then vf else []

/-- B 100 `Vote(n)`. -/
def State.vote (s : State) (n : Nat) : Str := s.voteOf (s.voteTerm[n]!) (s.voteFor[n]!) (s.currentTerm[n]!)

/-! ## Committed prefixes (B 102-143) -/

/-- B 109-112 `RecordedIn(ch, tl, l, c, t)`. -/
def recordedIn (ch : List Entry) (tl : TermFn Int) (l : List Entry) (c t : Int) : EvalM Bool := do
  if !(decide (c ≤ l.length) && decide (c ≤ ch.length)) then return false
  if !tl.any (fun p => decide (p.1 ≤ t) && decide (p.2 ≥ c)) then return false
  entriesEqual (← subSeq ch 1 c) (← subSeq l 1 c)

/-- B 117-126 `SendableIn(ld, ll, ch, tl, f)`. -/
def sendableIn (ld : List LeaderRec) (ll : TermFn (List Entry)) (ch : List Entry) (tl : TermFn Int)
    (f : AppendFact) : EvalM Bool := do
  if !ld.contains { server := f.src, term := f.term } then return false
  if !ll.has f.term then return false
  let l ← ll.get f.term
  let p := f.prevLogIndex
  let k : Int := f.entries.length
  if !decide (p + k ≤ l.length) then return false
  if f.prevLogTerm != termAt l p then return false
  if !(← entriesEqual f.entries (← subSeq l (p + 1) (p + k))) then return false
  orM (pure (f.commit == 0)) (recordedIn ch tl l f.commit f.term)

/-- B 128 `Sendable(f)`. -/
def State.sendable (s : State) (f : AppendFact) : EvalM Bool :=
  sendableIn s.leaders s.ledLog s.chain s.termLen f

/-- B 130 `Comparable(a, b)`. -/
def comparable (a b : List Entry) : EvalM Bool := orM (isPrefix a b) (isPrefix b a)

/-- B 132-134 `Matching(a, b)`: for `k` in `1..Min(Len(a), Len(b))`, entries of equal terms are
equal and so are their predecessors' terms; stops at the first `k` that fails. -/
def matching (a b : List Entry) : EvalM Bool :=
  (List.range (min a.length b.length)).foldlM (fun ok (i : Nat) => do
    if !ok then return false
    if (a[i]!).term == (b[i]!).term then
      if !(← (a[i]!).equal (b[i]!)) then return false
      if i > 0 && (a[i - 1]!).term != (b[i - 1]!).term then return false
    return true) true

/-- B 139 `MemCommit(n)`. -/
def State.memCommit (s : State) (n : Nat) : EvalM Int :=
  match (s.queue[n]!).getLast? with
  | none => pure (s.commitIndex[n]!)
  | some q => need q.ev.commit

/-- B 142-143 `SameConf(ev, C)`. -/
def sameConf (ev : Event) (c : Conf) : EvalM Bool :=
  match ev.voters with
  | none => pure true
  | some v => andM (pure (setOf v == c.cin)) (do pure (setOf (← need ev.outgoing) == c.cout))

/-! ## Announced writes (B 146-194) -/

/-- B 152 `EffTerm(j)`. -/
def State.effTerm (s : State) (j : Nat) : Int :=
  match s.undo[j]! with
  | none => s.currentTerm[j]!
  | some u => imin (s.currentTerm[j]!) u.term

/-- B 153 `Over(t)`. -/
def State.over (s : State) (t : Int) : Bool :=
  (List.range s.cfg.server.length).all (fun j => decide (s.effTerm j > t))

/-- B 155-157 `Recovered(ev, t, v, c, l)`. -/
def recovered (ev : Event) (t : Int) (v : Str) (c : Int) (l : List Entry) : EvalM Bool :=
  andM (fieldEq ev.term t) <| andM (fieldEq ev.vote v) <| andM (fieldEq ev.commit c) <|
    andM (fieldEq ev.lastIndex l.length) (fieldEq ev.lastTerm (termAt l l.length))

/-- B 162-194 `Boot(n, ev)`. -/
def State.boot (s : State) (n : Nat) (ev : Event) : EvalM (Option State) := do
  let mut ns := { s with undo := s.undo.set n none, pending := s.pending.set n [],
                         queue := s.queue.set n [], reads := s.reads.set n [],
                         role := s.role.set n follower }
  if !(← recovered ev (s.currentTerm[n]!) (s.vote n) (s.commitIndex[n]!) (s.log[n]!)) then
    match s.undo[n]! with
    | none => return none
    | some u =>
      if u.made then return none
      let l := (← subSeq (s.log[n]!) 1 u.keep) ++ u.suffix
      if !(← recovered ev u.term (s.voteOf u.voteTerm u.voteFor u.term) u.commit l) then return none
      ns := { ns with currentTerm := s.currentTerm.set n u.term, voteTerm := s.voteTerm.set n u.voteTerm,
                      voteFor := s.voteFor.set n u.voteFor, commitIndex := s.commitIndex.set n u.commit,
                      log := s.log.set n l, confirmed := s.confirmed.set n u.confirmed,
                      msgs := lset.minus s.msgs u.msgs, votes := lset.minus s.votes u.votes }
  let a ← if ev.applied.isSome then need ev.applied else pure 0
  let logn := ns.log[n]!
  if !(← orM (pure (a == 0))
        (andM (pure (decide (a ≤ logn.length) && decide (a ≤ s.chain.length)))
          (do entriesEqual (← subSeq s.chain 1 a) (← subSeq logn 1 a)))) then
    return none
  ns := { ns with lastApplied := s.lastApplied.set n a }
  let c ← confOf logn a s.initConf
  ns := { ns with config := s.config.set n c }
  ns := { ns with confAt := s.confAt.set n (← lastConf logn a) }
  if !(← sameConf ev c) then return none
  return some ns

/-- B 199-204 `Recv(n, ev)`. -/
def State.recv (s : State) (n : Nat) (ev : Event) : EvalM (Option State) := do
  let m ← need ev.msg
  if (← m.to_) != s.cfg.server[n]! then return none
  let ns := { s with pending := s.pending.set n [m] }
  if (← andM (isReq m) (do pure (decide ((← m.term_) ≥ s.currentTerm[n]!)))) then
    if !(← andM (snapOk s.ledLog m) (do s.sendable (← reqFactIn s.ledLog m))) then return none
  return some ns

/-! ## What a report did in memory (B 213-275 `InMemory`) -/

/-- The record `InMemory` returns (B 231-275; Go: `MemResult`). -/
structure MemResult where
  ok : Bool
  role : List Str
  leaders : List LeaderRec
  ledLog : TermFn (List Entry)
  ledConf : TermFn Conf
  config : List Conf
  confAt : List Int
  ledAt : TermFn Int
  elAt : TermFn Int
  chain : List Entry
  termLen : TermFn Int
  viol : SSet
  deriving DecidableEq, Repr, Inhabited

/-- `InMemory`'s arguments; its LET definitions (B 214-230) are its functions below, each
evaluated where the TLA+ uses it (Go: `inMem`). -/
structure InMem where
  s : State
  n : Nat
  ev : Event

namespace InMem
variable (x : InMem)

def T : EvalM Int := need x.ev.term
def role1 : EvalM Str := do
  let r ← need x.ev.role
  pure (if r == go!"precandidate" then follower else r)
def leads : EvalM Bool := fieldEq x.ev.role leader
def wins : EvalM Bool := andM x.leads (pure (x.s.role[x.n]! != leader))
def es : EvalM (List Entry) := if x.ev.entries.isSome then need x.ev.entries else pure []
def ld1 : EvalM (List LeaderRec) := do
  if (← x.wins) then pure (lset.add x.s.leaders { server := x.s.cfg.server[x.n]!, term := ← x.T })
  else pure x.s.leaders
def ll1 : EvalM (TermFn (List Entry)) := do
  if (← x.wins) then pure (x.s.ledLog.with (← x.T) (x.s.log[x.n]!)) else pure x.s.ledLog
def lc1 : EvalM (TermFn Conf) := do
  if (← x.wins) then pure (x.s.ledConf.with (← x.T) (x.s.config[x.n]!)) else pure x.s.ledConf
def snapsM : Bool := x.ev.snap.isSome
def known : EvalM Int := do
  let t ← x.T
  if x.s.termLen.has t then x.s.termLen.get t else pure 0
def app : EvalM Bool := andM x.leads (do pure ((← x.es).length != 0))
def ll2 : EvalM (TermFn (List Entry)) := do
  if (← andM x.app (do pure ((← x.ll1).has (← x.T)))) then
    let ll1 ← x.ll1
    let t ← x.T
    pure (ll1.with t ((← ll1.get t) ++ (← x.es)))
  else x.ll1
def L : EvalM (List Entry) := do
  let ll2 ← x.ll2
  let t ← x.T
  if ll2.has t then ll2.get t else pure []
def c : EvalM Int := need x.ev.commit
def cmt : EvalM Bool :=
  andM x.leads <| andM (do let c ← x.c; pure (decide (c > (← x.known))))
    (do let l ← x.L; let c ← x.c; pure (termAt l c == (← x.T)))
def newC : EvalM (List Entry) := do subSeq (← x.L) 1 (← x.c)

/-- `ok` (B 231-253). -/
def ok : EvalM Bool := do
  let s := x.s
  let n := x.n
  let ev := x.ev
  let by_ ← need ev.byE
  if !(by_ == go!"recv" || by_ == go!"tick" || by_ == go!"campaign" || by_ == go!"propose" ||
      by_ == go!"write" || by_ == go!"apply" || by_ == go!"boot" || by_ == go!"transfer" ||
      by_ == go!"snapstatus" || by_ == go!"read") then return false
  let r ← need ev.role
  if !(r == follower || r == candidate || r == leader || r == go!"precandidate") then return false
  if x.snapsM then
    if !(← andM (do pure ((← need ev.role) != leader)) <| andM (pure (s.role[n]! != leader))
          (do pure (decide ((← need ev.snap).index ≤ s.chain.length)))) then return false
  if (← x.wins) then
    if !(← andM (pure (s.role[n]! == candidate)) (do pure (s.currentTerm[n]! == (← x.T)))) then
      return false
    if s.ledLog.has (← x.T) then return false
    if !isQuorum (s.granted n) (s.config[n]!) then return false
    if !(← s.oneWaiting n (s.log[n]!)) then return false
    if !(← orM (pure (s.confAt[n]! == 0))
          (do recordedIn s.chain s.termLen (s.log[n]!) (s.confAt[n]!) ((← x.T) - 1))) then
      return false
  if (← x.leads) then
    if !(← andM (do pure (s.currentTerm[n]! == (← x.T))) <|
          andM (do pure ((← x.ll1).has (← x.T))) (do let c ← x.c; pure (decide (c ≤ (← x.L).length)))) then
      return false
  if (← x.app) then
    if ev.first.isSome then
      let f ← need ev.first
      if f != ((← (← x.ll1).get (← x.T)).length : Int) + 1 then return false
    let es ← x.es
    if (← anyM es (fun e => do pure (e.term != (← x.T)))) then return false
    let bad ← anyM (List.range es.length) (fun q => do
      let e := es[q]!
      if !isConf e then return false
      if !(← s.allSwitched n (← (← x.ll1).get (← x.T))) then return true
      if (List.range q).any (fun r => isConf (es[r]!)) then return true
      return !(← legal (s.config[n]!) e.value))
    if bad then return false
  if (← andM x.leads (do pure (decide ((← x.c) > 0)))) then
    if (← x.cmt) then return isQuorum (s.acked n (← x.T) (← x.c)) (← (← x.lc1).get (← x.T))
    return (← recordedIn s.chain s.termLen (← x.L) (← x.c) (← x.T))
  return true

end InMem

/-- B 213-275 `InMemory(n, ev)`. TLC builds the record whole (every field evaluated, in order),
so an evaluation error in any field is one even where `ok` is false. -/
def State.inMemory (s : State) (n : Nat) (ev : Event) : EvalM MemResult := do
  let x : InMem := { s, n, ev }
  let ok ← x.ok
  let role := s.role.set n (← x.role1)
  let leaders ← x.ld1
  let ledLog ← x.ll2
  let ledConf ← x.lc1
  let (config, confAt) ← if x.snapsM then do
      let k := (← need ev.snap).index
      let c ← confOf s.chain k s.initConf
      let a ← lastConf s.chain (← need ev.snap).index
      pure (s.config.set n c, s.confAt.set n a)
    else pure (s.config, s.confAt)
  let (ledAt, elAt) ← if (← x.wins) then do
      pure (s.ledAt.with (← x.T) (s.confAt[n]!), s.elAt.with (← x.T) (s.confAt[n]!))
    else pure (s.ledAt, s.elAt)
  let chain ← if (← andM x.cmt (do pure (decide ((← x.c) > s.chain.length)))) then x.newC
    else pure s.chain
  let termLen ← if (← x.cmt) then do pure (s.termLen.with (← x.T) (← x.c)) else pure s.termLen
  let mut viol := s.viol
  if (← andM x.cmt (notM (do comparable s.chain (← x.newC)))) then
    viol := setAdd viol go!"CommitSafety"
  let mut lc := false
  if (← x.cmt) then
    lc ← anyM (← x.ll2) (fun p => andM (do pure (decide (p.1 > (← x.T))))
      (notM (do isPrefix (← x.newC) p.2)))
  if (← andM (pure !lc) x.wins) then
    lc ← anyM s.termLen (fun p => andM (do pure (decide (p.1 < (← x.T))))
      (notM (do isPrefix (← subSeq s.chain 1 p.2) (s.log[n]!))))
  if lc then viol := setAdd viol go!"LeaderCompleteness"
  let me := s.cfg.server[n]!
  if (← need ev.role) == candidate && s.role[n]! != candidate &&
      !((s.config[n]!).cin.has me || (s.config[n]!).cout.has me) then
    viol := setAdd viol go!"Unpromotable"
  return { ok, role, leaders, ledLog, ledConf, config, confAt, ledAt, elAt, chain, termLen, viol }

/-! ## What a write did on disk (B 288-436 `OnDisk`) -/

/-- B 288 `Lowest(a, b)`. -/
def lowest (a b : Int) : Int := if a == 0 then b else if b == 0 then a else imin a b

/-- `OnDisk`'s arguments; its LET definitions (B 291-359) are its functions below, each evaluated
where the TLA+ uses it (Go: `onDisk`). -/
structure OnDisk where
  s : State
  n : Nat
  q : QItem
  more : Bool
  ro : List Str
  ld : List LeaderRec
  ll : TermFn (List Entry)
  ch : List Entry
  tl : TermFn Int
  vi : SSet

namespace OnDisk
variable (x : OnDisk)

def w : Event := x.q.ev
def hasM : Bool := x.q.m != []
def m : EvalM Msg := msgSeqHead x.q.m
def T0 : Int := x.s.currentTerm[x.n]!
def T1 : EvalM Int := need x.w.term
def elect : EvalM Bool := andM (do pure ((← x.T1) != x.T0)) (fieldEq x.w.role candidate)
def adopt : EvalM Bool := andM (do pure ((← x.T1) != x.T0)) (notM x.elect)
def V1 : EvalM Str := do if (← x.T1) != x.T0 then pure [] else pure (x.s.vote x.n)
def voted : EvalM Bool := do let v ← need x.w.vote; pure (v != (← x.V1))
def L0 : List Entry := x.s.log[x.n]!
def leads : EvalM Bool := fieldEq x.w.role leader
def moved : EvalM Bool := do pure ((← need x.w.commit) != x.s.commitIndex[x.n]!)
def fm : EvalM AppendFact := do reqFactIn x.ll (← x.m)
def snaps : Bool := x.w.snap.isSome
def bat : Bool := x.w.entries.isNone
def isApp : EvalM Bool :=
  andM (pure x.bat) <| andM (pure x.hasM) <| andM (do pure ((← (← x.m).typ) == go!"app"))
    (do pure ((← (← x.m).term_) == (← x.T1)))
def below : EvalM Bool := andM x.isApp (do pure (decide ((← x.fm).prevLogIndex < x.s.commitIndex[x.n]!)))
def takes : EvalM Bool := andM x.isApp <| andM (notM x.below) (do x.s.prevOk x.n (← x.fm))

/-- B 314-316 `K`: the least `k` in `Diff` (where the request's entry `k` is not in the log), or
`Len(fm.entries) + 1` when `Diff` is empty. -/
def K : EvalM Int := do
  let fm ← x.fm
  let l0 := x.L0
  let r ← (List.range fm.entries.length).foldlM (fun (acc : Option Int) (i : Nat) => do
    if acc.isSome then return acc
    let k : Int := (i : Int) + 1
    let y := fm.prevLogIndex + k
    if (← orM (pure (decide (y > l0.length)))
          (do pure ((← atE l0 y).term != (fm.entries[i]!).term))) then return some k
    return none) none
  pure (r.getD ((fm.entries.length : Int) + 1))

def es : EvalM (List Entry) := do
  if (← orM (pure x.snaps) x.takes) then
    let fm ← x.fm
    subSeq fm.entries (← x.K) fm.entries.length
  else if x.bat then pure [] else need x.w.entries

def first : EvalM Int := do
  if (← orM (pure x.snaps) x.takes) then pure ((← x.fm).prevLogIndex + (← x.K))
  else if x.w.first.isSome then need x.w.first
  else pure ((x.L0.length : Int) + 1)

def stores : EvalM Bool := do pure ((← x.es).length != 0)

def f : EvalM AppendFact := do
  if (← x.leads) then
    let t1 ← x.T1
    let me := x.s.cfg.server[x.n]!
    let mut f : AppendFact :=
      { src := me, dst := me, term := t1, prevLogIndex := 0, prevLogTerm := 0, entries := ← x.es,
        commit := 0 }
    if (← x.stores) then f := { f with prevLogIndex := (← x.first) - 1 }
    if (← andM x.stores (pure (x.ll.has t1))) then
      f := { f with prevLogTerm := termAt (← x.ll.get t1) ((← x.first) - 1) }
    if (← x.moved) then f := { f with commit := ← need x.w.commit }
    pure f
  else x.fm

def k : EvalM Int := do pure ((← x.first) - (← x.f).prevLogIndex)
def L1 : EvalM (List Entry) := do
  if (← x.stores) then pure ((← subSeq x.L0 1 ((← x.first) - 1)) ++ (← x.es)) else pure x.L0
def last : EvalM Int := do let f ← x.f; pure (f.prevLogIndex + f.entries.length)
def acks : EvalM Bool :=
  orM (andM x.stores x.leads) <|
  orM (andM x.moved <| andM (notM x.leads) <| andM (pure x.hasM) <|
        orM (do pure ((← (← x.m).typ) == go!"app")) (do pure ((← (← x.m).typ) == go!"snap"))) <|
  orM x.takes x.below
def ackAt : EvalM Int := do if (← x.below) then pure (x.s.commitIndex[x.n]!) else x.last
def conf1 : EvalM Confirmed := do
  if (← x.stores) then return { term := ← x.T1, index := ← x.last }
  if (← andM x.acks (notM x.below)) then
    let c := x.s.confirmed[x.n]!
    if c.term == (← x.T1) then return { term := ← x.T1, index := imax c.index (← x.last) }
    return { term := ← x.T1, index := ← x.last }
  return x.s.confirmed[x.n]!
def adv : EvalM Bool := do pure (decide ((← need x.w.commit) > x.s.commitIndex[x.n]!))
def newC : EvalM (List Entry) := do subSeq (← x.L1) 1 (← need x.w.commit)
def ch1 : EvalM (List Entry) := do
  if (← andM x.adv (do pure (decide ((← x.newC).length > x.ch.length)))) then x.newC else pure x.ch
def old : EvalM Int := do
  let t ← x.T1
  if x.tl.has t then x.tl.get t else pure 0

end OnDisk

/-- B 290-436 `OnDisk(n, q, more, ro, ld, ll, ch, tl, vi)`: the successor's variables `OnDisk`
gives (`currentTerm`, `voteTerm`, `voteFor`, `log`, `commitIndex`, `role`, `confirmed`, `msgs`,
`votes`, `leaders`, `ledLog`, `undo`, `chain`, `termLen`, `viol`), the others `s`'s. -/
def State.onDisk (s : State) (n : Nat) (q : QItem) (more : Bool) (ro : List Str)
    (ld : List LeaderRec) (ll : TermFn (List Entry)) (ch : List Entry) (tl : TermFn Int) (vi : SSet) :
    EvalM (Option State) := do
  let x : OnDisk := { s, n, q, more, ro, ld, ll, ch, tl, vi }
  let w := x.w
  let me := s.cfg.server[n]!
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
  if (← andM x.adv (do pure (c1.term != t1 || decide ((← need w.commit) > c1.index)))) then
    viol := setAdd viol go!"CommitBeyondConfirmed"
  return some { ns with viol }

/-- The item of a `ready`/`mem` report: `[ev |-> ev, m |-> IF ev.by = "recv" THEN pending[n] ELSE
<<>>]` (B 441, 452; Go: `queued`). -/
def State.queued (s : State) (n : Nat) (ev : Event) : EvalM QItem := do
  if (← need ev.byE) == go!"recv" then pure { ev, m := s.pending[n]! } else pure { ev, m := [] }

/-- B 439-447 `Ready(n, ev)`. -/
def State.ready (s : State) (n : Nat) (ev : Event) : EvalM (Option State) := do
  if s.queue[n]! != [] then return none
  let r ← s.inMemory n ev
  if !r.ok then return none
  match ← s.onDisk n (← s.queued n ev) false r.role r.leaders r.ledLog r.chain r.termLen r.viol with
  | none => return none
  | some ns =>
    return some { ns with ledConf := r.ledConf, ledAt := r.ledAt, elAt := r.elAt, config := r.config,
                          confAt := r.confAt }

/-- B 450-459 `Mem(n, ev)`. -/
def State.mem (s : State) (n : Nat) (ev : Event) : EvalM (Option State) := do
  let r ← s.inMemory n ev
  if !r.ok then return none
  let ns := { s with role := r.role, leaders := r.leaders, ledLog := r.ledLog, ledConf := r.ledConf,
                     ledAt := r.ledAt, elAt := r.elAt, config := r.config, confAt := r.confAt,
                     chain := r.chain, termLen := r.termLen, viol := r.viol }
  if (← need ev.w) == 1 then
    return some { ns with queue := s.queue.set n (s.queue[n]! ++ [← s.queued n ev]) }
  return some ns

/-- B 462-470 `Write(n, ev)`. -/
def State.write (s : State) (n : Nat) (ev : Event) : EvalM (Option State) := do
  match s.queue[n]! with
  | [] => return none
  | q :: rest =>
    let w := q.ev
    let same ← andM (do pure ((← need ev.term) == (← need w.term))) <|
      andM (do pure ((← need ev.vote) == (← need w.vote))) <|
      andM (do pure ((← need ev.commit) == (← need w.commit))) <|
      andM (do pure ((← need ev.first) == (← need w.first)))
        (do entriesEqual (← need ev.entries) (← need w.entries))
    if !same then return none
    match ← s.onDisk n q false s.role s.leaders s.ledLog s.chain s.termLen s.viol with
    | none => return none
    | some ns => return some { ns with queue := s.queue.set n rest }

/-- B 474-478 `Flush(n, ev)`. -/
def State.flush (s : State) (n : Nat) (ev : Event) : EvalM (Option State) := do
  match s.queue[n]! with
  | [] => return none
  | q :: rest =>
    let more := (← need ev.more) == 1
    match ← s.onDisk n q more s.role s.leaders s.ledLog s.chain s.termLen s.viol with
    | none => return none
    | some ns => return some { ns with queue := s.queue.set n rest }

/-- B 483-492 `Net(n, ev)`. -/
def State.net (s : State) (n : Nat) (ev : Event) : EvalM (Option State) := do
  match s.undo[n]! with
  | none => return none
  | some u =>
    if !(← andM (fieldEq ev.term (s.currentTerm[n]!)) <|
          andM (fieldEq ev.vote (s.vote n)) (fieldEq ev.commit (s.commitIndex[n]!))) then return none
    let es ← need ev.entries
    if es.length == 0 then
      if u.low != 0 then return none
    else
      let ln : Int := (s.log[n]!).length
      if !(← andM (fieldEq ev.first u.low) <|
            andM (do pure (ln == (← need ev.first) + es.length - 1))
              (do entriesEqual (← subSeq (s.log[n]!) (← need ev.first) ln) es)) then return none
    return some { s with undo := s.undo.set n (some { u with low := 0 }) }

/-- B 496-499 `Made(n, ev)`. -/
def State.made (s : State) (n : Nat) (_ev : Event) : EvalM (Option State) :=
  match s.undo[n]! with
  | none => pure none
  | some u => pure (some { s with undo := s.undo.set n (some { u with made := true }) })

/-- B 502-504 `Wrote(n, ev)`. -/
def State.wrote (s : State) (n : Nat) (_ev : Event) : EvalM (Option State) :=
  pure (some { s with undo := s.undo.set n none })

/-! ## Sends (B 506-593) -/

def isForwarded (t : Str) : Bool := t == go!"readindex" || t == go!"transfer" || t == go!"prop"

def isUnmodelled (t : Str) : Bool :=
  t == go!"prevote" || t == go!"prevoteresp" || t == go!"readindex" || t == go!"readindexresp" ||
    t == go!"prop" || t == go!"transfer" || t == go!"timeoutnow"

/-- B 510-593 `Send(n, ev)`. -/
def State.send (s : State) (n : Nat) (ev : Event) : EvalM (Option State) := do
  let m ← need ev.msg
  let me := s.cfg.server[n]!
  let late := ev.cause.isSome
  let bt := ev.b
  let (mine, cast) := match bt, s.undo[n]! with
    | true, some u => (u.msgs, u.votes)
    | _, _ => (([] : List Fact), ([] : List VoteRec))
  let dur := match s.undo[n]! with
    | none => true
    | some u => u.made
  if !(← orM (do pure ((← m.from_) == me)) (do pure (isForwarded (← m.typ)))) then return none
  if !(← andM (do pure (s.cfg.server.has (← m.to_))) (do pure ((← m.to_) != me))) then return none
  let mut ns := s
  if !(late || bt) then ns := { s with undo := s.undo.set n none }
  let t ← m.typ
  if t == go!"vote" then
    if bt then
      if !(← andM (pure dur) (orM (do pure (s.msgs.contains (← voteFact m)))
            (do pure (mine.contains (← voteFact m))))) then return none
    else if !(← andM (do pure ((← m.term_) == s.currentTerm[n]!))
          (do pure (s.msgs.contains (← voteFact m)))) then return none
    return some ns
  if t == go!"voteresp" then
    if !(← m.reject_) then
      let v : VoteRec := { voter := me, term := ← m.term_, cand := ← m.to_ }
      if !(s.votes.contains v || cast.contains v) then return none
      if bt && !dur then return none
      ns := { ns with msgs := lset.add s.msgs { type := go!"grant", src := me, dst := ← m.to_, term := ← m.term_ } }
    return some ns
  if (← isReq m) then
    if !(← orM (pure bt) <| andM (do pure ((← m.term_) == s.currentTerm[n]!))
          (pure (s.role[n]! == leader))) then return none
    if !(← andM (snapOk s.ledLog m) (do s.sendable (← reqFactIn s.ledLog m))) then return none
    return some ns
  if t == go!"appresp" then
    if (← m.reject_) then return some ns
    if bt then
      if (← m.index_) == 0 then return some ns
      let ok ← match s.undo[n]! with
        | none => pure false
        | some u => andM (pure dur) (do pure (u.acks.contains (ackFact me (← m.to_) (← m.term_) (← m.index_))))
      if !ok then return none
      return some ns
    let c ← if late then need ev.cause else pure (s.pending[n]!)
    if (← andM (pure (c != [])) <| andM (isReq (c[0]!))
          (do pure (decide ((← (c[0]!).term_) < s.currentTerm[n]!)))) then
      if !(← andM (do pure ((← m.index_) == 0)) (do pure ((← m.term_) == s.currentTerm[n]!))) then
        return none
      return some ns
    if (← m.index_) == 0 then return some ns
    if c == [] then return none
    let cm ← msgSeqHead c
    let f ← reqFactIn s.ledLog cm
    let last := f.prevLogIndex + f.entries.length
    if !(← andM (orM (do pure ((← cm.typ) == go!"app")) (do pure ((← cm.typ) == go!"snap"))) <|
          andM (snapOk s.ledLog cm) (s.sendable f)) then return none
    if !(← andM (do pure ((← m.to_) == (← cm.from_))) <| andM (do pure ((← m.term_) == (← cm.term_)))
          (do pure (s.currentTerm[n]! == (← cm.term_)))) then return none
    if (← andM (do pure ((← m.index_) == last)) <| andM (s.prevOk n f) (s.hasFirst n f f.entries.length)) then
      let old := s.confirmed[n]!
      let ct ← cm.term_
      let idx := if old.term == ct then imax old.index last else last
      ns := { ns with msgs := lset.add s.msgs (ackFact me (← cm.from_) ct last),
                      confirmed := s.confirmed.set n { term := ct, index := idx } }
      return some ns
    if !(← andM (pure (decide (f.prevLogIndex < s.commitIndex[n]!)))
          (do pure ((← m.index_) == s.commitIndex[n]!))) then return none
    ns := { ns with msgs := lset.add s.msgs (ackFact me (← cm.from_) (← cm.term_) (s.commitIndex[n]!)) }
    return some ns
  if t == go!"hbresp" then
    let t' := if bt then s.effTerm n else s.currentTerm[n]!
    if !decide (t' ≤ (← m.term_)) then return none
    return some ns
  if isUnmodelled t then return some ns
  return none

/-! ## Applying, configurations, snapshots, reads (B 595-667) -/

/-- B 598-609 `ApplyEv(n, ev)`. -/
def State.applyEv (s : State) (n : Nat) (ev : Event) : EvalM (Option State) := do
  if (← need ev.first) != s.lastApplied[n]! + 1 then return none
  let last := (← need ev.first) + (← need ev.entries).length - 1
  if !(decide (last ≤ (s.log[n]!).length) && decide (last ≤ s.chain.length)) then return none
  if !(← entriesEqual (← subSeq s.chain 1 last) (← subSeq (s.log[n]!) 1 last)) then return none
  if !(← entriesEqual (← need ev.entries) (← subSeq (s.log[n]!) (← need ev.first) last)) then return none
  let mut ns := { s with lastApplied := s.lastApplied.set n last }
  if !ev.a then ns := { ns with undo := s.undo.set n none }
  if last > (← s.memCommit n) then ns := { ns with viol := setAdd s.viol go!"ApplyBeyondCommit" }
  return some ns

/-- B 614-630 `ConfEv(n, ev)`. -/
def State.confEv (s : State) (n : Nat) (ev : Event) : EvalM (Option State) := do
  let k ← need ev.index
  let logn := s.log[n]!
  if !(decide (k > s.confAt[n]!) && decide (k ≤ s.lastApplied[n]!) && decide (k ≤ logn.length)) then
    return none
  if !(← andM (pure (decide (k ≤ s.chain.length)))
        (do entriesEqual (← subSeq s.chain 1 k) (← subSeq logn 1 k))) then return none
  if !isConf (← atE logn k) then return none
  let lo := s.confAt[n]! + 1
  if (← anyM (List.range (k - lo).toNat) (fun (i : Nat) => do pure (isConf (← atE logn (lo + i))))) then
    return none
  if !(← legal (s.config[n]!) (← atE logn k).value) then return none
  if (← andM (pure (s.role[n]! == leader))
        (notM (recordedIn s.chain s.termLen logn k (s.currentTerm[n]!)))) then return none
  let c ← nextConf (s.config[n]!) (← atE logn k).value
  if !(← sameConf ev c) then return none
  let mut ns := { s with config := s.config.set n c }
  if s.role[n]! == leader then
    ns := { ns with ledConf := s.ledConf.with (s.currentTerm[n]!) c,
                    ledAt := s.ledAt.with (s.currentTerm[n]!) k }
  return some { ns with confAt := s.confAt.set n k }

/-- B 634-643 `RestoreEv(n, ev)`. -/
def State.restoreEv (s : State) (n : Nat) (ev : Event) : EvalM (Option State) := do
  let k ← need ev.index
  if !(decide (k ≤ (s.log[n]!).length) && decide (k ≤ s.chain.length)) then return none
  if !(← entriesEqual (← subSeq s.chain 1 k) (← subSeq (s.log[n]!) 1 k)) then return none
  let mut ns := { s with lastApplied := s.lastApplied.set n k }
  if !(← sameConf ev (← confOf s.chain k s.initConf)) then return none
  if !ev.a then ns := { ns with undo := s.undo.set n none }
  return some ns

/-- B 647-650 `SnapEv(n, ev)`. -/
def State.snapEv (s : State) (n : Nat) (ev : Event) : EvalM (Option State) := do
  if !(← andM (do pure (decide ((← need ev.index) ≤ s.lastApplied[n]!)))
        (do pure (decide ((← need ev.index) ≤ s.commitIndex[n]!)))) then return none
  if termAt (s.log[n]!) (← need ev.index) != (← need ev.term) then return none
  return some s

/-- B 56 `MaxReads`. -/
def maxReads : Nat := 16

/-- B 657-661 `ReadAsked(n, ev)`. -/
def State.readAsked (s : State) (n : Nat) (ev : Event) : EvalM (Option State) := do
  let r : ReadRec := { ctx := ← need ev.ctx, floor := s.chain.length }
  let q := s.reads[n]! ++ [r]
  let q := if q.length > maxReads then q.drop 1 else q
  return some { s with reads := s.reads.set n q }

/-- B 663-667 `ReadGiven(n, ev)`. -/
def State.readGiven (s : State) (n : Nat) (ev : Event) : EvalM (Option State) := do
  let kept ← filterM (s.reads[n]!) (fun r => do pure (r.ctx != (← need ev.ctx)))
  let stale ← anyM (s.reads[n]!) (fun r =>
    andM (do pure (r.ctx == (← need ev.ctx))) (do pure (decide ((← need ev.index) < r.floor))))
  let ns := { s with reads := s.reads.set n kept }
  if stale then return some { ns with viol := setAdd s.viol go!"ReadIndexStale" }
  return some ns

/-- B 669-686 `Bind(n, ev)`. -/
def State.bind (s : State) (n : Nat) (ev : Event) : EvalM (Option State) :=
  if ev.e == go!"boot" then s.boot n ev
  else if ev.e == go!"recv" then s.recv n ev
  else if ev.e == go!"ready" then s.ready n ev
  else if ev.e == go!"mem" then s.mem n ev
  else if ev.e == go!"write" then s.write n ev
  else if ev.e == go!"wrote" then s.wrote n ev
  else if ev.e == go!"flush" then s.flush n ev
  else if ev.e == go!"net" then s.net n ev
  else if ev.e == go!"made" then s.made n ev
  else if ev.e == go!"send" then s.send n ev
  else if ev.e == go!"apply" then s.applyEv n ev
  else if ev.e == go!"restore" then s.restoreEv n ev
  else if ev.e == go!"conf" then s.confEv n ev
  else if ev.e == go!"snap" then s.snapEv n ev
  else if ev.e == go!"readreq" then s.readAsked n ev
  else if ev.e == go!"read" then s.readGiven n ev
  else pure none

/-! ## Forgetting facts (B 689-723) -/

/-- B 58 `GCBatch`. -/
def gcBatch : Nat := 32

/-- B 696-706 `Garbage`. -/
def State.garbage (s : State) : EvalM (List Fact) :=
  filterM s.msgs (fun m => do
    if m.type == go!"vote" then return s.over m.term
    if m.type == go!"grant" then return decide (s.effTerm (← s.idx m.dst) > m.term)
    if m.type == go!"ack" then
      if decide (s.effTerm (← s.idx m.dst) > m.term) then return true
      return (← anyM s.msgs (fun a => do
        if a.type == go!"ack" && a.src == m.src && a.dst == m.dst && a.term == m.term &&
            decide (a.index > m.index) then
          match s.undo[← s.idx a.src]! with
          | none => return true
          | some u => return !u.msgs.contains a
        return false))
    return false)

/-- B 708 `OldVotes`. -/
def State.oldVotes (s : State) : EvalM (List VoteRec) :=
  filterM s.votes (fun v => do pure (decide (s.effTerm (← s.idx v.voter) > v.term)))

/-- B 709 `StaleLed`. -/
def State.staleLed (s : State) : List Int := (s.ledLog.filter (fun p => s.over p.1)).map Prod.fst

/-- B 711 `GCDue`. -/
def State.gcDue (s : State) : EvalM Bool := do
  let g ← s.garbage
  let o ← s.oldVotes
  pure (decide (g.length + o.length ≥ gcBatch) || s.staleLed.length != 0)

/-- B 713-723 `GC` (without its guard `GCDue`). -/
def State.gc (s : State) : EvalM State := do
  let stale := s.staleLed
  let g ← s.garbage
  let o ← s.oldVotes
  pure { s with msgs := lset.minus s.msgs g, votes := lset.minus s.votes o,
                ledLog := s.ledLog.without stale, ledConf := s.ledConf.without stale,
                ledAt := s.ledAt.without stale, elAt := s.elAt.without stale,
                leaders := s.leaders.filter (fun l => !s.over l.term) }

/-- B 766-772 `Step` (without its guard `~GCDue`): event `i` of the stream bound. -/
def State.step (s : State) (ev : Event) : EvalM (Option State) := do
  if ev.bad != [] then evalError "a report not of the shape the binding reads"
  let n ← s.idx ev.node
  match ← s.bind n ev with
  | none => return none
  | some ns => return some { ns with i := s.i + 1 }

end AntCheck
end EtcdGrove
end Perennial
