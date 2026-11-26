/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: `OnDisk` of a follower's `ready` on a request (#33 S4)

`OnDisk` (B 290-436) of a `ready` report evaluated, as in `ReadyOD.lean` (`onDiskB`, the pieces
rewritten with the joins kept), for a follower that handled a `MsgApp` or a heartbeat
(`notes/antithesis-rawnode-design.md` §3.3): its entries stored from the first conflict and/or its
commit moved (`onDisk_fapp`), its commit moved by a heartbeat (`onDisk_fhb`), with or without the
request's term adopted. Every hypothesis is in the binding's terms (the binding's functions of the
reported request, `afOf`, and of the logs); the safety checks (B 422-436) are hypotheses of the
shape that `ReadySafe.lean` discharges from `GlobalOk` and `RaftLaws`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.ReadyOD

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open AntCheck

section pieces2
variable [GooseExts]

theorem logOf_nil [GooseExts] : logOf [] = [] := rfl
theorem stores_cons [GooseExts] (e : EntryM) (es : List EntryM) : ((logOf (e :: es)).length != 0) = true := rfl

/-- A reported request's append fact (B 68-71, `ToAppendFact(msgOf(m, to))`). -/
def afOf (m : Msg) (to : w64) : AppendFact :=
  { src := nameOf m.src, dst := nameOf to, term := uint.Z m.term, prevLogIndex := uint.Z m.index,
    prevLogTerm := uint.Z m.logterm, entries := logOf m.entries, commit := uint.Z m.commit }

theorem af_src (m : Msg) (to : w64) : (afOf m to).src = nameOf m.src := rfl
theorem af_commit (m : Msg) (to : w64) : (afOf m to).commit = uint.Z m.commit := rfl
theorem af_prev (m : Msg) (to : w64) : (afOf m to).prevLogIndex = uint.Z m.index := rfl
theorem af_len (m : Msg) (to : w64) : (afOf m to).entries.length = m.entries.length := logOf_length _

theorem mo_appendFact (m : Msg) (to : w64) : toAppendFact (msgOf m to) = .ok (afOf m to) := rfl

variable {S : State} {n : Nat} {id : w64} {b : Str} {r : Role} {t v c : w64} {es : List EntryM}
  {m : Msg} {to : w64} {M : List AntCheck.Msg} {ro : List Str} {ld : List LeaderRec} {ll : TermFn (List Entry)}
  {ch : List Entry} {tl : TermFn Int} {vi : SSet}

theorem ox_fm {x : OnDisk} (hx : odX S n id b r t v c es [msgOf m to] ro ld ll ch tl vi = x)
    (hs : m.ty ≠ .snap) : x.fm = .ok (afOf m to) := by
  subst hx
  show (do reqFactIn ll (← msgSeqHead [msgOf m to])) = _
  simp only [msgSeqHead, epure, eok_bind]
  unfold reqFactIn
  simp only [mo_typ, eok_bind, msgTypeStr_snap hs, Bool.false_eq_true, ite_false]
  rfl

theorem ox_f {x : OnDisk} (hx : odX S n id b r t v c es [msgOf m to] ro ld ll ch tl vi = x)
    (hs : m.ty ≠ .snap) (hr : (roleOf r == leader) = false) : x.f = .ok (afOf m to) := by
  unfold OnDisk.f
  rw [ox_leads hx, hr, eok_bind]
  exact ox_fm hx hs

theorem ox_last {x : OnDisk} (hx : odX S n id b r t v c es [msgOf m to] ro ld ll ch tl vi = x)
    (hs : m.ty ≠ .snap) (hr : (roleOf r == leader) = false) :
    x.last = .ok (uint.Z m.index + m.entries.length) := by
  unfold OnDisk.last
  rw [ox_f hx hs hr, eok_bind]
  simp only [afOf, logOf_length, epure]

theorem ox_k {x : OnDisk} (hx : odX S n id b r t v c es [msgOf m to] ro ld ll ch tl vi = x)
    (hs : m.ty ≠ .snap) (hr : (roleOf r == leader) = false) :
    x.k = .ok (firstOf es - uint.Z m.index) := by
  unfold OnDisk.k
  rw [ox_first hx, eok_bind, ox_f hx hs hr, eok_bind]
  rfl

theorem ox_ackAt {x : OnDisk} (hx : odX S n id b r t v c es [msgOf m to] ro ld ll ch tl vi = x)
    (hs : m.ty ≠ .snap) (hr : (roleOf r == leader) = false) :
    x.ackAt = .ok (uint.Z m.index + m.entries.length) := by
  unfold OnDisk.ackAt
  rw [ox_below hx, eok_bind]
  exact ox_last hx hs hr

/-- A follower's acks on a `MsgApp`: exactly when its commit moves (B 335-338). -/
theorem ox_acks_app {x : OnDisk} (hx : odX S n id b r t v c es [msgOf m to] ro ld ll ch tl vi = x)
    (hty : m.ty = .app) (hr : (roleOf r == leader) = false) :
    x.acks = .ok (uint.Z c != S.commitIndex[n]!) := by
  unfold OnDisk.acks
  rw [ox_stores hx, ox_leads hx, hr, ox_moved hx, ox_hasM hx, ox_m hx, ox_takes hx, ox_below hx]
  cases (uint.Z c != S.commitIndex[n]!) <;> cases ((logOf es).length != 0) <;>
    simp [AntCheck.andM, AntCheck.orM, AntCheck.notM, msgSeqHead, mo_typ, hty, msgTypeStr, epure,
      eok_bind, cons_bne_nil] <;> rfl

/-- A follower's acks on a heartbeat: none. -/
theorem ox_acks_hb {x : OnDisk} (hx : odX S n id b r t v c [] [msgOf m to] ro ld ll ch tl vi = x)
    (hty : m.ty = .heartbeat) (hr : (roleOf r == leader) = false) : x.acks = .ok false := by
  unfold OnDisk.acks
  rw [ox_stores hx, ox_leads hx, hr, ox_moved hx, ox_hasM hx, ox_m hx, ox_takes hx, ox_below hx]
  cases (uint.Z c != S.commitIndex[n]!) <;>
    simp [AntCheck.andM, AntCheck.orM, AntCheck.notM, msgSeqHead, mo_typ, hty, msgTypeStr, epure,
      eok_bind, cons_bne_nil, logOf] <;> rfl

/-- The log a follower's write leaves (B 328): the old log to just before `first`, then the
entries. -/
theorem ox_L1_cons {x : OnDisk} (hx : odX S n id b r t v c es M ro ld ll ch tl vi = x)
    (hne : es ≠ []) (h1 : 1 ≤ firstOf es) (h2 : firstOf es ≤ ((S.log[n]!).length : Int) + 1) :
    x.L1 = .ok ((S.log[n]!).take (firstOf es - 1).toNat ++ logOf es) := by
  unfold OnDisk.L1
  have hst : ((logOf es).length != 0) = true := by
    cases es with
    | nil => exact absurd rfl hne
    | cons e es => rfl
  rw [ox_stores hx, eok_bind, hst, if_pos rfl, ox_first hx, eok_bind, ox_L0 hx, ox_es hx]
  have := subSeq_nat (S.log[n]!) 0 (firstOf es - 1).toNat (by omega)
  have e1 : ((0 : Nat) : Int) + 1 = 1 := rfl
  have e2 : ((0 : Nat) : Int) + (((firstOf es - 1).toNat : Nat) : Int) = firstOf es - 1 := by omega
  rw [e1, e2, List.drop_zero] at this
  rw [this]; rfl

theorem uZ_toNat (c : w64) : (((uint.Z c).toNat : Nat) : Int) = uint.Z c := by
  have : 0 ≤ uint.Z c := by word
  omega

/-- The committed prefix of the new log (B 344). -/
theorem ox_newC {x : OnDisk} (hx : odX S n id b r t v c es M ro ld ll ch tl vi = x) {L1 : List Entry}
    (hL1 : x.L1 = .ok L1) (hc : uint.Z c ≤ L1.length) : x.newC = .ok (L1.take (uint.Z c).toNat) := by
  unfold OnDisk.newC
  rw [hL1, eok_bind, ox_w hx]
  have := subSeq_one L1 (uint.Z c).toNat (by omega)
  rw [uZ_toNat] at this
  simp only [ev_commit, need, eok_bind, epure]
  exact this

/-- `chain` after the write (B 345). -/
theorem ox_ch1 {x : OnDisk} (hx : odX S n id b r t v c es M ro ld ll ch tl vi = x) {L1 : List Entry}
    (hL1 : x.L1 = .ok L1) (hc : uint.Z c ≤ L1.length) :
    x.ch1 = .ok (if S.commitIndex[n]! < uint.Z c ∧ (ch.length : Int) < uint.Z c then
      L1.take (uint.Z c).toNat else ch) := by
  have hch : x.ch = ch := by subst hx; rfl
  unfold OnDisk.ch1
  rw [ox_adv hx, ox_newC hx hL1 hc, hch]
  have hl : ((L1.take (uint.Z c).toNat).length : Int) = uint.Z c := by
    rw [List.length_take]; have := uZ_toNat c; omega
  by_cases h1 : S.commitIndex[n]! < uint.Z c
  · by_cases h2 : (ch.length : Int) < uint.Z c
    · rw [if_pos ⟨h1, h2⟩]
      simp only [decide_eq_true (show uint.Z c > S.commitIndex[n]! from h1), andM_true, eok_bind,
        epure]
      rw [if_pos (by simp only [decide_eq_true_eq]; omega)]
    · rw [if_neg (fun h => h2 h.2)]
      simp only [decide_eq_true (show uint.Z c > S.commitIndex[n]! from h1), andM_true, eok_bind,
        epure]
      rw [if_neg (by simp only [decide_eq_true_eq]; omega)]
  · rw [if_neg (fun h => h1 h.1)]
    simp only [decide_eq_false (show ¬ uint.Z c > S.commitIndex[n]! from h1), andM_false, eok_bind,
      Bool.false_eq_true, ite_false, epure]

/-- A follower's confirmation index after a `MsgApp` that stores or commits (B 340-343): its
store's `last`, or, for a commit only, `last` raised at the term. -/
def fConfIdx (S : State) (n : Nat) (stores : Bool) (t : Int) (last : Int) : Int :=
  if stores then last else if (S.confirmed[n]!).term == t then imax (S.confirmed[n]!).index last else last

theorem ox_conf1_app {x : OnDisk} (hx : odX S n id b r t v c es [msgOf m to] ro ld ll ch tl vi = x)
    (hty : m.ty = .app) (hr : (roleOf r == leader) = false) :
    x.conf1 = .ok (if (((logOf es).length != 0) || (uint.Z c != S.commitIndex[n]!)) then
        { term := uint.Z t,
          index := fConfIdx S n ((logOf es).length != 0) (uint.Z t) (uint.Z m.index + m.entries.length) }
      else S.confirmed[n]!) := by
  have hs : m.ty ≠ .snap := by rw [hty]; decide
  have hc0 : x.s.confirmed[x.n]! = S.confirmed[n]! := by subst hx; rfl
  unfold OnDisk.conf1
  rw [ox_stores hx, eok_bind, ox_acks_app hx hty hr, ox_below hx, ox_T1 hx, ox_last hx hs hr, hc0]
  unfold fConfIdx
  generalize ((logOf es).length != 0) = sb
  generalize (uint.Z c != S.commitIndex[n]!) = mv
  cases sb <;> cases mv <;> simp [AntCheck.andM, AntCheck.notM, epure, eok_bind] <;> split <;> rfl

theorem tl_old_ok (tl : TermFn Int) (t : Int) :
    (if tl.has t then tl.get t else .ok 0) = (.ok (tlOld tl t) : EvalM Int) := by
  unfold tlOld TermFn.get TermFn.has
  cases h : tl.find? (fun p => p.1 == t) with
  | none =>
    have : tl.any (fun p => p.1 == t) = false := by
      rw [List.find?_eq_none] at h
      exact List.any_eq_false.mpr (fun p hp => by simpa using h p hp)
    rw [this]; rfl
  | some p =>
    have : tl.any (fun p => p.1 == t) = true :=
      List.any_eq_true.mpr ⟨p, List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩
    rw [this]; rfl

theorem ox_old' {x : OnDisk} (hx : odX S n id b r t v c es M ro ld ll ch tl vi = x) :
    x.old = .ok (tlOld tl (uint.Z t)) := by
  rw [ox_old hx]; exact tl_old_ok _ _

/-- LeaderCompleteness's check (B 426-428) passes. -/
theorem anyM_lc {ll : TermFn (List Entry)} {T : Int} {P : List Entry}
    (h : ∀ p ∈ ll, p.1 > T → isPrefix P p.2 = .ok true) :
    anyM ll (fun p => AntCheck.andM (Except.ok (decide (p.fst > T))) (AntCheck.notM (isPrefix P p.snd)))
      = .ok false := by
  induction ll with
  | nil => rfl
  | cons p ps ih =>
    unfold anyM
    have ih' := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    by_cases hp : p.1 > T
    · simp only [decide_eq_true hp, andM_true, h p (List.mem_cons_self ..) hp, notM_ok, Bool.not_true,
        eok_bind, Bool.false_eq_true, ite_false]
      exact ih'
    · simp only [decide_eq_false hp, andM_false, eok_bind, Bool.false_eq_true, ite_false]
      exact ih'

/-- LogMatching's check (B 430-432) passes. -/
theorem anyM_lm {N : Nat} {n : Nat} {L : List Entry} {logs : List (List Entry)}
    (h : ∀ b : Nat, matching L (logs[b]!) = .ok true) :
    anyM (List.range N) (fun b => AntCheck.andM (Except.ok (b != n)) (AntCheck.notM (matching L (logs[b]!))))
      = .ok false := by
  generalize List.range N = l
  induction l with
  | nil => rfl
  | cons p ps ih =>
    unfold anyM
    simp only [h p, notM_ok, od_andM_ok, Bool.not_true, Bool.and_false, eok_bind, Bool.false_eq_true,
      ite_false]
    exact ih

theorem isPrefix_take (L : List Entry) (k : Nat) : isPrefix (L.take k) L = .ok true := by
  unfold isPrefix
  have hk : (L.take k).length ≤ L.length := by simp; omega
  rw [if_pos hk, subSeq_one _ _ hk, eok_bind]
  have : L.take (L.take k).length = L.take k := by simp
  rw [this]; exact entriesEqual_self _

theorem take_len_c {L : List Entry} {c : w64} (h : uint.Z c ≤ L.length) :
    ((L.take (uint.Z c).toNat).length : Int) = uint.Z c := by
  rw [List.length_take]; have := uZ_toNat c; omega

theorem ox_conf1_hb {x : OnDisk} (hx : odX S n id b r t v c [] [msgOf m to] ro ld ll ch tl vi = x)
    (hty : m.ty = .heartbeat) (hr : (roleOf r == leader) = false) :
    x.conf1 = .ok (S.confirmed[n]!) := by
  have hc0 : x.s.confirmed[x.n]! = S.confirmed[n]! := by subst hx; rfl
  unfold OnDisk.conf1
  rw [ox_stores hx, eok_bind, ox_acks_hb hx hty hr, hc0]
  rfl

theorem fConfIdx_true (S : State) (n : Nat) (t last : Int) : fConfIdx S n true t last = last := rfl
theorem od_orM_ok (a b : Bool) : AntCheck.orM (.ok a) (.ok b) = .ok (a || b) := by cases a <;> rfl

theorem fConfIdx_ge (S : State) (n : Nat) (sb : Bool) (t last : Int) : last ≤ fConfIdx S n sb t last := by
  unfold fConfIdx imax; split
  · omega
  · split
    · split <;> omega
    · omega

/-- `SubSeq(chain', 1, c)` (B 434) is the new log's committed prefix, when `chain` agrees with it. -/
theorem subSeq_ch1 {L ch : List Entry} {c : w64} {P : Prop} [Decidable P] (hcL : uint.Z c ≤ L.length)
    (hch : uint.Z c ≤ ch.length → ch.take (uint.Z c).toNat = L.take (uint.Z c).toNat)
    (hnp : ¬ P → uint.Z c ≤ ch.length) :
    subSeq (if P ∧ (ch.length : Int) < uint.Z c then L.take (uint.Z c).toNat else ch) 1 (uint.Z c) =
      .ok (L.take (uint.Z c).toNat) := by
  have e := uZ_toNat c
  have e2 : (((uint.Z c).toNat : Nat) : Int).toNat = (uint.Z c).toNat := by omega
  split
  · rw [← e, subSeq_one _ _ (by rw [List.length_take]; omega), List.take_take, e2, Nat.min_self]
  · rename_i h
    have h1 : uint.Z c ≤ ch.length := by
      by_cases hp : P
      · exact Int.not_lt.mp (fun h' => h ⟨hp, h'⟩)
      · exact hnp hp
    rw [← e, subSeq_one _ _ (by omega), hch h1, e2]

/-- A leader's own request (B 318-326) for a write with nothing stored. -/
theorem ox_f_lnil {x : OnDisk} (hx : odX S n id b r t v c [] M ro ld ll ch tl vi = x)
    (hr : r = .leader) :
    x.f = .ok (AppendFact.mk (S.cfg.server[n]!) (S.cfg.server[n]!) (uint.Z t) 0 0 []
      (if (uint.Z c != S.commitIndex[n]!) then uint.Z c else 0)) := by
  subst hr
  have hme : x.s.cfg.server[x.n]! = S.cfg.server[n]! := by subst hx; rfl
  unfold OnDisk.f
  rw [ox_leads hx, eok_bind, hme]
  simp only [roleOf_beq_leader, decide_true, ite_true, ox_T1 hx, eok_bind, ox_es hx, ox_stores hx,
    ox_moved hx, epure, logOf_nil, List.length_nil, bne_self_eq_false, Bool.false_eq_true, ite_false,
    andM_false, ox_w hx, ev_commit, need]
  cases (uint.Z c != S.commitIndex[n]!) <;> rfl

/-- A leader's own request (B 318-326) for a write of `e :: es` at `first` (its log at its term
`lT`). -/
theorem ox_f_lcons {x : OnDisk} {e : EntryM} {es : List EntryM} {lT : List Entry}
    (hx : odX S n id b r t v c (e :: es) M ro ld ll ch tl vi = x) (hr : r = .leader)
    (hll : ll.get (uint.Z t) = .ok lT) :
    x.f = .ok (AppendFact.mk (S.cfg.server[n]!) (S.cfg.server[n]!) (uint.Z t) (uint.Z e.Index' - 1)
      (termAt lT (uint.Z e.Index' - 1)) (logOf (e :: es))
      (if (uint.Z c != S.commitIndex[n]!) then uint.Z c else 0)) := by
  subst hr
  have hme : x.s.cfg.server[x.n]! = S.cfg.server[n]! := by subst hx; rfl
  have hll' : x.ll = ll := by subst hx; rfl
  unfold OnDisk.f
  rw [ox_leads hx, eok_bind, hme, hll']
  simp only [roleOf_beq_leader, decide_true, ite_true, ox_T1 hx, eok_bind, ox_es hx, ox_stores hx,
    ox_moved hx, epure, ox_first hx, TermFn.has_of_get hll, hll, stores_cons, andM_true, ox_w hx,
    ev_commit, need, firstOf]
  cases (uint.Z c != S.commitIndex[n]!) <;> rfl


/-- The suffix of the log from `k` (an announced write's `suffix`, B 353). -/
theorem subSeq_suffix (L : List Entry) (k : Int) (h1 : 1 ≤ k) (h2 : k ≤ (L.length : Int) + 1) :
    subSeq L k L.length = .ok (L.drop (k - 1).toNat) := by
  by_cases hk : k = (L.length : Int) + 1
  · unfold subSeq
    rw [if_pos (by omega)]
    have : L.drop (k - 1).toNat = [] := List.drop_eq_nil_of_le (by omega)
    rw [this]; rfl
  · have := subSeq_nat L (k - 1).toNat (L.length - (k - 1).toNat) (by omega)
    have e1 : (((k - 1).toNat : Nat) : Int) + 1 = k := by omega
    have e2 : (((k - 1).toNat : Nat) : Int) + (((L.length - (k - 1).toNat : Nat)) : Int) = L.length := by omega
    rw [e1, e2] at this
    rw [this, List.take_of_length_le (by simp)]

/-- The request's entries from the first conflict `K` (B 386). -/
theorem subSeq_from {l : List EntryM} {K : Int} {es : List EntryM} (h1 : 1 ≤ K) (h2 : K ≤ l.length)
    (hes : es = l.drop (K - 1).toNat) : subSeq (logOf l) K l.length = .ok (logOf es) := by
  have := subSeq_suffix (logOf l) K h1 (by rw [logOf_length]; omega)
  rw [logOf_length] at this
  rw [this, hes]; unfold logOf; rw [List.map_drop]

theorem ox_acks_lnil {x : OnDisk} (hx : odX S n id b r t v c [] M ro ld ll ch tl vi = x) (hr : r = .leader) :
    x.acks = .ok false := by
  subst hr
  unfold OnDisk.acks
  rw [ox_stores hx, ox_leads hx, ox_takes hx, ox_below hx]
  simp only [logOf_nil, List.length_nil, bne_self_eq_false, andM_false, orM_false, roleOf_beq_leader,
    decide_true, notM_ok, Bool.not_true]
  rw [ox_moved hx]
  cases (uint.Z c != S.commitIndex[n]!) <;> rfl

theorem ox_conf1_lnil {x : OnDisk} (hx : odX S n id b r t v c [] M ro ld ll ch tl vi = x) (hr : r = .leader) :
    x.conf1 = .ok (S.confirmed[n]!) := by
  have hc0 : x.s.confirmed[x.n]! = S.confirmed[n]! := by subst hx; rfl
  unfold OnDisk.conf1
  rw [ox_stores hx, eok_bind, ox_acks_lnil hx hr, hc0]
  rfl

theorem ox_acks_lcons {x : OnDisk} {e : EntryM} {es : List EntryM}
    (hx : odX S n id b r t v c (e :: es) M ro ld ll ch tl vi = x) (hr : r = .leader) :
    x.acks = .ok true := by
  subst hr
  unfold OnDisk.acks
  rw [ox_stores hx, ox_leads hx]
  simp only [stores_cons, andM_true, roleOf_beq_leader, decide_true, orM_true]

theorem ox_last_lcons {x : OnDisk} {e : EntryM} {es : List EntryM} {lT : List Entry}
    (hx : odX S n id b r t v c (e :: es) M ro ld ll ch tl vi = x) (hr : r = .leader)
    (hll : ll.get (uint.Z t) = .ok lT) :
    x.last = .ok (uint.Z e.Index' - 1 + (es.length + 1 : Nat)) := by
  unfold OnDisk.last
  rw [ox_f_lcons hx hr hll, eok_bind]
  simp [logOf, epure]

theorem ox_ackAt_lcons {x : OnDisk} {e : EntryM} {es : List EntryM} {lT : List Entry}
    (hx : odX S n id b r t v c (e :: es) M ro ld ll ch tl vi = x) (hr : r = .leader)
    (hll : ll.get (uint.Z t) = .ok lT) :
    x.ackAt = .ok (uint.Z e.Index' - 1 + (es.length + 1 : Nat)) := by
  unfold OnDisk.ackAt
  rw [ox_below hx, eok_bind]
  exact ox_last_lcons hx hr hll

theorem ox_conf1_lcons {x : OnDisk} {e : EntryM} {es : List EntryM} {lT : List Entry}
    (hx : odX S n id b r t v c (e :: es) M ro ld ll ch tl vi = x) (hr : r = .leader)
    (hll : ll.get (uint.Z t) = .ok lT) :
    x.conf1 = .ok { term := uint.Z t, index := uint.Z e.Index' - 1 + (es.length + 1 : Nat) } := by
  unfold OnDisk.conf1
  rw [ox_stores hx, eok_bind]
  simp only [stores_cons, ite_true, ox_T1 hx, eok_bind, ox_last_lcons hx hr hll]
  rfl

end pieces2

section kinds
variable [GooseExts]

set_option hygiene false in
/-- `od_run` of `ReadyOD.lean`. -/
local syntax "od_run2" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

set_option hygiene false in
macro_rules
  | `(tactic| od_run2 [$hs,*]) => `(tactic|
    (rw [onDisk_eq, server_of hc n]
     generalize hX : (⟨_, _, _, false, _, _, _, _, _, _⟩ : OnDisk) = x
     unfold onDiskB
     simp (config := { zeta := false, decide := true }) only [$hs,*, ox_T1 hX, ox_T0 hX, ox_L0 hX,
       ox_snaps hX, ox_hasM hX, ox_m hX, ox_isApp hX, ox_below hX, ox_takes hX, ox_es hX, ox_first hX,
       ox_stores hX, ox_leads hX, ox_moved hX, ox_adv hX, ox_elect hX, ox_adopt hX, ox_V1 hX, ox_voted hX,
       ox_old' hX, ox_w hX, ev_vote, ev_commit, ev_term, ev_role, ev_snap, ev_entries, cand_leader,
       fol_leader, fol_cand, leader_cand, beq_self_str, roleOf_beq_leader, roleOf_beq_cand, reduceCtorEq,
       decide_true, decide_false, notM_ok, bne_self_eq_false, eok_bind, epure, server_of hc n, andM_true,
       andM_false, orM_true, orM_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_true,
       ite_false, Bool.true_and, Bool.and_true, Bool.false_and, Bool.and_false, Bool.or_false,
       Bool.false_or, logOf_nil, stores_cons, List.length_nil, fieldEq, need, msgSeqHead, mo_typ, mo_from, mo_to,
       mo_term, mo_index, mo_logTerm, mo_entries, mo_commit, mo_reject, mo_voteFact, msgTypeStr,
       cons_bne_nil, isReq, beq_self_eq_true, od_andM_ok, od_orM_ok, af_src, af_commit, af_prev, af_len]
     simp only [$hs,*, eok_bind, epure, entriesEqual_self, Bool.not_true, Bool.false_eq_true, ite_false,
       ite_true, andM_false, orM_false, Bool.false_or, Bool.or_false, andM_true, Bool.not_false,
       beq_self_eq_true, od_andM_ok, Bool.true_and, Bool.and_true, Bool.false_and, Bool.and_false,
       Bool.true_or, Bool.or_true, af_src, af_commit, af_prev, af_len, decide_true, decide_false, ite_self, od_orM_ok,
       fConfIdx_true]))

/-- **A follower's commit on a `MsgApp`, nothing stored** (`appAccept` with every entry already in
the log: `plogFindConflict` none), at the request's term (the node's, or adopted from it: a node
other than `n` is at it, `hj`): the commit `c` (above the old one, within the log, the request's
commit and its last index), the ack of the request's last index recorded and confirmed. The safety
checks' hypotheses: `chain` and the new committed prefix comparable (`hcs`), the latter in every
later leader log (`hlc`), `chain` agreeing with the log to `c` (`hch`). -/
theorem onDisk_fcommit {S : State} {R : RunCfg} (n : Fin R.N) (hc : S.cfg = R.cfg) (t v c : w64) (m : Msg)
    (ro : List Str) (ld : List LeaderRec) (ll : TermFn (List Entry)) (ch : List Entry)
    (tl : TermFn Int) (vi : SSet)
    (hty : m.ty = .app) (hmt : m.term = t)
    (hge : S.currentTerm[n.val]! ≤ uint.Z t)
    (hj : ∃ j : Fin R.N, j ≠ n ∧ uint.Z t ≤ S.currentTerm[j.val]!)
    (hv : (nameOf v != (if uint.Z t != S.currentTerm[n.val]! then [] else S.vote n.val)) = false)
    (hro : ro[n.val]! = follower)
    (hsend : sendableIn ld ll ch tl (afOf m (nodeId n)) = .ok true)
    (hcm : S.commitIndex[n.val]! < uint.Z c) (hcL : uint.Z c ≤ (S.log[n.val]!).length)
    (hcc : uint.Z c ≤ uint.Z m.commit) (hcl : uint.Z c ≤ uint.Z m.index + m.entries.length)
    (hprev : S.prevOk n.val (afOf m (nodeId n)) = .ok true)
    (hfirst : S.hasFirst n.val (afOf m (nodeId n)) (m.entries.length : Int) = .ok true)
    (hcs : comparable ch ((S.log[n.val]!).take (uint.Z c).toNat) = .ok true)
    (hlc : ∀ p ∈ ll, p.1 > uint.Z t → isPrefix ((S.log[n.val]!).take (uint.Z c).toNat) p.2 = .ok true)
    (hch : uint.Z c ≤ ch.length → ch.take (uint.Z c).toNat = (S.log[n.val]!).take (uint.Z c).toNat) :
    ∃ p : Pre, PreOk S n.val (S.log[n.val]!) p ∧
      S.onDisk n.val ⟨evReady (nodeId n) go!"recv" (roleOf .follower) t v c [], [msgOf m (nodeId n)]⟩ false ro ld
          ll ch tl vi
        = .ok (some (odS S n.val (uint.Z t) none (S.log[n.val]!) (uint.Z c) ro
            { term := uint.Z t, index := fConfIdx S n.val false (uint.Z t) (uint.Z m.index + m.entries.length) }
            (lset.add S.msgs (ackFact (nameOf (nodeId n)) (nameOf m.src) (uint.Z t)
              (uint.Z m.index + m.entries.length)))
            S.votes ld ll p
            (if S.commitIndex[n.val]! < uint.Z c ∧ (ch.length : Int) < uint.Z c then
              (S.log[n.val]!).take (uint.Z c).toNat else ch)
            (tl.with (uint.Z t) (imax (tlOld tl (uint.Z t)) (uint.Z c))) vi)) := by
  subst hmt
  obtain ⟨j, hj, htj⟩ := hj
  have hs : m.ty ≠ .snap := by rw [hty]; decide
  have hr : (roleOf .follower == leader) = false := by decide
  have hcm' : (uint.Z c != S.commitIndex[n.val]!) = true := by rw [bne_iff_ne]; omega
  have hadv : decide (uint.Z c > S.commitIndex[n.val]!) = true := decide_eq_true (by omega)
  have hge' : decide (uint.Z m.term ≥ S.currentTerm[n.val]!) = true := decide_eq_true (by omega)
  have hcL' : decide (uint.Z c ≤ ((S.log[n.val]!).length : Int)) = true := decide_eq_true hcL
  have hcc' : decide (uint.Z c ≤ uint.Z m.commit) = true := decide_eq_true hcc
  have hcb : decide (uint.Z c > fConfIdx S n.val false (uint.Z m.term) (uint.Z m.index + m.entries.length))
      = false := by
    have := fConfIdx_ge S n.val false (uint.Z m.term) (uint.Z m.index + m.entries.length)
    exact decide_eq_false (by omega)
  have hany : ((List.range (List.length S.cfg.server)).any fun k =>
      k != n.val && decide (S.currentTerm[k]! ≥ uint.Z m.term)) = true := by
    rw [List.any_eq_true]
    refine ⟨j.val, ?_, ?_⟩
    · rw [List.mem_range, server_length hc]; exact j.isLt
    · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
      exact ⟨fun h => hj (Fin.ext h), htj⟩
  have hsub := subSeq_ch1 (P := S.commitIndex[n.val]! < uint.Z c) hcL hch (fun h => absurd hcm h)
  od_run2 [ox_L1_nil hX, ox_fm hX hs, ox_f hX hs hr, ox_acks_app hX hty hr, ox_conf1_app hX hty hr,
    ox_ackAt hX hs hr, ox_ch1 hX (ox_L1_nil hX) hcL, ox_newC hX (ox_L1_nil hX) hcL, hcm', hadv, hge', hcL',
    hcc', hv, hro, hty, hany, hsend, hprev, hfirst, snapOk_msgOf _ _ _ hs, hcs, anyM_lc hlc, hsub,
    isPrefix_take, hcb, take_len_c hcL, hcc]
  exact ⟨_, ⟨rfl, rfl, rfl, rfl, rfl, by simp⟩, rfl⟩

/-- The announced write's log of a store at `k + 1` (`keep = k`, the suffix from there). -/
theorem pre_store_log (L0 X : List Entry) (k : Nat) (hk : k ≤ L0.length) :
    (L0.take k ++ X).take k ++ L0.drop k = L0 := by
  rw [List.take_append_of_le_length (by simp [hk]), List.take_take, Nat.min_self, List.take_append_drop]

/-- **A follower's store on a `MsgApp`** (`appAccept` with a conflict or new entries:
`plogMaybeAppend` appends the request's entries from the first conflict `K`), with its commit
moved or not, at the request's term (the node's, or adopted). The report's entries `e :: es'`
start at `first = e.Index'`, `K = first - m.index` (`hK1`, `hK2`); the request's entries before
`K` are in the log (`hhf`), those from `K` are the report's (`hes`); `first` conflicts with the log
or is just past its end (`hcf`, `hlen`). `L1` is the log after the write. -/
theorem onDisk_fstore {S : State} {R : RunCfg} (n : Fin R.N) (hc : S.cfg = R.cfg) (t v c : w64) (m : Msg)
    (e : EntryM) (es' : List EntryM)
    (ro : List Str) (ld : List LeaderRec) (ll : TermFn (List Entry)) (ch : List Entry)
    (tl : TermFn Int) (vi : SSet) (eqb : Bool)
    (hty : m.ty = .app) (hmt : m.term = t)
    (hge : S.currentTerm[n.val]! ≤ uint.Z t)
    (hj : ∃ j : Fin R.N, j ≠ n ∧ uint.Z t ≤ S.currentTerm[j.val]!)
    (hv : (nameOf v != (if uint.Z t != S.currentTerm[n.val]! then [] else S.vote n.val)) = false)
    (hro : ro[n.val]! = follower)
    (hsend : sendableIn ld ll ch tl (afOf m (nodeId n)) = .ok true)
    (hprev : S.prevOk n.val (afOf m (nodeId n)) = .ok true)
    (hK1 : 1 ≤ uint.Z e.Index' - uint.Z m.index) (hK2 : uint.Z e.Index' - uint.Z m.index ≤ m.entries.length)
    (hhf : S.hasFirst n.val (afOf m (nodeId n)) (uint.Z e.Index' - uint.Z m.index - 1) = .ok true)
    (hes : e :: es' = m.entries.drop (uint.Z e.Index' - uint.Z m.index - 1).toNat)
    (hcf : uint.Z e.Index' ≤ (S.log[n.val]!).length →
      ((S.log[n.val]!)[(uint.Z e.Index' - 1).toNat]!).term ≠ uint.Z e.Term')
    (hlen : (S.log[n.val]!).length < uint.Z e.Index' → uint.Z e.Index' = (S.log[n.val]!).length + 1)
    (hcm : S.commitIndex[n.val]! ≤ uint.Z c)
    (hcL : uint.Z c ≤ ((S.log[n.val]!).take (uint.Z e.Index' - 1).toNat ++ logOf (e :: es')).length)
    (hcc : S.commitIndex[n.val]! < uint.Z c → uint.Z c ≤ uint.Z m.commit) (hcl : uint.Z c ≤ uint.Z m.index + m.entries.length)
    (hee : entriesEqual ((S.log[n.val]!).take (uint.Z e.Index' - 1).toNat ++ logOf (e :: es'))
      (S.log[n.val]!) = .ok eqb)
    (hlm : ∀ b : Nat, matching ((S.log[n.val]!).take (uint.Z e.Index' - 1).toNat ++ logOf (e :: es'))
      (S.log[b]!) = .ok true)
    (hcs : comparable ch (((S.log[n.val]!).take (uint.Z e.Index' - 1).toNat ++ logOf (e :: es')).take
      (uint.Z c).toNat) = .ok true)
    (hlc : ∀ p ∈ ll, p.1 > uint.Z t → isPrefix (((S.log[n.val]!).take (uint.Z e.Index' - 1).toNat ++
      logOf (e :: es')).take (uint.Z c).toNat) p.2 = .ok true)
    (hch : uint.Z c ≤ ch.length → ch.take (uint.Z c).toNat =
      ((S.log[n.val]!).take (uint.Z e.Index' - 1).toNat ++ logOf (e :: es')).take (uint.Z c).toNat)
    (hcch : uint.Z c = S.commitIndex[n.val]! → uint.Z c ≤ ch.length) :
    ∃ p : Pre, PreOk S n.val ((S.log[n.val]!).take (uint.Z e.Index' - 1).toNat ++ logOf (e :: es')) p ∧
      S.onDisk n.val ⟨evReady (nodeId n) go!"recv" (roleOf .follower) t v c (e :: es'), [msgOf m (nodeId n)]⟩ false
          ro ld ll ch tl vi
        = .ok (some (odS S n.val (uint.Z t) none
            ((S.log[n.val]!).take (uint.Z e.Index' - 1).toNat ++ logOf (e :: es')) (uint.Z c) ro
            { term := uint.Z t, index := uint.Z m.index + m.entries.length }
            (if S.commitIndex[n.val]! < uint.Z c then
              lset.add S.msgs (ackFact (nameOf (nodeId n)) (nameOf m.src) (uint.Z t)
                (uint.Z m.index + m.entries.length)) else S.msgs)
            S.votes ld ll p
            (if S.commitIndex[n.val]! < uint.Z c ∧ (ch.length : Int) < uint.Z c then
              ((S.log[n.val]!).take (uint.Z e.Index' - 1).toNat ++ logOf (e :: es')).take (uint.Z c).toNat
             else ch)
            (if S.commitIndex[n.val]! < uint.Z c then tl.with (uint.Z t) (imax (tlOld tl (uint.Z t)) (uint.Z c))
             else tl) vi)) := by
  subst hmt
  obtain ⟨j, hj, htj⟩ := hj
  have hs : m.ty ≠ .snap := by rw [hty]; decide
  have hr : (roleOf .follower == leader) = false := by decide
  have hm0 : 0 ≤ uint.Z m.index := by word
  have hge' : decide (uint.Z m.term ≥ S.currentTerm[n.val]!) = true := decide_eq_true (by omega)
  have hany : ((List.range (List.length S.cfg.server)).any fun k =>
      k != n.val && decide (S.currentTerm[k]! ≥ uint.Z m.term)) = true := by
    rw [List.any_eq_true]
    refine ⟨j.val, ?_, ?_⟩
    · rw [List.mem_range, server_length hc]; exact j.isLt
    · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
      exact ⟨fun h => hj (Fin.ext h), htj⟩
  have hf1 : 1 ≤ firstOf (e :: es') := by show 1 ≤ uint.Z e.Index'; omega
  have hf2 : firstOf (e :: es') ≤ ((S.log[n.val]!).length : Int) + 1 := by
    show uint.Z e.Index' ≤ _; by_cases h : ((S.log[n.val]!).length : Int) < uint.Z e.Index'
    · have := hlen h; omega
    · omega
  have hL1 := fun {x : OnDisk} (hx : odX S n.val (nodeId n) go!"recv" .follower m.term v c (e :: es')
      [msgOf m (nodeId n)] ro ld ll ch tl vi = x) => ox_L1_cons hx (List.cons_ne_nil e es') hf1 hf2
  have hfo : firstOf (e :: es') = uint.Z e.Index' := rfl
  rw [hfo] at hf1 hf2 hL1
  have hsubE : subSeq (afOf m (nodeId n)).entries (uint.Z e.Index' - uint.Z m.index) (m.entries.length)
      = .ok (logOf (e :: es')) := subSeq_from hK1 hK2 hes
  have hsuf := subSeq_suffix (S.log[n.val]!) _ hf1 hf2
  have hK1' : decide (1 ≤ uint.Z e.Index' - uint.Z m.index) = true := decide_eq_true hK1
  have hK2' : decide (uint.Z e.Index' - uint.Z m.index ≤ (m.entries.length : Int)) = true :=
    decide_eq_true hK2
  have he1 : atE (logOf (e :: es')) 1 = .ok (entOf e) := rfl
  have hcb : decide (uint.Z c > fConfIdx S n.val true (uint.Z m.term) (uint.Z m.index + m.entries.length))
      = false := decide_eq_false (by unfold fConfIdx; simp only [ite_true]; omega)
  have hcL' : decide (uint.Z c ≤
      (((S.log[n.val]!).take (uint.Z e.Index' - 1).toNat ++ logOf (e :: es')).length : Int)) = true :=
    decide_eq_true hcL
  have hne1 : ¬ uint.Z e.Index' ≤ ((S.log[n.val]!).length : Int) →
      (uint.Z e.Index' != ((S.log[n.val]!).length : Int) + 1) = false := by
    intro h; rw [hlen (by omega)]; exact bne_self_eq_false _
  have hneq : uint.Z e.Index' ≤ ((S.log[n.val]!).length : Int) →
      ((S.log[n.val]!)[(uint.Z e.Index' - 1).toNat]!.term == (entOf e).term) = false := by
    intro hfl; rw [entOf_term]; simpa using hcf hfl
  rcases Int.lt_or_eq_of_le hcm with hlt | heq
  · have hcm' : (uint.Z c != S.commitIndex[n.val]!) = true := by rw [bne_iff_ne]; omega
    have hadv : decide (uint.Z c > S.commitIndex[n.val]!) = true := decide_eq_true (by omega)
    have hsub := subSeq_ch1 (P := S.commitIndex[n.val]! < uint.Z c) hcL hch (fun h => absurd hlt h)
    rw [if_pos hlt, if_pos hlt]
    by_cases hfl : uint.Z e.Index' ≤ ((S.log[n.val]!).length : Int)
    · have hat := atE_ok (l := S.log[n.val]!) hf1 hfl
      od_run2 [hL1 hX, ox_fm hX hs, ox_f hX hs hr, ox_acks_app hX hty hr, ox_conf1_app hX hty hr,
        ox_k hX hs hr, ox_ackAt hX hs hr, ox_ch1 hX (hL1 hX) hcL, ox_newC hX (hL1 hX) hcL, hcm', hadv,
        hge', hv, hro, hty, hany, hsend, hprev, hhf, snapOk_msgOf _ _ _ hs, hcs, anyM_lc hlc, hsub,
        isPrefix_take, hcb, take_len_c hcL, hcc hlt, hsubE, hsuf, hK1', hK2', he1, hat, hneq hfl, hfl, hee,
        anyM_lm hlm, hcL', firstOf]
      exact ⟨_, ⟨rfl, rfl, rfl, rfl, rfl, pre_store_log _ _ _ (by simp only; omega)⟩, rfl⟩
    · od_run2 [hL1 hX, ox_fm hX hs, ox_f hX hs hr, ox_acks_app hX hty hr, ox_conf1_app hX hty hr,
        ox_k hX hs hr, ox_ackAt hX hs hr, ox_ch1 hX (hL1 hX) hcL, ox_newC hX (hL1 hX) hcL, hcm', hadv,
        hge', hv, hro, hty, hany, hsend, hprev, hhf, snapOk_msgOf _ _ _ hs, hcs, anyM_lc hlc, hsub,
        isPrefix_take, hcb, take_len_c hcL, hcc hlt, hsubE, hsuf, hK1', hK2', he1, hne1 hfl, hfl, hee,
        anyM_lm hlm, hcL', firstOf]
      exact ⟨_, ⟨rfl, rfl, rfl, rfl, rfl, pre_store_log _ _ _ (by simp only; omega)⟩, rfl⟩
  · have hcm' : (uint.Z c != S.commitIndex[n.val]!) = false := by rw [heq]; exact bne_self_eq_false _
    have hadv : decide (uint.Z c > S.commitIndex[n.val]!) = false := decide_eq_false (by omega)
    have hnlt : ¬ S.commitIndex[n.val]! < uint.Z c := by omega
    have hsub0 : subSeq ch 1 (uint.Z c) =
        .ok (((S.log[n.val]!).take (uint.Z e.Index' - 1).toNat ++ logOf (e :: es')).take (uint.Z c).toNat) := by
      have h1 := hcch heq.symm
      rw [← uZ_toNat c, subSeq_one _ _ (by omega), uZ_toNat c, hch h1]
    rw [if_neg hnlt, if_neg hnlt, if_neg (fun h => hnlt h.1)]
    by_cases hfl : uint.Z e.Index' ≤ ((S.log[n.val]!).length : Int)
    · have hat := atE_ok (l := S.log[n.val]!) hf1 hfl
      od_run2 [hL1 hX, ox_fm hX hs, ox_f hX hs hr, ox_acks_app hX hty hr, ox_conf1_app hX hty hr,
        ox_k hX hs hr, ox_ackAt hX hs hr, ox_ch1_noadv hX hadv, hcm', hadv,
        hge', hv, hro, hty, hany, hsend, hprev, hhf, snapOk_msgOf _ _ _ hs, hsub0,
        isPrefix_take, hsubE, hsuf, hK1', hK2', he1, hat, hneq hfl, hfl, hee,
        anyM_lm hlm, firstOf]
      exact ⟨_, ⟨rfl, rfl, rfl, rfl, rfl, pre_store_log _ _ _ (by simp only; omega)⟩, rfl⟩
    · od_run2 [hL1 hX, ox_fm hX hs, ox_f hX hs hr, ox_acks_app hX hty hr, ox_conf1_app hX hty hr,
        ox_k hX hs hr, ox_ackAt hX hs hr, ox_ch1_noadv hX hadv, hcm', hadv,
        hge', hv, hro, hty, hany, hsend, hprev, hhf, snapOk_msgOf _ _ _ hs, hsub0,
        isPrefix_take, hsubE, hsuf, hK1', hK2', he1, hne1 hfl, hfl, hee,
        anyM_lm hlm, firstOf]
      exact ⟨_, ⟨rfl, rfl, rfl, rfl, rfl, pre_store_log _ _ _ (by simp only; omega)⟩, rfl⟩

/-- **A follower's commit on a heartbeat** (`handleHeartbeat`'s `commitTo(m.Commit)`), at the
heartbeat's term (the node's, or adopted): nothing recorded; `CommitBeyondConfirmed` (B 435) passes
since the node's confirmation is at the term and covers the commit (`hcbc`, what `HbCommitOk` gives
when the commit moves). -/
theorem onDisk_fhb {S : State} {R : RunCfg} (n : Fin R.N) (hc : S.cfg = R.cfg) (t v c : w64) (m : Msg)
    (ro : List Str) (ld : List LeaderRec) (ll : TermFn (List Entry)) (ch : List Entry)
    (tl : TermFn Int) (vi : SSet)
    (hty : m.ty = .heartbeat) (hmt : m.term = t)
    (hge : S.currentTerm[n.val]! ≤ uint.Z t)
    (hj : ∃ j : Fin R.N, j ≠ n ∧ uint.Z t ≤ S.currentTerm[j.val]!)
    (hv : (nameOf v != (if uint.Z t != S.currentTerm[n.val]! then [] else S.vote n.val)) = false)
    (hro : ro[n.val]! = follower)
    (hsend : sendableIn ld ll ch tl (afOf m (nodeId n)) = .ok true)
    (hcm : S.commitIndex[n.val]! < uint.Z c) (hcL : uint.Z c ≤ (S.log[n.val]!).length)
    (hcc : uint.Z c ≤ uint.Z m.commit)
    (hcbc : (S.confirmed[n.val]!).term = uint.Z t ∧ uint.Z c ≤ (S.confirmed[n.val]!).index)
    (hcs : comparable ch ((S.log[n.val]!).take (uint.Z c).toNat) = .ok true)
    (hlc : ∀ p ∈ ll, p.1 > uint.Z t → isPrefix ((S.log[n.val]!).take (uint.Z c).toNat) p.2 = .ok true)
    (hch : uint.Z c ≤ ch.length → ch.take (uint.Z c).toNat = (S.log[n.val]!).take (uint.Z c).toNat) :
    ∃ p : Pre, PreOk S n.val (S.log[n.val]!) p ∧
      S.onDisk n.val ⟨evReady (nodeId n) go!"recv" (roleOf .follower) t v c [], [msgOf m (nodeId n)]⟩ false ro ld
          ll ch tl vi
        = .ok (some (odS S n.val (uint.Z t) none (S.log[n.val]!) (uint.Z c) ro (S.confirmed[n.val]!)
            S.msgs S.votes ld ll p
            (if S.commitIndex[n.val]! < uint.Z c ∧ (ch.length : Int) < uint.Z c then
              (S.log[n.val]!).take (uint.Z c).toNat else ch)
            (tl.with (uint.Z t) (imax (tlOld tl (uint.Z t)) (uint.Z c))) vi)) := by
  subst hmt
  obtain ⟨j, hj, htj⟩ := hj
  have hs : m.ty ≠ .snap := by rw [hty]; decide
  have hr : (roleOf .follower == leader) = false := by decide
  have hcm' : (uint.Z c != S.commitIndex[n.val]!) = true := by rw [bne_iff_ne]; omega
  have hadv : decide (uint.Z c > S.commitIndex[n.val]!) = true := decide_eq_true (by omega)
  have hge' : decide (uint.Z m.term ≥ S.currentTerm[n.val]!) = true := decide_eq_true (by omega)
  have hcL' : decide (uint.Z c ≤ ((S.log[n.val]!).length : Int)) = true := decide_eq_true hcL
  have hcb1 : ((S.confirmed[n.val]!).term != uint.Z m.term) = false := by
    rw [hcbc.1]; exact bne_self_eq_false _
  have hcb2 : decide (uint.Z c > (S.confirmed[n.val]!).index) = false := decide_eq_false (by omega)
  have hany : ((List.range (List.length S.cfg.server)).any fun k =>
      k != n.val && decide (S.currentTerm[k]! ≥ uint.Z m.term)) = true := by
    rw [List.any_eq_true]
    refine ⟨j.val, ?_, ?_⟩
    · rw [List.mem_range, server_length hc]; exact j.isLt
    · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
      exact ⟨fun h => hj (Fin.ext h), htj⟩
  have hsub := subSeq_ch1 (P := S.commitIndex[n.val]! < uint.Z c) hcL hch (fun h => absurd hcm h)
  od_run2 [ox_L1_nil hX, ox_fm hX hs, ox_f hX hs hr, ox_acks_hb hX hty hr, ox_conf1_hb hX hty hr,
    ox_ch1 hX (ox_L1_nil hX) hcL, ox_newC hX (ox_L1_nil hX) hcL, hcm', hadv, hge', hcL',
    hv, hro, hty, hany, hsend, snapOk_msgOf _ _ _ hs, hcs, anyM_lc hlc, hsub,
    isPrefix_take, hcb1, hcb2, take_len_c hcL, hcc]
  exact ⟨_, ⟨rfl, rfl, rfl, rfl, rfl, by simp⟩, rfl⟩

/-- **A leader's commit, nothing stored** (`AppRespEnd`'s `maybeCommit`, or a drain's later
`Ready` after `Advance` stepped the leader's self-acknowledgement): its own request with the commit
`Sendable` (`hsend`: in `InMemory`'s `chain`/`termLen`, `RecordedIn`), its confirmation at its term
covering the commit (`hcbc`, `LeaderConfOk`). -/
theorem onDisk_lcommit {S : State} {R : RunCfg} (n : Fin R.N) (hc : S.cfg = R.cfg) (b : Str) (t v c : w64)
    (M : List AntCheck.Msg) (ro : List Str) (ld : List LeaderRec) (ll : TermFn (List Entry))
    (ch : List Entry) (tl : TermFn Int) (vi : SSet)
    (ht : uint.Z t = S.currentTerm[n.val]!) (hv : nameOf v = S.vote n.val) (hro : ro[n.val]! = leader)
    (hsend : sendableIn ld ll ch tl (AppendFact.mk (nameOf (nodeId n)) (nameOf (nodeId n)) (uint.Z t) 0 0 []
      (uint.Z c)) = .ok true)
    (hcm : S.commitIndex[n.val]! < uint.Z c) (hcL : uint.Z c ≤ (S.log[n.val]!).length)
    (hcbc : (S.confirmed[n.val]!).term = uint.Z t ∧ uint.Z c ≤ (S.confirmed[n.val]!).index)
    (hcs : comparable ch ((S.log[n.val]!).take (uint.Z c).toNat) = .ok true)
    (hlc : ∀ p ∈ ll, p.1 > uint.Z t → isPrefix ((S.log[n.val]!).take (uint.Z c).toNat) p.2 = .ok true)
    (hch : uint.Z c ≤ ch.length → ch.take (uint.Z c).toNat = (S.log[n.val]!).take (uint.Z c).toNat) :
    ∃ p : Pre, PreOk S n.val (S.log[n.val]!) p ∧
      S.onDisk n.val ⟨evReady (nodeId n) b (roleOf .leader) t v c [], M⟩ false ro ld ll ch tl vi
        = .ok (some (odS S n.val (uint.Z t) none (S.log[n.val]!) (uint.Z c) ro (S.confirmed[n.val]!)
            S.msgs S.votes ld ll p
            (if S.commitIndex[n.val]! < uint.Z c ∧ (ch.length : Int) < uint.Z c then
              (S.log[n.val]!).take (uint.Z c).toNat else ch)
            (tl.with (uint.Z t) (imax (tlOld tl (uint.Z t)) (uint.Z c))) vi)) := by
  have hne : (uint.Z t != S.currentTerm[n.val]!) = false := by rw [ht]; exact bne_self_eq_false _
  have hge : decide (uint.Z t ≥ S.currentTerm[n.val]!) = true := decide_eq_true (by omega)
  have hv' : (nameOf v != S.vote n.val) = false := by rw [hv]; exact bne_self_eq_false _
  have hst : (uint.Z t == S.currentTerm[n.val]!) = true := by rw [ht]; exact beq_self_eq_true _
  have hcm' : (uint.Z c != S.commitIndex[n.val]!) = true := by rw [bne_iff_ne]; omega
  have hadv : decide (uint.Z c > S.commitIndex[n.val]!) = true := decide_eq_true (by omega)
  have hcL' : decide (uint.Z c ≤ ((S.log[n.val]!).length : Int)) = true := decide_eq_true hcL
  have hcb1 : ((S.confirmed[n.val]!).term != uint.Z t) = false := by
    rw [hcbc.1]; exact bne_self_eq_false _
  have hcb2 : decide (uint.Z c > (S.confirmed[n.val]!).index) = false := decide_eq_false (by omega)
  have hsub := subSeq_ch1 (P := S.commitIndex[n.val]! < uint.Z c) hcL hch (fun h => absurd hcm h)
  od_run2 [ox_L1_nil hX, ox_f_lnil hX rfl, ox_acks_lnil hX rfl, ox_conf1_lnil hX rfl,
    ox_ch1 hX (ox_L1_nil hX) hcL, ox_newC hX (ox_L1_nil hX) hcL, hne, hge, hv', hst, hcm', hadv, hcL',
    hro, hsend, hcs, anyM_lc hlc, hsub, isPrefix_take, hcb1, hcb2, take_len_c hcL]
  exact ⟨_, ⟨rfl, rfl, rfl, rfl, rfl, by simp⟩, rfl⟩

/-- **A leader's store** (`WinEnd`'s empty entry, `ProposeEnd`'s proposal: `appendEntry` at the
log's end), its commit unchanged: its own request `Sendable` from its leader log `lT` at its term
(`hll`, `hsend`: `InMemory`'s `ledLog`, which has the entries appended), its acknowledgement of
its new last index recorded and confirmed. -/
theorem onDisk_lstore {S : State} {R : RunCfg} (n : Fin R.N) (hc : S.cfg = R.cfg) (b : Str) (t v c : w64)
    (e : EntryM) (es' : List EntryM)
    (M : List AntCheck.Msg) (ro : List Str) (ld : List LeaderRec) (ll : TermFn (List Entry))
    (ch : List Entry) (tl : TermFn Int) (vi : SSet) (lT : List Entry) (eqb : Bool)
    (ht : uint.Z t = S.currentTerm[n.val]!) (hv : nameOf v = S.vote n.val) (hro : ro[n.val]! = leader)
    (hfirst : uint.Z e.Index' = ((S.log[n.val]!).length : Int) + 1)
    (hll : ll.get (uint.Z t) = .ok lT)
    (hsend : sendableIn ld ll ch tl (AppendFact.mk (nameOf (nodeId n)) (nameOf (nodeId n)) (uint.Z t)
      (uint.Z e.Index' - 1) (termAt lT (uint.Z e.Index' - 1)) (logOf (e :: es')) 0) = .ok true)
    (hcm : uint.Z c = S.commitIndex[n.val]!)
    (hee : entriesEqual ((S.log[n.val]!).take (uint.Z e.Index' - 1).toNat ++ logOf (e :: es'))
      (S.log[n.val]!) = .ok eqb)
    (hlm : ∀ b : Nat, matching ((S.log[n.val]!).take (uint.Z e.Index' - 1).toNat ++ logOf (e :: es'))
      (S.log[b]!) = .ok true)
    (hcch : uint.Z c ≤ ch.length)
    (hch : ch.take (uint.Z c).toNat =
      ((S.log[n.val]!).take (uint.Z e.Index' - 1).toNat ++ logOf (e :: es')).take (uint.Z c).toNat) :
    ∃ p : Pre, PreOk S n.val ((S.log[n.val]!).take (uint.Z e.Index' - 1).toNat ++ logOf (e :: es')) p ∧
      S.onDisk n.val ⟨evReady (nodeId n) b (roleOf .leader) t v c (e :: es'), M⟩ false ro ld ll ch tl vi
        = .ok (some (odS S n.val (uint.Z t) none
            ((S.log[n.val]!).take (uint.Z e.Index' - 1).toNat ++ logOf (e :: es')) (uint.Z c) ro
            { term := uint.Z t, index := uint.Z e.Index' - 1 + (es'.length + 1 : Nat) }
            (lset.add S.msgs (ackFact (nameOf (nodeId n)) (nameOf (nodeId n)) (uint.Z t)
              (uint.Z e.Index' - 1 + (es'.length + 1 : Nat))))
            S.votes ld ll p ch tl vi)) := by
  have hne : (uint.Z t != S.currentTerm[n.val]!) = false := by rw [ht]; exact bne_self_eq_false _
  have hge : decide (uint.Z t ≥ S.currentTerm[n.val]!) = true := decide_eq_true (by omega)
  have hv' : (nameOf v != S.vote n.val) = false := by rw [hv]; exact bne_self_eq_false _
  have hst : (uint.Z t == S.currentTerm[n.val]!) = true := by rw [ht]; exact beq_self_eq_true _
  have hcm' : (uint.Z c != S.commitIndex[n.val]!) = false := by rw [hcm]; exact bne_self_eq_false _
  have hadv : decide (uint.Z c > S.commitIndex[n.val]!) = false := decide_eq_false (by omega)
  have hfo : firstOf (e :: es') = uint.Z e.Index' := rfl
  have hf1 : 1 ≤ firstOf (e :: es') := by rw [hfo]; omega
  have hf2 : firstOf (e :: es') ≤ ((S.log[n.val]!).length : Int) + 1 := by rw [hfo]; omega
  have hfe : (uint.Z e.Index' == ((S.log[n.val]!).length : Int) + 1) = true := by
    rw [hfirst]; exact beq_self_eq_true _
  have hL1 := fun {x : OnDisk} (hx : odX S n.val (nodeId n) b .leader t v c (e :: es') M ro ld ll ch tl vi = x) =>
    ox_L1_cons hx (List.cons_ne_nil e es') hf1 hf2
  rw [hfo] at hL1
  have hsuf := subSeq_suffix (S.log[n.val]!) _ hf1 hf2
  rw [hfo] at hsuf
  have hsub0 : subSeq ch 1 (uint.Z c) =
      .ok (((S.log[n.val]!).take (uint.Z e.Index' - 1).toNat ++ logOf (e :: es')).take (uint.Z c).toNat) := by
    rw [← uZ_toNat c, subSeq_one _ _ (by omega), uZ_toNat c, hch]
  od_run2 [hL1 hX, ox_f_lcons hX rfl hll, ox_acks_lcons hX rfl, ox_conf1_lcons hX rfl hll,
    ox_ackAt_lcons hX rfl hll, ox_ch1_noadv hX hadv, hne, hge, hv', hst, hcm', hadv, hro, hsend, hfe,
    hsuf, hsub0, isPrefix_take, hee, anyM_lm hlm, firstOf]
  exact ⟨_, ⟨rfl, rfl, rfl, rfl, rfl, pre_store_log _ _ _ (by simp only; omega)⟩, rfl⟩

end kinds

end AntSim
end EtcdGrove
end Perennial
