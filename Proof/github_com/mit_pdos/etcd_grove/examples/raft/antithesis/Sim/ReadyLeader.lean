/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: `InMemory` of a leader's `ready` (#33 S4)

`InMemory` (B 213-275) of a `ready` report of role `leader` evaluated
(`notes/antithesis-rawnode-design.md` §3.3, `InMemory.ok`): a commit (`cmt`: a new commit to an entry
of the leader's term, beyond what its term recorded, with a quorum of acks, `Acked`). Every
hypothesis is in the binding's terms.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.ReadyOD2

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open AntCheck

section leader
variable [GooseExts]

theorem TermFn.get_with_self {α : Type} (f : TermFn α) (t : Int) (v : α) : (f.with t v).get t = .ok v := by
  induction f with
  | nil => simp [TermFn.with, TermFn.get, epure]
  | cons p ps ih =>
    unfold TermFn.with
    split
    · simp [TermFn.get, epure]
    · rename_i h
      unfold TermFn.get at ih ⊢
      have : (p.1 == t) = false := by simp only [beq_eq_false_iff_ne]; omega
      simp only [List.find?_cons, this]
      exact ih

theorem TermFn.has_with_self {α : Type} (f : TermFn α) (t : Int) (v : α) : (f.with t v).has t = true :=
  TermFn.has_of_get (TermFn.get_with_self f t v)

/-- **A leader's commit in memory** (`AppRespEnd`'s `maybeCommit`): its log at its term `lT`
(`ledLog`), the new commit `c` within it at an entry of its term, beyond what `termLen` recorded for
the term (`cmt`), with a quorum of acks at `c` in its term's configuration (`Acked`, B 252); the
commit recorded (`chain`, `termLen`), the checks (`CommitSafety`, `LeaderCompleteness`) passing. -/
theorem inMemory_lcommit {S : State} {R : RunCfg} (n : Fin R.N) (hc : S.cfg = R.cfg) (b : Str)
    (hb : DrainBy b)
    (t v c : w64) (lT : List Entry) (cf : Conf)
    (hrole : S.role[n.val]! = leader) (ht : S.currentTerm[n.val]! = uint.Z t)
    (hll : S.ledLog.get (uint.Z t) = .ok lT) (hlc : S.ledConf.get (uint.Z t) = .ok cf)
    (hcL : uint.Z c ≤ lT.length) (hc0 : 0 < uint.Z c)
    (hk : tlOld S.termLen (uint.Z t) < uint.Z c) (hterm : termAt lT (uint.Z c) = uint.Z t)
    (hq : isQuorum (S.acked n.val (uint.Z t) (uint.Z c)) cf = true)
    (hcs : comparable S.chain (lT.take (uint.Z c).toNat) = .ok true)
    (hlcp : ∀ p ∈ S.ledLog, p.1 > uint.Z t → isPrefix (lT.take (uint.Z c).toNat) p.2 = .ok true) :
    S.inMemory n.val (evReady (nodeId n) b (roleOf .leader) t v c []) =
      .ok { ok := true, role := S.role.set n.val leader, leaders := S.leaders, ledLog := S.ledLog,
            ledConf := S.ledConf, config := S.config, confAt := S.confAt, ledAt := S.ledAt, elAt := S.elAt,
            chain := if (S.chain.length : Int) < uint.Z c then lT.take (uint.Z c).toNat else S.chain,
            termLen := S.termLen.with (uint.Z t) (uint.Z c), viol := S.viol } := by
  have hnewC : subSeq lT 1 (uint.Z c) = .ok (lT.take (uint.Z c).toNat) := by
    have := subSeq_one lT (uint.Z c).toNat (by omega)
    rwa [uZ_toNat] at this
  have hknown : (if S.termLen.has (uint.Z t) then S.termLen.get (uint.Z t) else .ok 0) =
      (.ok (tlOld S.termLen (uint.Z t)) : EvalM Int) := tl_old_ok _ _
  have hk' : decide (uint.Z c > tlOld S.termLen (uint.Z t)) = true := decide_eq_true hk
  have hterm' : (termAt lT (uint.Z c) == uint.Z t) = true := by rw [hterm]; exact beq_self_eq_true _
  have hc0' : decide (uint.Z c > 0) = true := decide_eq_true hc0
  have hcL' : decide (uint.Z c ≤ (lT.length : Int)) = true := decide_eq_true hcL
  have hlr : (leader != leader) = false := bne_self_eq_false _
  have hct : (S.currentTerm[n.val]! == uint.Z t) = true := by rw [ht]; exact beq_self_eq_true _
  unfold State.inMemory
  rcases drainBy_cases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (config := { decide := true }) only [evReady, InMem.ok, InMem.T, InMem.role1, InMem.leads,
      InMem.wins, InMem.es, InMem.ld1, InMem.ll1, InMem.lc1, InMem.snapsM, InMem.app, InMem.ll2,
      InMem.cmt, InMem.known, InMem.L, InMem.c, InMem.newC, fieldEq, need, eok_bind, epure, roleOf,
      str_beq, str_bne, leader, follower, candidate, decide_false, decide_true, Bool.not_true,
      Bool.not_false, Bool.false_eq_true, ite_true, ite_false, andM_false, andM_true, orM_true, orM_false,
      server_of hc n, Option.isSome_none, Option.isSome_some, Option.map_none, Bool.false_and, Bool.and_false, Bool.true_and,
      Bool.and_true, hrole, hll, hlc, TermFn.has_of_get hll, hknown, hk', hterm', hc0', hcL', hct,
      logOf_nil, List.length_nil, bne_self_eq_false, hnewC, hcs, notM_ok, hq, anyM_lc hlcp,
      od_andM_ok, od_orM_ok] <;>
  (by_cases h : (S.chain.length : Int) < uint.Z c
   · rw [if_pos h, if_pos (decide_eq_true h)]
   · rw [if_neg h, if_neg (by simpa using h)])

theorem entOf_isConf (e : EntryM) : isConf (entOf e) = false := by
  unfold entOf isConf; split <;> (try split) <;> rfl

theorem anyM_notConf (es : List EntryM) (f : Nat → EvalM Bool) :
    anyM (List.range (logOf es).length) (fun q =>
      if (!isConf ((logOf es)[q]!)) = true then Except.ok false else f q) = .ok false := by
  generalize hl : List.range (logOf es).length = l
  have hl' : ∀ q ∈ l, q < (logOf es).length := by intro q hq; rw [← hl] at hq; exact List.mem_range.mp hq
  clear hl
  induction l with
  | nil => rfl
  | cons q l ih =>
    unfold anyM
    obtain ⟨e, he⟩ : ∃ e, es[q]? = some e :=
      ⟨es[q]'(by have := hl' q (List.mem_cons_self ..); rwa [logOf_length] at this),
       List.getElem?_eq_getElem _⟩
    dsimp only
    rw [logOf_getElem! he, entOf_isConf]
    simp only [Bool.not_false, ite_true, epure, eok_bind, Bool.false_eq_true, ite_false]
    exact ih (fun r hr => hl' r (List.mem_cons_of_mem _ hr))

theorem anyM_terms (es : List EntryM) (T : Int) (h : ∀ e ∈ es, uint.Z e.Term' = T) :
    anyM (logOf es) (fun e => (Except.ok (e.term != T) : EvalM Bool)) = .ok false := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    show anyM (entOf e :: logOf es) _ = _
    unfold anyM
    dsimp only
    rw [entOf_term, h e (List.mem_cons_self ..), bne_self_eq_false]
    simp only [epure, eok_bind, Bool.false_eq_true, ite_false]
    exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- **A leader's proposal in memory** (`ProposeEnd`'s `appendEntry`): the entries `e :: es'`, all of
its term, at the end of its leader log `lT` (`first`); no configuration change; its commit `c` not a
new one (`hcmt`: not beyond its term's recorded commit at an entry of its term) and `RecordedIn`
(`hrec`, or `0`); `ledLog` at its term extended. -/
theorem inMemory_lprop {S : State} {R : RunCfg} (n : Fin R.N) (hc : S.cfg = R.cfg) (b : Str)
    (hb : DrainBy b)
    (t v c : w64) (e : EntryM) (es' : List EntryM) (lT : List Entry)
    (hrole : S.role[n.val]! = leader) (ht : S.currentTerm[n.val]! = uint.Z t)
    (hll : S.ledLog.get (uint.Z t) = .ok lT)
    (hfirst : uint.Z e.Index' = (lT.length : Int) + 1)
    (hterms : ∀ x ∈ e :: es', uint.Z x.Term' = uint.Z t)
    (hcL : uint.Z c ≤ (lT ++ logOf (e :: es')).length)
    (hcm : (decide (uint.Z c > tlOld S.termLen (uint.Z t)) &&
      (termAt (lT ++ logOf (e :: es')) (uint.Z c) == uint.Z t)) = false)
    (hrec : uint.Z c = 0 ∨ recordedIn S.chain S.termLen (lT ++ logOf (e :: es')) (uint.Z c) (uint.Z t) = .ok true) :
    S.inMemory n.val (evReady (nodeId n) b (roleOf .leader) t v c (e :: es')) =
      .ok { ok := true, role := S.role.set n.val leader, leaders := S.leaders,
            ledLog := S.ledLog.with (uint.Z t) (lT ++ logOf (e :: es')),
            ledConf := S.ledConf, config := S.config, confAt := S.confAt, ledAt := S.ledAt, elAt := S.elAt,
            chain := S.chain, termLen := S.termLen, viol := S.viol } := by
  have hknown : (if S.termLen.has (uint.Z t) then S.termLen.get (uint.Z t) else .ok 0) =
      (.ok (tlOld S.termLen (uint.Z t)) : EvalM Int) := tl_old_ok _ _
  have hcL' : decide (uint.Z c ≤ ((lT ++ logOf (e :: es')).length : Int)) = true := decide_eq_true hcL
  have hlr : (leader != leader) = false := bne_self_eq_false _
  have hct : (S.currentTerm[n.val]! == uint.Z t) = true := by rw [ht]; exact beq_self_eq_true _
  have hfe : (firstOf (e :: es') != (lT.length : Int) + 1) = false := by
    show (uint.Z e.Index' != _) = _; rw [hfirst]; exact bne_self_eq_false _
  have hts := anyM_terms (e :: es') (uint.Z t) hterms
  have hbad := anyM_notConf (e :: es')
  unfold State.inMemory
  by_cases h0 : uint.Z c = 0
  · have hc0 : decide (uint.Z c > 0) = false := decide_eq_false (by omega)
    rcases drainBy_cases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := { decide := true }) only [evReady, InMem.ok, InMem.T, InMem.role1, InMem.leads,
        InMem.wins, InMem.es, InMem.ld1, InMem.ll1, InMem.lc1, InMem.snapsM, InMem.app, InMem.ll2,
        InMem.cmt, InMem.known, InMem.L, InMem.c, InMem.newC, fieldEq, need, eok_bind, epure, roleOf,
        str_beq, str_bne, leader, follower, candidate, decide_false, decide_true, Bool.not_true,
        Bool.not_false, Bool.false_eq_true, ite_true, ite_false, andM_false, andM_true, orM_true, orM_false,
        server_of hc n, Option.isSome_none, Option.isSome_some, Option.map_none, Bool.false_and, Bool.and_false, Bool.true_and,
        Bool.and_true, hrole, hll, TermFn.has_of_get hll, hknown, hc0, hcL', hct, stores_cons, hfe,
        TermFn.get_with_self, TermFn.has_with_self, hts, hbad, notM_ok, od_andM_ok, od_orM_ok, hcm]
  · have hcn : 0 ≤ uint.Z c := by word
    have hc0 : decide (uint.Z c > 0) = true := decide_eq_true (by omega)
    have hrc := hrec.resolve_left h0
    rcases drainBy_cases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := { decide := true }) only [evReady, InMem.ok, InMem.T, InMem.role1, InMem.leads,
        InMem.wins, InMem.es, InMem.ld1, InMem.ll1, InMem.lc1, InMem.snapsM, InMem.app, InMem.ll2,
        InMem.cmt, InMem.known, InMem.L, InMem.c, InMem.newC, fieldEq, need, eok_bind, epure, roleOf,
        str_beq, str_bne, leader, follower, candidate, decide_false, decide_true, Bool.not_true,
        Bool.not_false, Bool.false_eq_true, ite_true, ite_false, andM_false, andM_true, orM_true, orM_false,
        server_of hc n, Option.isSome_none, Option.isSome_some, Option.map_none, Bool.false_and, Bool.and_false, Bool.true_and,
        Bool.and_true, hrole, hll, TermFn.has_of_get hll, hknown, hcL', hct, stores_cons, hfe,
        TermFn.get_with_self, TermFn.has_with_self, hts, hbad, notM_ok, od_andM_ok, od_orM_ok, hcm, hrc, hc0]

end leader

end AntSim
end EtcdGrove
end Perennial
