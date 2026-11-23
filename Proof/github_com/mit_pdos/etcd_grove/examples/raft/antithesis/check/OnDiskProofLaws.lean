/-
Lean-first (no Rocq counterpart). #33 S3b W4b (2026-11-23): `State.onDisk`'s successor sections
(`OnDiskLaws2.u0` .. `v5`) taken apart keeping the exact values `State__OnDisk.lean`'s Go proof
needs (the vote, `voteFor`, the exact `viol`), as `OnDiskLaws2`'s `_ok` lemmas do for the rest.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.OnDiskLaws2
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Init0Laws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.OnDisk

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntCheck
namespace OnDiskProofLaws

open OnDiskLaws2

variable {x : OnDisk}

/-- `voteFor` after `u0`: the vote where `voted` (B 395). -/
def vf0 (x : OnDisk) (voted : Bool) : List Str :=
  if voted then x.s.voteFor.set x.n (x.w.vote.getD []) else x.s.voteFor

theorem u0_ok' {K : Int → Bool → State → EvalM (Option State)} {r : Option State} (h : u0 x K = .ok r) :
    ∃ t1 voted, x.T1 = .ok t1 ∧ x.voted = .ok voted ∧ (voted = true → ∃ v, need x.w.vote = .ok v) ∧
      K t1 voted (ns0 x t1 voted (vf0 x voted)) = .ok r := by
  unfold u0 at h
  obtain ⟨t1, ht1, h⟩ := bind_ok h
  obtain ⟨vd, hvd, h⟩ := bind_ok h
  rcases ite_bool h with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · obtain ⟨v, hv, h⟩ := bind_ok h
    refine ⟨t1, true, ht1, hvd, fun _ => ⟨v, hv⟩, ?_⟩
    have : x.w.vote = some v := need_ok hv
    simp only [vf0, ite_true, this, Option.getD_some]
    exact h
  · exact ⟨t1, false, ht1, hvd, fun h => absurd h (by decide), h⟩

theorem u3_ok' {t1 : Int} {voted : Bool} {K : List VoteRec → EvalM (Option State)} {r : Option State}
    (h : u3 x t1 voted K = .ok r) :
    (voted = false ∧ K x.s.votes = .ok r) ∨
      ∃ v, voted = true ∧ need x.w.vote = .ok v ∧
        K (lset.add x.s.votes { voter := x.s.cfg.server[x.n]!, term := t1, cand := v }) = .ok r := by
  unfold u3 at h
  rcases ite_bool h with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · obtain ⟨v, hv, h⟩ := bind_ok h
    exact .inr ⟨v, rfl, hv, h⟩
  · exact .inl ⟨rfl, h⟩

theorem v1_ok' {K : SSet → EvalM (Option State)} {r : Option State} (h : v1 x K = .ok r) :
    ∃ cs, andM x.adv (notM (do comparable x.ch (← x.newC))) = .ok cs ∧
      K (if cs then setAdd x.vi go!"CommitSafety" else x.vi) = .ok r := by
  unfold v1 at h
  obtain ⟨cs, hcs, h⟩ := bind_ok h
  rcases ite_bool h with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · exact ⟨true, hcs, h⟩
  · exact ⟨false, hcs, h⟩

theorem v2_ok' {t1 : Int} {viol : SSet} {K : SSet → EvalM (Option State)} {r : Option State}
    (h : v2 x t1 viol K = .ok r) :
    ∃ ad, x.adv = .ok ad ∧ (ad = false → K viol = .ok r) ∧
      (ad = true → ∃ lc, anyM x.ll (fun p => andM (pure (decide (p.1 > t1)))
          (notM (do isPrefix (← x.newC) p.2))) = .ok lc ∧
        K (if lc then setAdd viol go!"LeaderCompleteness" else viol) = .ok r) := by
  unfold v2 at h
  obtain ⟨ad, had, h⟩ := bind_ok h
  rcases ite_bool h with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · obtain ⟨lc, hlc, h⟩ := bind_ok h
    refine ⟨true, had, fun h => absurd h (by decide), fun _ => ⟨lc, hlc, ?_⟩⟩
    rcases ite_bool h with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> exact h
  · exact ⟨false, had, fun _ => h, fun h => absurd h (by decide)⟩

theorem v3_ok' {viol : SSet} {K : List Entry → Bool → SSet → EvalM (Option State)} {r : Option State}
    (h : v3 x viol K = .ok r) :
    ∃ l1 ee, x.L1 = .ok l1 ∧ entriesEqual l1 x.L0 = .ok ee ∧ (ee = true → K l1 false viol = .ok r) ∧
      (ee = false → ∃ lm, anyM (List.range x.s.cfg.server.length)
          (fun b => andM (pure (b != x.n)) (notM (matching l1 (x.s.log[b]!)))) = .ok lm ∧
        K l1 true (if lm then setAdd viol go!"LogMatching" else viol) = .ok r) := by
  unfold v3 at h
  obtain ⟨l1, hl1, h⟩ := bind_ok h
  obtain ⟨ee, hee, h⟩ := bind_ok h
  cases ee
  · simp only [Bool.not_false, ite_true] at h
    obtain ⟨lm, hlm, h⟩ := bind_ok h
    refine ⟨l1, false, hl1, hee, fun h => absurd h (by decide), fun _ => ⟨lm, hlm, ?_⟩⟩
    rcases ite_bool h with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> exact h
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h
    exact ⟨l1, true, hl1, hee, fun _ => h, fun h => absurd h (by decide)⟩

theorem v4_ok' {l1 : List Entry} {c : Bool} {viol : SSet} {K : SSet → EvalM (Option State)} {r : Option State}
    (h : v4 x l1 c viol K = .ok r) :
    ∃ cp, andM (orM (pure c) x.adv) (notM (do isPrefix (← subSeq (← x.ch1) 1 (← need x.w.commit)) l1)) = .ok cp ∧
      K (if cp then setAdd viol go!"CommittedEntriesPreserved" else viol) = .ok r := by
  unfold v4 at h
  obtain ⟨cp, hcp, h⟩ := bind_ok h
  rcases ite_bool h with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · exact ⟨true, hcp, h⟩
  · exact ⟨false, hcp, h⟩

theorem v5_ok' {t1 : Int} {ns : State} {viol : SSet} {r : Option State} (h : v5 x t1 ns viol = .ok r) :
    ∃ c1 cb, x.conf1 = .ok c1 ∧
      andM x.adv (do pure ((c1.term != t1) || decide ((← need x.w.commit) > c1.index))) = .ok cb ∧
      r = some { ns with viol := if cb then setAdd viol go!"CommitBeyondConfirmed" else viol } := by
  unfold v5 at h
  obtain ⟨c1, hc1, h⟩ := bind_ok h
  obtain ⟨cb, hcb, h⟩ := bind_ok h
  rcases ite_bool h with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · exact ⟨c1, true, hc1, hcb, by cases h; rfl⟩
  · exact ⟨c1, false, hc1, hcb, by cases h; rfl⟩

/-- `votes` after `u3`, as one term (the vote where `voted`, B 401). -/
def votes3 (x : OnDisk) (t1 : Int) (voted : Bool) : List VoteRec :=
  if voted then lset.add x.s.votes { voter := x.s.cfg.server[x.n]!, term := t1, cand := x.w.vote.getD [] }
  else x.s.votes

theorem u3_ok'' {t1 : Int} {voted : Bool} {K : List VoteRec → EvalM (Option State)} {r : Option State}
    (h : u3 x t1 voted K = .ok r) :
    (voted = true → ∃ v, need x.w.vote = .ok v) ∧ K (votes3 x t1 voted) = .ok r := by
  rcases u3_ok' h with ⟨rfl, h⟩ | ⟨v, rfl, hv, h⟩
  · exact ⟨fun h => absurd h (by decide), h⟩
  · refine ⟨fun _ => ⟨v, hv⟩, ?_⟩
    have : x.w.vote = some v := need_ok hv
    simp only [votes3, ite_true, this, Option.getD_some]
    exact h

/-- `pre` before its updates (`OnDiskLaws2.pre0`), from the successor's `msgs` and `votes` only. -/
def pre0' (x : OnDisk) (msgs : List Fact) (votes : List VoteRec) : Pre :=
  { term := x.T0, voteTerm := x.s.voteTerm[x.n]!, voteFor := x.s.voteFor[x.n]!,
    commit := x.s.commitIndex[x.n]!, confirmed := x.s.confirmed[x.n]!,
    msgs := lset.minus msgs x.s.msgs, votes := lset.minus votes x.s.votes }

theorem pre0_eq (x : OnDisk) (ns : State) : pre0 x ns = pre0' x ns.msgs ns.votes := rfl

/-- `pre`'s facts (`msgs' \\ s.msgs`, B 352): at most the vote request and the ack. -/
theorem minus_two {α : Type} [DecidableEq α] {s0 m : List α} {el : Bool} {v : α}
    (h : m = (if el then lset.add s0 v else s0) ∨ ∃ a, m = lset.add (if el then lset.add s0 v else s0) a) :
    (lset.minus m s0).length ≤ 2 := by
  have h1 : (lset.minus (if el then lset.add s0 v else s0) s0).length ≤ 1 := by
    cases el
    · simp [lset_minus_self]
    · have := lset_minus_add s0 s0 v
      simp only [ite_true, lset_minus_self, List.length_nil] at *
      omega
  rcases h with rfl | ⟨a, rfl⟩
  · omega
  · have := lset_minus_add (if el then lset.add s0 v else s0) s0 a
    omega

/-- The numbers `u7` (B 404-419) needs: of `pre` after `u4`..`u6` (built from `msgs`, `votes`) and
of `undo[n]`: the kept prefixes within `bigOk`, the logs within `b`, the unions' sizes. -/
theorem u7_bounds {b E : Nat} (hW : x.Within b E) (hb : ((b + 1 : Nat) : Int) < numBound)
    {msgs : List Fact} {votes : List VoteRec} {me : Str} {t1 : Int} {pre4 pre5 pre6 : Pre}
    (hm : (lset.minus msgs x.s.msgs).length ≤ 2) (hv : (votes.length : Int) ≤ b + 1)
    (h4 : (x.stores = .ok false ∧ pre4 = { pre0' x msgs votes with keep := x.L0.length }) ∨
      ∃ fi suf, x.stores = .ok true ∧ x.first = .ok fi ∧ subSeq x.L0 fi x.L0.length = .ok suf ∧
        pre4 = { pre0' x msgs votes with keep := fi - 1, suffix := suf })
    (h5 : (x.acks = .ok false ∧ pre5 = pre4) ∨ ∃ f a, x.acks = .ok true ∧ x.f = .ok f ∧ x.ackAt = .ok a ∧
        pre5 = { pre4 with acks := [ackFact me f.src t1 a] })
    (h6 : (x.stores = .ok false ∧ pre6 = pre5) ∨
      ∃ fi, x.stores = .ok true ∧ x.first = .ok fi ∧ pre6 = { pre5 with low := fi }) :
    bigOk pre6.keep ∧ bigOk ((x.s.undo[x.n]!).getD {}).keep ∧ (x.L0.length : Int) ≤ b ∧
      (((x.s.undo[x.n]!).getD {}).suffix.length : Int) ≤ b ∧
      (((x.s.undo[x.n]!).getD {}).msgs.length : Int) + pre6.msgs.length < 2 ^ 62 ∧
      (((x.s.undo[x.n]!).getD {}).votes.length : Int) + pre6.votes.length < 2 ^ 62 ∧
      (((x.s.undo[x.n]!).getD {}).acks.length : Int) + pre6.acks.length < 2 ^ 62 := by
  have hu : ((x.s.undo[x.n]!).getD {}).Within b E := undo_within hW
  have hL0 := (L0_within hW).1
  have hb' := hb; unfold numBound at hb'
  obtain ⟨-, -, -, huk, -, -, -, hus, -, hum, -, hua, -, huv, -⟩ := hu
  have hvl := lset_minus_len votes x.s.votes
  have hus' := hus.1
  have key : bigOk pre6.keep ∧ pre6.msgs = lset.minus msgs x.s.msgs ∧
      pre6.votes = lset.minus votes x.s.votes ∧ pre6.acks.length ≤ 1 := by
    rcases h6 with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ <;> rcases h5 with ⟨-, rfl⟩ | ⟨-, -, -, -, -, rfl⟩ <;>
      rcases h4 with ⟨-, rfl⟩ | ⟨fi, suf, -, hfi, -, rfl⟩ <;>
      first
        | exact ⟨by unfold bigOk; dsimp only; omega, rfl, rfl, by simp [pre0']⟩
        | exact ⟨(first_bigOk hW hb hfi).2, rfl, rfl, by simp [pre0']⟩
  obtain ⟨hk, hm6, hv6, ha6⟩ := key
  rw [hm6, hv6]
  refine ⟨hk, huk, by omega, by omega, by omega, by omega, by omega⟩

section iris
open Iris Iris.BI Iris.ProofMode
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- An owned successor's struct opened to read its `Msgs` and `Votes` fields (B 349-352's `pre`). -/
theorem stateOwn_msgs_votes (q : Loc) (s : State) :
    stateOwn (GF := GF) q s ⊢ ∃ g : G.State, q ↦ g ∗ factsRO g.Msgs' s.msgs ∗ votesRO g.Votes' s.votes ∗
      (q ↦ g -∗ stateOwn q s) := by
  iintro Hq
  iunfold stateOwn at Hq
  iNamed Hq
  icases Hf with #Hf
  ihave #Hf2 := Hf
  iNamed Hf2
  iexists g
  iframe Hp HMsgs HVotes
  iintro Hp
  iunfold stateOwn
  iexists g
  iframe Hp Hf

/-- A Go `Pre`'s scalar fields holding `u`'s (as in `preRO`). -/
def preRel (g : G.Pre) (u : Pre) : Prop :=
  sint.Z g.Term' = u.term ∧ sint.Z g.VoteTerm' = u.voteTerm ∧ g.VoteFor' = u.voteFor ∧
    sint.Z g.Commit' = u.commit ∧ sint.Z g.Keep' = u.keep ∧ confirmedRel g.Confirmed' u.confirmed ∧
    sint.Z g.Low' = u.low ∧ g.Made' = u.made

/-- A `*Pre` being built (`OnDisk`'s `pre`, B 349-359), the struct owned, holding `u`. -/
noncomputable def preOwn (l : Loc) (u : Pre) : IProp GF :=
  iprop(∃ g : G.Pre, l ↦ g ∗ ⌜preRel g u⌝ ∗ logRO g.Suffix' u.suffix ∗ factsRO g.Msgs' u.msgs ∗
    votesRO g.Votes' u.votes ∗ factsRO g.Acks' u.acks)

end iris

end OnDiskProofLaws
end AntCheck
end EtcdGrove
end Perennial
