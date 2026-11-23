/-
Lean-first (no Rocq counterpart). #33 S3b W4b (2026-11-23): `State.onDisk`'s successor sections
(`OnDiskLaws2.u0` .. `v5`) taken apart keeping the exact values `State__OnDisk.lean`'s Go proof
needs (the vote, `voteFor`, the exact `viol`), as `OnDiskLaws2`'s `_ok` lemmas do for the rest.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.OnDiskLaws2

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

end OnDiskProofLaws
end AntCheck
end EtcdGrove
end Perennial
