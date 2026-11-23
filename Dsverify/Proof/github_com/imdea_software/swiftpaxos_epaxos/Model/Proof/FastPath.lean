/-
The fast path's commit (`handlePreAcceptReply` with `2F - 1` counted equal replies at the
initial ballot) agrees with every committed value and is chosen: `fast_agree`. Stated over the
pre-state from `Inv S` and the counted replies (`Inv.lbInv`'s `Q` with `allEqual`), plus two facts
to become conjuncts: a counted reply is never ACCEPTED (the leader is still pre-accepting at the
initial ballot, so no Accept there exists), and a COMMITTED reply at the initial ballot carries a
committed value with the initial Phase 1's commands (questions.md, note on COMMITTED replies).

Paper proof: if a counted reply is COMMITTED, its committed value has the counted attributes and
the Phase 1's commands, so it is the fast path's value, already decided. Otherwise the three
counted replies are pre-accept votes for the value (`fastReplies`), the leader's `bal` is the
initial ballot (`fastLive`), and every committed value `u` was chosen: slow at the initial ballot
is excluded (`accInit` blocks the fast path), slow above it gives `u = v` (`chosenSafe`), fast
gives a common pre-accept voter of `u` and `v` (`paUnique`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.Decide

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace FastProof

open SafeProof DecideProof

theorem fast_agree (S : Sys) (hI : Inv0 S) (x : InstId) (hxq : x.q < nR) (v v0 : Val)
    (hph : S.ev x.q (.phase1 x (initBal x) v0)) (hcmd : v.cmds = v0.cmds)
    (hLbal : ∃ wL, (S.rep x.q).inst x = some wL ∧ wL.bal = initBal x)
    (Q : List (Nat × PreAcceptReply)) (hnd : (Q.map (·.1)).Nodup) (hlen : 2 * fR - 1 ≤ Q.length)
    (hQ : ∀ a m, (a, m) ∈ Q → a < nR ∧ a ≠ x.q ∧ Msg.preAcceptReply m ∈ S.msgs a x.q ∧
      (Msg.preAcceptReply m).instOf = some x ∧ m.ballot = initBal x ∧ m.seq = v.seq ∧
      m.deps = v.deps ∧
      (isPA m.status ∨ isCommitted m.status))
    (hcomm : ∀ a m, (a, m) ∈ Q → isCommitted m.status →
      ∃ u, S.committedVal x u ∧ u.seq = m.seq ∧ u.deps = m.deps ∧ u.cmds = v0.cmds) :
    (∀ u, S.committedVal x u → u = v) ∧ ((S.committedVal x v) ∨ S.fastReplies x v) := by
  obtain ⟨hwf, -, -, -, hbal, hown, hop, hvf, hrr, -, -, hagr, hdc, -, -, -, -, -, -, -, -, -, -,
    -, -, hsafe, hrepo⟩ := hI
  by_cases hc : ∃ a m, (a, m) ∈ Q ∧ isCommitted m.status
  · obtain ⟨a, m, hm, hcm⟩ := hc
    obtain ⟨u, hu, hs, hd, hcu⟩ := hcomm a m hm hcm
    obtain ⟨-, -, -, -, -, hseq, hdeps, -⟩ := hQ a m hm
    have huv : u = v := by
      cases u; cases v; simp only at hs hd hcu hcmd ⊢
      rw [hs, hd, hcu, hcmd, hseq, hdeps]
    subst huv
    exact ⟨fun u' hu' => hagr.1 x u' u hu' hu, Or.inl hu⟩
  · -- every counted reply is a pre-accept vote for `v`
    have hpa : ∀ a m, (a, m) ∈ Q → ∃ st, isPA st ∧ S.ev a (.vote x (initBal x) st v) := by
      intro a m hm
      obtain ⟨-, -, hmsg, hx, hb, hseq, hdeps, hst⟩ := hQ a m hm
      have hpa : isPA m.status := by
        rcases hst with h | h
        · exact h
        · exact absurd ⟨a, m, hm, h⟩ hc
      obtain ⟨-, hvote, -, -⟩ := hrr.2.1 a x.q m hmsg
      obtain ⟨-, va, hva, hvs, hvd⟩ := hvote hpa
      simp only [Msg.instOf, Option.some.injEq] at hx
      rw [hx, hb] at hva
      obtain ⟨ℓ1, v1, hph1, hc1⟩ := hvf.1 a x _ _ _ hva hpa
      have := (hop.1 ℓ1 x.q x _ v1 v0 hph1 hph).2.1
      have hvaeq : va = v := by
        cases va; cases v; simp only at hvs hvd hc1 hcmd this ⊢
        rw [hc1, this, ← hcmd, hvs, hvd, hseq, hdeps]
      exact ⟨m.status, hpa, hvaeq ▸ hva⟩
    have hfr : S.fastReplies x v := by
      refine ⟨Q.map (·.1), hnd, by simpa using hlen, fun a ha => ?_⟩
      simp only [List.mem_map] at ha
      obtain ⟨⟨a', m⟩, hm, rfl⟩ := ha
      obtain ⟨h1, h2, -⟩ := hQ a' m hm
      exact ⟨h1, h2, hpa a' m hm⟩
    have hfl : S.fastLive x v := by
      obtain ⟨wL, hwL, hb⟩ := hLbal
      exact ⟨hfr, Or.inl (by rw [hwL]; simp [hb])⟩
    have hcs := chosenSafe_of_safe S hwf hbal hown hvf hsafe
    refine ⟨fun u hu => ?_, Or.inr hfr⟩
    rcases hdc x u hu with ⟨b, hsc⟩ | ⟨hfu, -⟩
    · obtain ⟨hreal, -⟩ := slowChosen_real S hbal hwf hown hvf x b u hsc
      -- a voter of `u` at `b`, and the Accept it followed
      obtain ⟨Qs, -, hls, hQs⟩ := hsc
      obtain ⟨r, hr⟩ : ∃ r, r ∈ Qs := by
        cases Qs with
        | nil => simp [nR] at hls
        | cons r _ => exact ⟨r, List.mem_cons_self⟩
      obtain ⟨ℓ, hacc⟩ := hvf.2 r x b u (hQs r hr).2
      rcases hreal with rfl | hge
      · exact absurd hfl (fun h => not_fastLive_of_fastBlocked S x v hxq h
          (hrepo.2.2.2.2.2.2.2.1 ℓ x u hacc v))
      · have hlt : zz (initBal x) < zz b := by
          rw [zz_initBal x hxq]; simp [nR] at hxq hge; omega
        exact (hcs x (initBal x) v (Or.inr ⟨rfl, hfl⟩) b hlt).1 ℓ u hacc
    · obtain ⟨Qu, hQu, hlu, hQum⟩ := hfu
      obtain ⟨Qv, hQv, hlv, hQvm⟩ := hfr
      obtain ⟨a, hau, hav⟩ := meet_fast x.q hxq hQu hQv (fun a h => ⟨(hQum a h).1, (hQum a h).2.1⟩)
        (fun a h => ⟨(hQvm a h).1, (hQvm a h).2.1⟩) hlu (by simp [fR] at hlv ⊢; omega)
      obtain ⟨-, -, st, hst, h1⟩ := hQum a hau
      obtain ⟨-, -, st', hst', h2⟩ := hQvm a hav
      exact hrepo.2.2.2.2.2.1 a x _ st st' u v hst hst' h1 h2

end FastProof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
