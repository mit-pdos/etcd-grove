/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/proto/SrvFrame.lean (241f27e).
-/
/-
`proto` — frame lemmas for steps that change one server's own state (`upd σ.srv i s`), and the
facts about a valid AppendEntries (its entries are a slice of the leader log; the follower's log
agrees with the leader log up to the matched entries).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.proto.Frame

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace github_com.hashicorp.raft
namespace proto

/-- The state with server `i`'s own state replaced. -/
abbrev setSrv (σ : PState) (i : SID) (s : SState) : PState := { σ with srv := upd σ.srv i s }

theorem setSrv_srv (σ : PState) (i : SID) (s : SState) (j : SID) :
    (setSrv σ i s).srv j = if j = i then s else σ.srv j := rfl

theorem setSrv_log (σ : PState) (i : SID) (s : SState) (j : SID) :
    (setSrv σ i s).log j = if j = i then s.log else σ.log j := by
  unfold PState.log; rw [setSrv_srv]; split <;> rfl

theorem setSrv_term (σ : PState) (i : SID) (s : SState) (j : SID) :
    (setSrv σ i s).term j = if j = i then s.term else σ.term j := by
  unfold PState.term; rw [setSrv_srv]; split <;> rfl

/-- `IVotes` survives a change of server states keeping the votes and raising terms. -/
theorem IVotes_srv {σ σ' : PState} (hv : σ'.srvs = σ.srvs) (hc : σ'.cand = σ.cand)
    (hvo : σ'.votes = σ.votes) (hl : σ'.leader = σ.leader)
    (hs : ∀ j, (σ'.srv j).vterm = (σ.srv j).vterm ∧ (σ'.srv j).vcand = (σ.srv j).vcand)
    (ht : ∀ j, σ.term j ≤ σ'.term j) (h : IVotes σ) : IVotes σ' := by
  obtain ⟨a, b, c⟩ := h
  refine ⟨fun j T c' L b' hvj => ?_, fun j hj => ?_, fun c' T x hcx => ?_⟩
  · rw [hvo] at hvj
    obtain ⟨a1, a2, a3, a4, a5⟩ := a j T c' L b' hvj
    rw [hv, (hs j).1, hc, hl]
    exact ⟨a1, a2, a3, a4, a5⟩
  · rw [hv] at hj
    obtain ⟨b1, b2⟩ := b j hj
    rw [(hs j).1, (hs j).2, hvo]
    exact ⟨Nat.le_trans b1 (ht j), b2⟩
  · rw [hc] at hcx
    obtain ⟨c1, c2, c3, c4⟩ := c c' T x hcx
    rw [hv]
    exact ⟨c1, c2, Nat.le_trans c3 (ht c'), c4⟩

theorem ent_take_some {L : RLog} {n k : Nat} {e : Entry} (h : ent (L.take n) k = some e) :
    ent L k = some e := by
  have := (ent_le_length h).2
  simp only [List.length_take] at this
  rw [ent_take L n k (by omega)] at h
  exact h

/-! ### Valid AppendEntries -/

theorem ae_slice {σ : PState} {T prev pt lci : Nat} {ents : RLog} (h : AEok σ T prev pt ents lci)
    {x : Nat} (h1 : 1 ≤ x) (h2 : x ≤ ents.length) : ent ents x = ent (σ.llog T) (prev + x) := by
  have he := h.2.2.2.2.1
  generalize ents.length = n at he h2
  subst he
  rw [ent_take _ _ _ h2, ent_drop _ _ _ h1]

theorem ae_slice_term {σ : PState} {T prev pt lci : Nat} {ents : RLog} (h : AEok σ T prev pt ents lci)
    {x : Nat} (h1 : 1 ≤ x) (h2 : x ≤ ents.length) :
    termAt ents x = termAt (σ.llog T) (prev + x) := by
  simp [termAt, ae_slice h h1 h2]

/-- The follower's log agrees with the leader log up to its matched entries. -/
theorem ae_agree_upto {σ : PState} (hLo : ILogs σ) {i : SID} (hi : i ∈ σ.srvs)
    {prev pt lci j : Nat} {ents : RLog} (hae : AEok σ (σ.term i) prev pt ents lci)
    (hpm : prevMatch (σ.log i) prev pt) (hm : matchedUpTo (σ.log i) prev ents j)
    (hlen : prev + j ≤ (σ.log i).length) : agree (σ.log i) (σ.llog (σ.term i)) (prev + j) := by
  by_cases hz : prev + j = 0
  · rw [hz]; exact agree_zero _ _
  have hnT : prev + j ≤ (σ.llog (σ.term i)).length := by
    have := hae.2.1; have := hm.1; omega
  apply LMok_agree (hLo.1 i hi).1 (hLo.2.1 _) (by omega) hlen hnT
  cases j with
  | zero =>
    rcases hpm with hp | ⟨_, hp⟩
    · omega
    · simp only [Nat.add_zero]
      rw [hp, hae.2.2.2.1 (by omega)]
  | succ j' =>
    obtain ⟨_, ht⟩ := hm.2 j' (Nat.lt_succ_self _)
    have e : prev + 1 + j' = prev + (j' + 1) := by omega
    rw [e] at ht
    rw [ht, ae_slice_term hae (by omega) hm.1]

/-- The follower's log after storing the request's entries is a prefix of the leader log. -/
theorem fs_log {σ : PState} {T prev pt lci j : Nat} {ents L : RLog} (hae : AEok σ T prev pt ents lci)
    (hag : agree L (σ.llog T) (prev + j)) (hlen : L.length = prev + j) (hj : j ≤ ents.length) :
    L ++ ents.drop j = (σ.llog T).take (prev + ents.length) := by
  have hL : L = (σ.llog T).take (prev + j) := by
    have := hag.2.2
    rw [List.take_of_length_le (by omega)] at this
    exact this
  have he := hae.2.2.2.2.1
  generalize ents.length = n at he hj ⊢
  subst he
  rw [hL, List.drop_take, List.drop_drop, ← List.take_add]
  congr 1
  omega

end proto
end github_com.hashicorp.raft
end Perennial
