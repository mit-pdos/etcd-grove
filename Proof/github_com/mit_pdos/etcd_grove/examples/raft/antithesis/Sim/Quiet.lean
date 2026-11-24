/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: the steps that report nothing (#33 S4)

`antSim_quiet`'s steps keep the node's role, term, log and commit (`Quiet`: an input noted, no
`Ready`, or a `Ready` the harness does not report). What they may move is a leader's `Match` (an
acknowledgement that commits nothing, its ack fact in `msgs` by C4 at the leader's term) and a
candidate's tally (a grant, its fact in `msgs` by C4; its own vote, in `votes` by `QsOk`): this file
shows `LeaderPart`'s and `CandPart`'s facts survive those steps (`MatchOk`, `VotesOk`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Outbox
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.SendRel

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open GMap AntCheck

/-! ## `Granted(n)` -/

theorem mem_foldl_setAdd {P : Str → Prop} [DecidablePred P] (x : Str) :
    ∀ (l : List Str) (acc : SSet), (x ∈ acc ∨ (x ∈ l ∧ P x)) →
      x ∈ l.foldl (fun out j => if P j then setAdd out j else out) acc
  | [], _, h => h.elim id (fun h => absurd h.1 (List.not_mem_nil))
  | j :: l, acc, h => by
    simp only [List.foldl_cons]
    apply mem_foldl_setAdd x l
    rcases h with h | ⟨h1, h2⟩
    · left; split
      · exact mem_setAdd.mpr (.inl h)
      · exact h
    · rcases List.mem_cons.mp h1 with rfl | h1
      · left; rw [if_pos h2]; exact mem_setAdd.mpr (.inr rfl)
      · right; exact ⟨h1, h2⟩

/-- A grant fact. -/
def grantF (src dst : Str) (t : Int) : Fact := { type := go!"grant", src := src, dst := dst, term := t }

/-- A grant to `n` at its term from another node is in `Granted(n)` (R 277-279). -/
theorem granted_grant {S : State} (hc : S.cfg = cfg3) {n j : Fin 3} (hne : j ≠ n)
    (h : grantF (nameOf (nodeId j)) (nameOf (nodeId n)) (S.currentTerm[n.val]!) ∈ S.msgs) :
    (S.granted n.val).has (nameOf (nodeId j)) = true := by
  unfold State.granted
  simp only [SSet.has, List.contains_iff_mem]
  rw [server_of hc n]
  have hmem : nameOf (nodeId j) ∈ S.cfg.server := by
    have := server_has j
    rw [hc, cfg3_server]; simpa [SSet.has] using this
  have hne' : nameOf (nodeId j) ≠ nameOf (nodeId n) := fun h' => hne (name_inj h')
  have hf := mem_foldl_setAdd (P := fun j' => (j' != nameOf (nodeId n) &&
      S.msgs.contains (grantF j' (nameOf (nodeId n)) (S.currentTerm[n.val]!))) = true)
      (nameOf (nodeId j)) S.cfg.server []
      (.inr ⟨hmem, by simp only [Bool.and_eq_true, bne_iff_ne, List.contains_iff_mem]; exact ⟨hne', h⟩⟩)
  split
  · exact mem_setAdd.mpr (.inl hf)
  · exact hf

/-- A node's own vote at its term, in `votes`, puts it in `Granted(n)` (R 280). -/
theorem granted_self {S : State} (hc : S.cfg = cfg3) {n : Fin 3}
    (h : ({ voter := nameOf (nodeId n), term := S.currentTerm[n.val]!, cand := nameOf (nodeId n) } :
      VoteRec) ∈ S.votes) :
    (S.granted n.val).has (nameOf (nodeId n)) = true := by
  unfold State.granted
  simp only [SSet.has, List.contains_iff_mem]
  rw [server_of hc n]
  rw [if_pos h]
  exact mem_setAdd.mpr (.inr rfl)

section quiet
variable [GooseExts]

/-! ## What a quiet step keeps -/

/-- `LeaderPart`'s `Match` facts at a state `s`. -/
def MatchOk (S : State) (n : Fin 3) (s : PState) : Prop :=
  (∀ (j : Fin 3) (k : w64), uint.Z k ≤ uint.Z (matchOf s (nodeId j)) →
      plogTermAt base0 s.log k = some s.term →
      AckIn S (nameOf (nodeId j)) (nameOf (nodeId n)) (uint.Z s.term) (uint.Z k)) ∧
  (∀ j : Fin 3, j ≠ n → matchOf s (nodeId j) = W64 0 ∨
      AckIn S (nameOf (nodeId j)) (nameOf (nodeId n)) (uint.Z s.term)
        (uint.Z (matchOf s (nodeId j))))

/-- `CandPart`'s tally facts at a state `s`. -/
def VotesOk (S : State) (n : Fin 3) (s : PState) : Prop :=
  ∀ j : Fin 3, s.votes !! nodeId j = some true → (S.granted n.val).has (nameOf (nodeId j)) = true

/-- What a step from `s` to `s'` that keeps the role keeps: the base, the term, and (for a leader)
the `Match` facts, (for a candidate) the tally facts. -/
def QKeep (S : State) (n : Fin 3) (s s' : PState) : Prop :=
  s'.base = s.base ∧ s'.term = s.term ∧
  (s'.role = .leader → MatchOk S n s → MatchOk S n s') ∧
  (s'.role = .candidate → VotesOk S n s → VotesOk S n s')

theorem QKeep.same {S : State} {n : Fin 3} {s s' : PState} (hb : s'.base = s.base)
    (ht : s'.term = s.term) (hl : s'.log = s.log) (hm : s'.matched = s.matched)
    (hv : s'.votes = s.votes) : QKeep S n s s' := by
  refine ⟨hb, ht, fun _ h => ?_, fun _ h => ?_⟩
  · unfold MatchOk matchOf at *; rw [ht, hl, hm]; exact h
  · unfold VotesOk at *; rw [hv]; exact h

theorem QKeep.refl {S : State} {n : Fin 3} {s : PState} : QKeep S n s s :=
  QKeep.same rfl rfl rfl rfl rfl

theorem QKeep.trans {S : State} {n : Fin 3} {s s1 s' : PState} (h1 : QKeep S n s s1)
    (h2 : QKeep S n s1 s') (hr1 : s1.role = s'.role) : QKeep S n s s' :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, fun hr h => h2.2.2.1 hr (h1.2.2.1 (hr1 ▸ hr) h),
    fun hr h => h2.2.2.2 hr (h1.2.2.2 (hr1 ▸ hr) h)⟩

theorem AckIn.le {S : State} {src dst : Str} {t k k' : Int} (h : AckIn S src dst t k)
    (hk : k' ≤ k) : AckIn S src dst t k' := by
  obtain ⟨a, ha, h1, h2, h3, h4, h5⟩ := h; exact ⟨a, ha, h1, h2, h3, h4, Int.le_trans hk h5⟩

/-- An acknowledgement raising `Match` of `src` (`MaybeUpdate`) keeps the `Match` facts, its ack
fact at the leader's term in `msgs` when it raises it. -/
theorem matchOk_raise {S : State} {n i : Fin 3} {s s' : PState} {src x idx : w64}
    (hsrc : src = nodeId i) (hx : s.matched !! src = some x)
    (hack : uint.Z x < uint.Z idx →
      AckIn S (nameOf src) (nameOf (nodeId n)) (uint.Z s.term) (uint.Z idx))
    (ht : s'.term = s.term) (hl : s'.log = s.log)
    (hm : s'.matched = <[src := if uint.Z x < uint.Z idx then idx else x]> s.matched)
    (h : MatchOk S n s) : MatchOk S n s' := by
  have hmo : ∀ j : Fin 3, matchOf s' (nodeId j) =
      if nodeId j = src then (if uint.Z x < uint.Z idx then idx else x) else matchOf s (nodeId j) := by
    intro j
    unfold matchOf; rw [hm]
    by_cases hj : nodeId j = src
    · rw [if_pos hj, hj, lookup_insert]; rfl
    · rw [if_neg hj, lookup_insert_ne _ _ (Ne.symm hj)]
  have hxo : matchOf s src = x := by unfold matchOf; rw [hx]; rfl
  obtain ⟨h3, h4⟩ := h
  refine ⟨fun j k hk hkt => ?_, fun j hj => ?_⟩
  · rw [ht, hl] at *
    rw [hmo j] at hk
    by_cases hjs : nodeId j = src
    · rw [if_pos hjs] at hk
      by_cases hlt : uint.Z x < uint.Z idx
      · rw [if_pos hlt] at hk; rw [hjs]; exact (hack hlt).le hk
      · rw [if_neg hlt] at hk; exact h3 j k (by rw [hjs, hxo]; exact hk) hkt
    · rw [if_neg hjs] at hk; exact h3 j k hk hkt
  · rw [ht, hmo j]
    by_cases hjs : nodeId j = src
    · rw [if_pos hjs]
      by_cases hlt : uint.Z x < uint.Z idx
      · rw [if_pos hlt]; right; rw [hjs]; exact hack hlt
      · rw [if_neg hlt, ← hxo, ← hjs]; exact h4 j hj
    · rw [if_neg hjs]; exact h4 j hj

/-- A vote tallied (`recordVote`) keeps the tally facts, the vote's grant in `Granted(n)`. -/
theorem votesOk_record {S : State} {n : Fin 3} {s s' : PState} {src : w64} {b : Bool}
    (hg : b = true → ∀ j : Fin 3, src = nodeId j → (S.granted n.val).has (nameOf (nodeId j)) = true)
    (hv : s'.votes = recordVote s.votes src b) (h : VotesOk S n s) : VotesOk S n s' := by
  intro j hj
  rw [hv] at hj
  unfold recordVote at hj
  split at hj
  · exact h j hj
  · by_cases hjs : src = nodeId j
    · rw [hjs, lookup_insert] at hj
      exact hg (Option.some.inj hj) j hjs
    · rw [lookup_insert_ne _ _ hjs] at hj; exact h j hj

/-! ## A received message's step -/

/-- The type switch keeps the term (`HandleEnd`: no arm changes it). -/
theorem handle_term {c : CfgM} {id : w64} {s s' : PState} {m : Msg}
    (hsc : m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp ∨ m.ty = .propose)
    (h : HandleEnd c id s m s') : s'.term = s.term := by
  unfold HandleEnd at h
  rcases hsc with hty | hty | hty | hty | hty | hty | hty <;> rw [hty] at h <;> simp only at h
  · rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> rfl
  · split at h
    · rcases h with ⟨-, rfl⟩ | ⟨-, mt, ms, -, -, rfl⟩ | ⟨-, rfl⟩ <;> rfl
    · subst h; rfl
  · split at h
    · subst h; rfl
    · rcases h with ⟨-, rfl⟩ | ⟨-, _, _, -, rfl⟩ | ⟨-, -, _, _, -, -, rfl⟩ <;> rfl
  · split at h
    · unfold AppRespEnd at h
      rcases h with ⟨-, rfl⟩ | ⟨-, -, ms, -, rfl⟩ | ⟨-, x, n, -, -, ms, -, rfl⟩ <;> rfl
    · subst h; rfl
  · split at h
    · subst h; rfl
    · subst h; rfl
  · split at h
    · obtain ⟨ms, -, rfl⟩ := h; rfl
    · subst h; rfl
  · unfold ProposeEnd at h
    split at h
    · rcases h with rfl | ⟨es, ms, -, -, rfl⟩ <;> rfl
    · split at h <;> (subst h; rfl)

/-- `AppEnd` keeps the base, the term and the role (the adopting follower's). -/
theorem appEnd_facts {id : w64} {X s' : PState} {m : Msg} (h : AppEnd id X m s') :
    s'.base = X.base ∧ s'.term = X.term ∧ s'.role = X.role := by
  rcases h with ⟨-, rfl⟩ | ⟨-, _, _, -, rfl⟩ | ⟨-, -, _, _, -, -, rfl⟩ <;> exact ⟨rfl, rfl, rfl⟩

/-- **The type switch of a received message at the node's term keeps `QKeep`** when it keeps the
role and the log: a grant tallied is in `Granted(n)` (C4: its grant fact, at the candidate's term,
from another node), an acknowledgement raising `Match` has its ack fact (C4, at the leader's term,
its index not `0`); a follower adopting the sender stays a follower. -/
theorem quiet_handle {S : State} {net : List Msg} {n : Fin 3} {s s' : PState} {m : Msg}
    (hc : S.cfg = cfg3) (hnet : NetOk S net) (hm : m ∈ net) (hmd : m.dst = nodeId n)
    (hsd : m.src ≠ m.dst) (hct : S.currentTerm[n.val]! = uint.Z s.term) (hmt : m.term = s.term)
    (h : HandleEnd cfgM3 (nodeId n) s m s') (hr : s'.role = s.role) (hl : s'.log = s.log) :
    QKeep S n s s' := by
  obtain ⟨hsc, ⟨i, hsi, -⟩, j, hdj, hj⟩ := hnet.1 m hm
  have hjn : j = n := nodeId_inj (hdj.symm.trans hmd)
  subst hjn
  have hf := hj (by rw [hct, hmt]; exact Int.le_refl _)
  unfold HandleEnd at h
  rcases hsc with hty | hty | hty | hty | hty | hty | hty <;> rw [hty] at h <;> simp only at h
  · rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
    · exact QKeep.same rfl rfl rfl rfl rfl
    · exact QKeep.same rfl rfl rfl rfl rfl
  · split at h
    · rename_i hcand
      rcases h with ⟨-, rfl⟩ | ⟨-, mt, ms, -, -, rfl⟩ | ⟨-, rfl⟩
      · refine ⟨rfl, rfl, fun hr' => absurd (hr'.symm.trans hcand) (by simp [padoptLeader, psendMsgs, pwinState, pappend, pbecomeLeader, pbecomeFollower]), fun _ hv => ?_⟩
        refine votesOk_record (fun hb j' hj' => ?_) rfl hv
        have hrj : m.reject = false := by simpa using hb
        have hg := hf.2.2.1 ⟨hty, hrj⟩
        have hne : j' ≠ j := fun he => hsd (by rw [hj', he, hdj])
        refine granted_grant hc hne ?_
        rw [hct, ← hmt, ← hj', ← hdj]; exact hg
      · exact absurd (hr.trans hcand) (by simp [padoptLeader, psendMsgs, pwinState, pappend, pbecomeLeader, pbecomeFollower])
      · exact absurd (hr.trans hcand) (by simp [padoptLeader, psendMsgs, pwinState, pappend, pbecomeLeader, pbecomeFollower])
    · subst h; exact QKeep.refl
  · split at h
    · subst h; exact QKeep.refl
    · obtain ⟨hb, ht, hr'⟩ := appEnd_facts h
      exact ⟨hb, ht, fun hl' => absurd (hl'.symm.trans hr') (by simp [padoptLeader, psendMsgs, pwinState, pappend, pbecomeLeader, pbecomeFollower]),
        fun hl' => absurd (hl'.symm.trans hr') (by simp [padoptLeader, psendMsgs, pwinState, pappend, pbecomeLeader, pbecomeFollower])⟩
  · split at h
    · rename_i hlead
      unfold AppRespEnd at h
      rcases h with ⟨-, rfl⟩ | ⟨-, -, ms, -, rfl⟩ | ⟨hrj, x, c, hx, -, ms, -, rfl⟩
      · exact QKeep.refl
      · exact QKeep.same rfl rfl rfl rfl rfl
      · refine ⟨rfl, rfl, fun _ hmo => ?_, fun hl' => absurd (hl'.symm.trans hlead) (by simp [padoptLeader, psendMsgs, pwinState, pappend, pbecomeLeader, pbecomeFollower])⟩
        refine matchOk_raise hsi hx (fun hlt => ?_) rfl rfl rfl hmo
        have hi0 : m.index ≠ W64 0 := by
          intro h0; rw [h0] at hlt; have := uint_Z_nonneg x; simp at hlt <;> omega
        have ha := hf.2.2.2 ⟨hty, hrj, hi0⟩
        rw [hdj, hmt] at ha; exact ha
    · subst h; exact QKeep.refl
  · split at h
    · subst h; exact QKeep.refl
    · subst h
      exact ⟨rfl, rfl, fun hl' => absurd hl' (by simp [padoptLeader, psendMsgs, pwinState, pappend, pbecomeLeader, pbecomeFollower]),
        fun hl' => absurd hl' (by simp [padoptLeader, psendMsgs, pwinState, pappend, pbecomeLeader, pbecomeFollower])⟩
  · split at h
    · obtain ⟨ms, -, rfl⟩ := h; exact QKeep.same rfl rfl rfl rfl rfl
    · subst h; exact QKeep.refl
  · unfold ProposeEnd at h
    split at h
    · rcases h with rfl | ⟨es, ms, -, -, rfl⟩
      · exact QKeep.refl
      · exact QKeep.same rfl rfl hl rfl rfl
    · split at h
      · subst h; exact QKeep.same rfl rfl rfl rfl rfl
      · subst h; exact QKeep.refl

/-- **A received message's step (`RecvEnd`, its term not `0`) that keeps the role, the term and
the log keeps `QKeep`**: a higher term's preamble would change the term (the type switch keeps the
preamble's), so the message is at the node's term. -/
theorem quiet_recv {S : State} {net : List Msg} {n : Fin 3} {s s' : PState} {m : Msg}
    (hc : S.cfg = cfg3) (hnet : NetOk S net) (hm : m ∈ net) (hmd : m.dst = nodeId n)
    (hsd : m.src ≠ m.dst) (hm0 : m.term ≠ W64 0) (hct : S.currentTerm[n.val]! = uint.Z s.term)
    (h : RecvEnd cfgM3 (nodeId n) s m s') (hr : s'.role = s.role) (ht : s'.term = s.term)
    (hl : s'.log = s.log) : QKeep S n s s' := by
  rcases h with ⟨h0, -⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, hh⟩
  · exact absurd h0 hm0
  · exact QKeep.refl
  · have ht' := handle_term (hnet.1 m hm).1 hh
    rcases hpre with ⟨hlt, rfl⟩ | ⟨hmt, rfl⟩
    · have : s'.term = m.term := ht'
      rw [this] at ht; rw [ht] at hlt; exact absurd hlt (Int.lt_irrefl _)
    · exact quiet_handle hc hnet hm hmd hsd hct hmt hh hr hl

/-! ## A tick, a proposal, `Advance` -/

theorem w64_succ_ne (x : w64) : x + W64 1 ≠ x := by
  intro h
  have h2 := congrArg uint.Z h
  have := uint_Z_nonneg x
  word

/-- A tick that keeps the term: nothing, or a leader's heartbeats. -/
theorem quiet_tick {c : CfgM} {id : w64} {S : State} {n : Fin 3} {s s' : PState}
    (h : TickEnd c id s s') (ht : s'.term = s.term) : QKeep S n s s' := by
  rcases h with rfl | ⟨-, -, peers, cl, -, rfl⟩ | ⟨-, ms, -, rfl⟩
  · exact QKeep.refl
  · exact absurd ht (w64_succ_ne _)
  · exact QKeep.same rfl rfl rfl rfl rfl

/-- A proposal that keeps the log: dropped, an empty batch, or forwarded. -/
theorem quiet_propose {id : w64} {S : State} {n : Fin 3} {s s' : PState} {m : Msg}
    (h : ProposeEnd id s m s') (hl : s'.log = s.log) : QKeep S n s s' := by
  unfold ProposeEnd at h
  split at h
  · rcases h with rfl | ⟨es, ms, -, -, rfl⟩
    · exact QKeep.refl
    · exact QKeep.same rfl rfl hl rfl rfl
  · split at h
    · subst h; exact QKeep.same rfl rfl rfl rfl rfl
    · subst h; exact QKeep.refl

/-- What `QsOk` says of a self-addressed message `Advance` steps at term `T`. -/
def QMsg (S : State) (n : Fin 3) (T : w64) (q : Msg) : Prop :=
  SelfMsg (nodeId n) T q ∧
  (q.ty = .appResp → AckIn S (nameOf (nodeId n)) (nameOf (nodeId n)) (uint.Z T) (uint.Z q.index)) ∧
  (q.ty = .voteResp →
    ({ voter := nameOf (nodeId n), term := uint.Z T, cand := nameOf (nodeId n) } : VoteRec) ∈ S.votes)

/-- One step of `Advance`: the term kept, a non-candidate's role kept, and `QKeep` when the role is
kept (the self-acknowledgement's ack fact and the self-vote are `QsOk`'s). -/
theorem quiet_adv_step {S : State} {n : Fin 3} {T : w64} {s s1 : PState} {q : Msg}
    (hc : S.cfg = cfg3) (hT : s.term = T) (hct : S.currentTerm[n.val]! = uint.Z T)
    (hq : QMsg S n T q) (h : RecvEnd cfgM3 (nodeId n) s q s1) :
    s1.term = s.term ∧ (s.role ≠ .candidate → s1.role = s.role) ∧
      (s1.role = s.role → QKeep S n s s1) := by
  obtain ⟨⟨hqs, -, hqt, hrj, hty⟩, hack, hvote⟩ := hq
  have hqt' : q.term = s.term := hqt.trans hT.symm
  have hh : HandleEnd cfgM3 (nodeId n) s q s1 := by
    rcases h with ⟨-, hh⟩ | ⟨-, hlt, -⟩ | ⟨-, s2, hpre, hh⟩
    · exact hh
    · rw [hqt'] at hlt; exact absurd hlt (Int.lt_irrefl _)
    · rcases hpre with ⟨hlt, -⟩ | ⟨-, rfl⟩
      · rw [hqt'] at hlt; exact absurd hlt (Int.lt_irrefl _)
      · exact hh
  have hrefl : s1 = s → s1.term = s.term ∧ (s.role ≠ .candidate → s1.role = s.role) ∧
      (s1.role = s.role → QKeep S n s s1) := fun h => by subst h; exact ⟨rfl, fun _ => rfl, fun _ => QKeep.refl⟩
  unfold HandleEnd at hh
  rcases hty with hty | hty <;> rw [hty] at hh <;> simp only at hh
  · split at hh
    · unfold AppRespEnd at hh
      rcases hh with ⟨-, rfl⟩ | ⟨h', -⟩ | ⟨-, x, c, hx, -, ms, -, rfl⟩
      · exact hrefl rfl
      · rw [hrj] at h'; cases h'
      · refine ⟨rfl, fun _ => rfl, fun _ => ⟨rfl, rfl, fun _ hmo => ?_, fun _ hv => ?_⟩⟩
        · exact matchOk_raise (i := n) hqs hx (fun _ => by rw [hqs, hT]; exact hack hty) rfl rfl rfl hmo
        · exact hv
    · exact hrefl hh
  · split at hh
    · rename_i hcand
      rcases hh with ⟨-, rfl⟩ | ⟨-, mt, ms, -, -, rfl⟩ | ⟨-, rfl⟩
      · refine ⟨rfl, fun h => absurd hcand h, fun _ => ⟨rfl, rfl, fun hl => ?_, fun _ hv => ?_⟩⟩
        · exact absurd (hl.symm.trans hcand) (by simp)
        · refine votesOk_record (fun _ j hj => ?_) rfl hv
          have hjn : j = n := nodeId_inj (hj.symm.trans hqs)
          subst hjn
          exact granted_self hc (by rw [hct]; exact hvote hty)
      · exact ⟨rfl, fun h => absurd hcand h, fun hr => absurd (hr.trans hcand)
          (by simp [psendMsgs, pwinState, pappend, pbecomeLeader])⟩
      · exact ⟨rfl, fun h => absurd hcand h, fun hr => absurd (hr.trans hcand)
          (by simp [pbecomeFollower])⟩
    · exact hrefl hh

/-- `Advance`'s run: the term kept, a non-candidate's role kept, and `QKeep` when the role is the
same at the end (a candidate that won or lost stays a leader or follower). -/
theorem quiet_adv_run {S : State} {n : Fin 3} {T : w64} {s s' : PState} {qs : List Msg}
    (hc : S.cfg = cfg3) (hct : S.currentTerm[n.val]! = uint.Z T)
    (hqs : ∀ q ∈ qs, QMsg S n T q) (h : AdvanceEnd cfgM3 (nodeId n) s qs s') (hT : s.term = T) :
    s'.term = s.term ∧ (s.role ≠ .candidate → s'.role = s.role) ∧
      (s'.role = s.role → QKeep S n s s') := by
  induction h with
  | nil => exact ⟨rfl, fun _ => rfl, fun _ => QKeep.refl⟩
  | cons s s1 s' q qs hr _ ih =>
    obtain ⟨ht1, hro1, hk1⟩ := quiet_adv_step hc hT hct (hqs q (List.mem_cons_self ..)) hr
    obtain ⟨ht2, hro2, hk2⟩ := ih (fun x hx => hqs x (List.mem_cons_of_mem _ hx)) (ht1.trans hT)
    refine ⟨ht2.trans ht1, fun hnc => ?_, fun hrr => ?_⟩
    · have h1 := hro1 hnc
      exact (hro2 (h1 ▸ hnc)).trans h1
    · by_cases hs1 : s1.role = .candidate
      · by_cases hs : s.role = .candidate
        · have e1 : s1.role = s.role := hs1.trans hs.symm
          have e2 : s'.role = s1.role := hrr.trans e1.symm
          exact (hk1 e1).trans (hk2 e2) e2.symm
        · exact absurd (hro1 hs ▸ hs1) hs
      · have e2 := hro2 hs1
        have e1 : s1.role = s.role := e2.symm.trans hrr
        exact (hk1 e1).trans (hk2 e2) e2.symm

/-- **A quiet step's state** (`Reach` to a state with the view's role, term and log): `QKeep` from
the view's state (received messages from another node: C4's `NetShape`). -/
theorem quiet_reach {S : State} {net : List Msg} {n : Fin 3} {v : NodeView} {ps₁ : PState}
    (hc : S.cfg = cfg3) (hnet : NetOk S net) (hv : NodeOk S net n v)
    (hr : Reach (nodeId n) net v ps₁)
    (hro : ps₁.role = v.ps.role) (ht : ps₁.term = v.ps.term) (hl : ps₁.log = v.ps.log) :
    QKeep S n v.ps ps₁ := by
  obtain ⟨hd, -, -, -, hqs, -, -⟩ := hv
  have hct : S.currentTerm[n.val]! = uint.Z v.ps.term := hd.1
  cases hr with
  | stay _ => exact QKeep.refl
  | input inp _ _ _ _ hm hs =>
    cases inp with
    | recv m =>
      obtain ⟨hmn, hmd, hm0⟩ := hm m rfl
      exact quiet_recv hc hnet hmn hmd (hnet.2.2 m hmn).2.1 hm0 hct hs hro ht hl
    | tick => exact quiet_tick hs ht
    | propose d => exact quiet_propose hs hl
  | advance _ _ _ _ ha =>
    refine (quiet_adv_run hc hct (fun q hq => ?_) ha rfl).2.2 hro
    obtain ⟨h1, h2, h3, h4, h5⟩ := hqs q hq
    refine ⟨⟨h1, h2, h3, h4, h5.imp (fun h => h.1) (fun h => h.1)⟩, fun hty => ?_, fun hty => ?_⟩
    · rcases h5 with h5 | h5
      · exact h5.2
      · rw [h5.1] at hty; cases hty
    · rcases h5 with h5 | h5
      · rw [h5.1] at hty; cases hty
      · exact h5.2

end quiet

end AntSim
end EtcdGrove
end Perennial
