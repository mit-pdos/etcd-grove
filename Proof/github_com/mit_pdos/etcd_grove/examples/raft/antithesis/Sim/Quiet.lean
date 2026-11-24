/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: the steps that report nothing (#33 S4)

`antSim_quiet`'s steps keep the node's role, term, log and commit (`Quiet`: an input noted, no
`Ready`, or a `Ready` the harness does not report). What they may move is a leader's `Match` (an
acknowledgement that commits nothing, its ack fact in `msgs` by C4 at the leader's term) and a
candidate's tally (a grant, its fact in `msgs` by C4; its own vote, in `votes` by `QsOk`): this file
shows `LeaderPart`'s and `CandPart`'s facts survive those steps (`MatchOk`, `VotesOk`), that the
leader hint is kept along `Reach` (`reach_leadOk`), that a silent `Ready` queues nothing for
`Advance` (`reach_selfFree`), and proves `antSim_quiet`.
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

/-! ## The leader hint along `Reach` -/

/-- Raft's leader hint at `s` (C1's `LeadOk`): a node that does not lead does not name itself. -/
def LeadHint (id : w64) (s : PState) : Prop := s.role ≠ .leader → s.lead ≠ id

theorem leadHint_pre {id : w64} {s s1 : PState} {m : Msg} (h : LeadHint id s) (hid : id ≠ W64 0)
    (hsrc : fromLeader m.ty = true → m.src ≠ id) (hp : PreEnd s m s1) : LeadHint id s1 := by
  rcases hp with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · intro _
    show (if fromLeader m.ty then m.src else W64 0) ≠ id
    split
    · rename_i hfl; exact hsrc hfl
    · exact Ne.symm hid
  · exact h

theorem leadHint_propose {id : w64} {s s' : PState} {m : Msg} (h : LeadHint id s)
    (hp : ProposeEnd id s m s') : LeadHint id s' := by
  unfold ProposeEnd at hp
  split at hp
  · rename_i hr
    rcases hp with rfl | ⟨es, ms, -, -, rfl⟩
    · exact h
    · intro h'; exact absurd hr h'
  · split at hp
    · subst hp; exact h
    · subst hp; exact h

/-- The type switch keeps the leader hint: the sender adopted as leader (`MsgApp`, `MsgHeartbeat`)
is another node; a lost election clears `lead`; a win makes the node leader. -/
theorem leadHint_handle {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (h : LeadHint id s)
    (hid : id ≠ W64 0)
    (hsc : m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp ∨ m.ty = .propose)
    (hsrc : m.src ≠ id ∨ m.ty = .appResp ∨ m.ty = .voteResp)
    (hh : HandleEnd c id s m s') : LeadHint id s' := by
  unfold HandleEnd at hh
  rcases hsc with hty | hty | hty | hty | hty | hty | hty <;> rw [hty] at hh <;> simp only at hh
  · rcases hh with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact h
  · split at hh
    · rcases hh with ⟨-, rfl⟩ | ⟨-, mt, ms, -, -, rfl⟩ | ⟨-, rfl⟩
      · exact h
      · intro h'; exact absurd rfl h'
      · exact fun _ => Ne.symm hid
    · subst hh; exact h
  · have hs : m.src ≠ id := hsrc.resolve_right (by rw [hty]; simp)
    split at hh
    · subst hh; exact h
    · rcases hh with ⟨-, rfl⟩ | ⟨-, _, _, -, rfl⟩ | ⟨-, -, _, _, -, -, rfl⟩ <;> exact fun _ => hs
  · split at hh
    · unfold AppRespEnd at hh
      rcases hh with ⟨-, rfl⟩ | ⟨-, -, ms, -, rfl⟩ | ⟨-, x, k, -, -, ms, -, rfl⟩ <;> exact h
    · subst hh; exact h
  · have hs : m.src ≠ id := hsrc.resolve_right (by rw [hty]; simp)
    split at hh
    · subst hh; exact h
    · subst hh; exact fun _ => hs
  · split at hh
    · obtain ⟨ms, -, rfl⟩ := hh; exact h
    · subst hh; exact h
  · exact leadHint_propose h hh

theorem leadHint_recv {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (h : LeadHint id s)
    (hid : id ≠ W64 0)
    (hsc : m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp ∨ m.ty = .propose)
    (hsrc : m.src ≠ id ∨ m.ty = .appResp ∨ m.ty = .voteResp)
    (hr : RecvEnd c id s m s') : LeadHint id s' := by
  rcases hr with ⟨-, hh⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, hh⟩
  · exact leadHint_handle h hid hsc hsrc hh
  · exact h
  · refine leadHint_handle (leadHint_pre h hid (fun hfl => ?_) hpre) hid hsc hsrc hh
    rcases hsrc with hs | hty | hty
    · exact hs
    · exact absurd hfl (by simp [hty, fromLeader])
    · exact absurd hfl (by simp [hty, fromLeader])

theorem leadHint_tick {c : CfgM} {id : w64} {s s' : PState} (h : LeadHint id s) (hid : id ≠ W64 0)
    (ht : TickEnd c id s s') : LeadHint id s' := by
  rcases ht with rfl | ⟨-, -, peers, cl, -, rfl⟩ | ⟨-, ms, -, rfl⟩
  · exact h
  · exact fun _ => Ne.symm hid
  · exact h

theorem leadHint_adv {c : CfgM} {id : w64} {s s' : PState} {qs : List Msg} (h : LeadHint id s)
    (hid : id ≠ W64 0) (hq : ∀ q ∈ qs, q.ty = .appResp ∨ q.ty = .voteResp)
    (ha : AdvanceEnd c id s qs s') : LeadHint id s' := by
  induction ha with
  | nil => exact h
  | cons s s1 s' q qs hr _ ih =>
    have hq0 := hq q (List.mem_cons_self ..)
    have hsc : q.ty = .vote ∨ q.ty = .voteResp ∨ q.ty = .app ∨ q.ty = .appResp ∨
        q.ty = .heartbeat ∨ q.ty = .heartbeatResp ∨ q.ty = .propose := by
      rcases hq0 with h0 | h0
      · exact .inr (.inr (.inr (.inl h0)))
      · exact .inr (.inl h0)
    exact ih (leadHint_recv h hid hsc (.inr hq0) hr) (fun x hx => hq x (List.mem_cons_of_mem _ hx))

/-- **The leader hint is kept along `Reach`** (C1's `LeadOk` at the state a `Ready` is taken at): a
received message is from another node (C4's `NetShape`), `Advance` steps only acknowledgements and
vote responses. -/
theorem reach_leadOk {S : State} {net : List Msg} {n : Fin 3} {v : NodeView} {ps₁ : PState}
    (hnet : NetOk S net) (hv : NodeOk S net n v) (hr : Reach (nodeId n) net v ps₁) :
    LeadHint (nodeId n) ps₁ := by
  obtain ⟨-, -, -, -, hqs, -, -, hlo⟩ := hv
  have hid := nodeId_ne_zero n
  cases hr with
  | stay _ => exact hlo
  | input inp _ _ _ _ hm hs =>
    cases inp with
    | recv m =>
      obtain ⟨hmn, hmd, -⟩ := hm m rfl
      have hsd : m.src ≠ nodeId n := hmd ▸ (hnet.2.2 m hmn).2.1
      exact leadHint_recv hlo hid (hnet.1 m hmn).1 (.inl hsd) hs
    | tick => exact leadHint_tick hlo hid hs
    | propose d => exact leadHint_propose hlo hs
  | advance _ _ _ _ ha =>
    refine leadHint_adv hlo hid (fun q hq => ?_) ha
    obtain ⟨-, -, -, -, h5⟩ := hqs q hq
    exact h5.imp (fun h => h.1) (fun h => h.1)

/-! ## No self-addressed message at a quiet step's state -/

/-- No message of `s`'s outbox is to the node itself. -/
def SelfFree (id : w64) (s : PState) : Prop := ∀ q ∈ s.outbox, q.dst ≠ id

theorem selfFree_psend {id : w64} {s : PState} {ms : List Msg} (hX : SelfFree id s)
    (hms : ∀ x ∈ ms, x.dst ≠ id) : SelfFree id (psendMsgs s ms) := by
  intro q hq
  rw [psendMsgs_outbox] at hq
  rcases List.mem_append.mp hq with hq | hq
  · exact hX q hq
  · exact hms q hq

theorem selfFree_one {id : w64} {s : PState} {q : Msg} (hX : SelfFree id s) (hq : q.dst ≠ id) :
    SelfFree id (psendMsgs s [q]) :=
  selfFree_psend hX fun x hx => by rw [List.mem_singleton.mp hx]; exact hq

theorem selfFree_sends {id : w64} {s s' : PState} (h : SendsEnd id s s') (hX : SelfFree id s) :
    SelfFree id s' := by
  obtain ⟨ms, hms, rfl⟩ := h
  exact selfFree_psend hX fun x hx => (hms x hx).1.2.2.2.1

/-- The type switch at a state with the role kept queues nothing to the node itself: the answers
are to the sender (another node), a leader's appends to other nodes (`AppOk`); a win (the only
arm queueing a self-acknowledgement, besides a proposal) changes the role. -/
theorem selfFree_handle {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (hX : SelfFree id s)
    (hsc : m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp ∨ m.ty = .propose)
    (hnp : m.ty ≠ .propose) (hsrc : m.src ≠ id) (hro : s'.role = s.role)
    (hh : HandleEnd c id s m s') : SelfFree id s' := by
  unfold HandleEnd at hh
  rcases hsc with hty | hty | hty | hty | hty | hty | hty <;> rw [hty] at hh <;> simp only at hh
  · rcases hh with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
    · exact selfFree_one hX hsrc
    · exact selfFree_one hX hsrc
  · split at hh
    · rename_i hcand
      rcases hh with ⟨-, rfl⟩ | ⟨-, mt, ms, -, -, rfl⟩ | ⟨-, rfl⟩
      · exact hX
      · exact absurd (hro.trans hcand) (by simp [psendMsgs, pwinState, pappend, pbecomeLeader])
      · exact hX
    · subst hh; exact hX
  · split at hh
    · subst hh; exact hX
    · rcases hh with ⟨-, rfl⟩ | ⟨-, _, _, -, rfl⟩ | ⟨-, -, _, _, -, -, rfl⟩
      · exact selfFree_one hX hsrc
      · exact selfFree_one hX hsrc
      · exact selfFree_one hX hsrc
  · split at hh
    · unfold AppRespEnd at hh
      rcases hh with ⟨-, rfl⟩ | ⟨-, -, hs⟩ | ⟨-, x, k, -, -, hs⟩
      · exact hX
      · exact selfFree_sends hs hX
      · exact selfFree_sends hs hX
    · subst hh; exact hX
  · split at hh
    · subst hh; exact hX
    · subst hh; exact selfFree_one hX hsrc
  · split at hh
    · exact selfFree_sends hh hX
    · subst hh; exact hX
  · exact absurd hty hnp

theorem selfFree_recv {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (hX : SelfFree id s)
    (hsc : m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp ∨ m.ty = .propose)
    (hnp : m.ty ≠ .propose) (hsrc : m.src ≠ id) (hm0 : m.term ≠ W64 0)
    (hro : s'.role = s.role) (ht : s'.term = s.term) (hr : RecvEnd c id s m s') :
    SelfFree id s' := by
  rcases hr with ⟨h0, -⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, hh⟩
  · exact absurd h0 hm0
  · exact hX
  · have ht' := handle_term hsc hh
    rcases hpre with ⟨hlt, rfl⟩ | ⟨-, rfl⟩
    · have : s'.term = m.term := ht'
      rw [this] at ht; rw [ht] at hlt; exact absurd hlt (Int.lt_irrefl _)
    · exact selfFree_handle hX hsc hnp hsrc hro hh

theorem selfFree_tick {c : CfgM} {id : w64} {s s' : PState} (hX : SelfFree id s)
    (ht : s'.term = s.term) (h : TickEnd c id s s') : SelfFree id s' := by
  rcases h with rfl | ⟨-, -, peers, cl, -, rfl⟩ | ⟨-, ms, hms, rfl⟩
  · exact hX
  · exact absurd ht (w64_succ_ne _)
  · exact selfFree_psend hX fun x hx => (hms x hx).1.2.2.2.1

/-- A proposal that keeps the log queues nothing to the node itself: a leader's batch is never
empty, a forward goes to the leader (another node, the leader hint). -/
theorem selfFree_propose {id : w64} {s s' : PState} {m : Msg} (hX : SelfFree id s)
    (hlead : LeadHint id s) (hne : m.entries ≠ []) (hl : s'.log = s.log)
    (h : ProposeEnd id s m s') : SelfFree id s' := by
  unfold ProposeEnd at h
  split at h
  · rcases h with rfl | ⟨es, ms, hrep, -, rfl⟩
    · exact hX
    · exfalso
      have h1 := congrArg List.length hl
      simp only [psendMsgs, pappend, List.length_append, List.length_mapIdx, hrep.length] at h1
      exact hne (List.eq_nil_of_length_eq_zero (by omega))
  · split at h
    · rename_i hc
      subst h
      exact selfFree_one hX (hlead (by rw [hc.1]; decide))
    · subst h; exact hX

/-- What `Advance`'s steps keep from a state of role `r0`: the candidate role only from a
candidate's start, and a message to the node itself queued only once a candidate's start has
left the candidate role (its win's self-acknowledgement). -/
def AdvSelf (id : w64) (r0 : Role) (s : PState) : Prop :=
  (s.role = .candidate → r0 = .candidate) ∧
  ∀ q ∈ s.outbox, q.dst = id → r0 = .candidate ∧ s.role ≠ .candidate

theorem advSelf_sends {id : w64} {r0 : Role} {s s' : PState} (h : SendsEnd id s s')
    (hi : AdvSelf id r0 s) : AdvSelf id r0 s' := by
  obtain ⟨ms, hms, rfl⟩ := h
  refine ⟨hi.1, fun q hq hd => ?_⟩
  rw [psendMsgs_outbox] at hq
  rcases List.mem_append.mp hq with hq | hq
  · exact hi.2 q hq hd
  · exact absurd hd (hms q hq).1.2.2.2.1

theorem advSelf_handle {c : CfgM} {id : w64} {r0 : Role} {s s' : PState} {q : Msg}
    (hi : AdvSelf id r0 s) (hty : q.ty = .appResp ∨ q.ty = .voteResp)
    (hh : HandleEnd c id s q s') : AdvSelf id r0 s' := by
  unfold HandleEnd at hh
  rcases hty with hty | hty <;> rw [hty] at hh <;> simp only at hh
  · split at hh
    · unfold AppRespEnd at hh
      rcases hh with ⟨-, rfl⟩ | ⟨-, -, hs⟩ | ⟨-, x, k, -, -, hs⟩
      · exact hi
      · exact advSelf_sends hs hi
      · exact advSelf_sends hs hi
    · subst hh; exact hi
  · split at hh
    · rename_i hcand
      have hr0 := hi.1 hcand
      rcases hh with ⟨-, rfl⟩ | ⟨-, mt, ms, -, -, rfl⟩ | ⟨-, rfl⟩
      · exact hi
      · exact ⟨fun h => absurd h (by simp [psendMsgs, pwinState, pappend, pbecomeLeader]),
          fun _ _ _ => ⟨hr0, by simp [psendMsgs, pwinState, pappend, pbecomeLeader]⟩⟩
      · exact ⟨fun h => absurd h (by simp [pbecomeFollower]),
          fun _ _ _ => ⟨hr0, by simp [pbecomeFollower]⟩⟩
    · subst hh; exact hi

theorem advSelf_step {c : CfgM} {id : w64} {r0 : Role} {s s1 : PState} {q : Msg}
    (hi : AdvSelf id r0 s) (hty : q.ty = .appResp ∨ q.ty = .voteResp)
    (h : RecvEnd c id s q s1) : AdvSelf id r0 s1 := by
  rcases h with ⟨-, hh⟩ | ⟨-, -, rfl⟩ | ⟨-, s2, hpre, hh⟩
  · exact advSelf_handle hi hty hh
  · exact hi
  · rcases hpre with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · have hi' : AdvSelf id r0
          (pbecomeFollower s q.term (if fromLeader q.ty then q.src else W64 0)) :=
        ⟨fun h => absurd h (by simp [pbecomeFollower]),
          fun q' hq hd => ⟨(hi.2 q' hq hd).1, by simp [pbecomeFollower]⟩⟩
      exact advSelf_handle hi' hty hh
    · exact advSelf_handle hi hty hh

theorem advSelf_run {c : CfgM} {id : w64} {r0 : Role} {s s' : PState} {qs : List Msg}
    (h : AdvanceEnd c id s qs s') (hq : ∀ q ∈ qs, q.ty = .appResp ∨ q.ty = .voteResp)
    (hi : AdvSelf id r0 s) : AdvSelf id r0 s' := by
  induction h with
  | nil => exact hi
  | cons s s1 s' q qs hr _ ih =>
    exact ih (fun x hx => hq x (List.mem_cons_of_mem _ hx))
      (advSelf_step hi (hq q (List.mem_cons_self ..)) hr)

/-- **A state reached with the view's role, term and log has nothing to the node itself in its
outbox** (so a silent `Ready`'s `qs` is empty): an input's answers are to other nodes (C4's
`NetShape`; a received message is never a proposal, its term not `0`), a campaign changes the
term, a win the role, a proposal the log; a forward goes to the leader (the leader hint);
`Advance` queues a self-acknowledgement only at a candidate's win. -/
theorem reach_selfFree {S : State} {net : List Msg} {n : Fin 3} {v : NodeView} {ps₁ : PState}
    (hnet : NetOk S net) (hv : NodeOk S net n v) (hr : Reach (nodeId n) net v ps₁)
    (hro : ps₁.role = v.ps.role) (ht : ps₁.term = v.ps.term) (hl : ps₁.log = v.ps.log) :
    SelfFree (nodeId n) ps₁ := by
  obtain ⟨hd, -, -, -, hqs, -, -, hlo⟩ := hv
  have hX0 : v.ps.outbox = [] := hd.2.2.2.2.2.2.1
  have hX : SelfFree (nodeId n) v.ps := fun q hq => by rw [hX0] at hq; cases hq
  cases hr with
  | stay _ => exact hX
  | input inp _ _ _ _ hm hs =>
    cases inp with
    | recv m =>
      obtain ⟨hmn, hmd, hm0⟩ := hm m rfl
      obtain ⟨-, hsd, hpt⟩ := hnet.2.2 m hmn
      have hsd' : m.src ≠ nodeId n := hmd ▸ hsd
      exact selfFree_recv hX (hnet.1 m hmn).1 (fun hp => hm0 (hpt hp)) hsd' hm0 hro ht hs
    | tick => exact selfFree_tick hX ht hs
    | propose d => exact selfFree_propose hX hlo (by simp [propMsg]) hl hs
  | advance _ _ _ _ ha =>
    have hty : ∀ q ∈ v.qs, q.ty = .appResp ∨ q.ty = .voteResp := fun q hq => by
      obtain ⟨-, -, -, -, h5⟩ := hqs q hq
      exact h5.imp (fun h => h.1) (fun h => h.1)
    have hfin := advSelf_run ha hty
      (⟨fun h => h, fun q hq => by rw [hX0] at hq; cases hq⟩ : AdvSelf (nodeId n) v.ps.role v.ps)
    exact fun q hq hdq => (hfin.2 q hq hdq).2 (hro.trans (hfin.2 q hq hdq).1)

/-! ## `antSim_quiet` -/

/-- A `Ready` the harness does not report is at the view's role, term, vote, commit and log. -/
theorem silent_eq {id : w64} {v : NodeView} {ps : PState} {rd : ReadyD}
    (hro : ReadyOutP id v ps rd) (hs : ¬ Reported v rd) :
    ps.role = v.ps.role ∧ ps.term = v.ps.term ∧ ps.vote = v.ps.vote ∧ ps.commit = v.ps.commit ∧
      ps.log = v.ps.log := by
  obtain ⟨hr, ht, hv, hc, hnil, -⟩ := hro
  have h1 : rd.term = v.ps.term := Classical.byContradiction fun h => hs (.inl h)
  have h2 : rd.vote = v.ps.vote := Classical.byContradiction fun h => hs (.inr (.inl h))
  have h3 : rd.commit = v.ps.commit := Classical.byContradiction fun h => hs (.inr (.inr (.inl h)))
  have h4 : rd.ents = [] := Classical.byContradiction fun h => hs (.inr (.inr (.inr (.inl h))))
  have h5 : rd.role = v.ps.role := Classical.byContradiction fun h => hs (.inr (.inr (.inr (.inr h))))
  exact ⟨hr.symm.trans h5, ht.symm.trans h1, hv.symm.trans h2, hc.symm.trans h3, hnil h4⟩

/-- Nothing of a `Ready` is pending at a state `Reach` starts from. -/
theorem reach_pend {id : w64} {net : List Msg} {v : NodeView} {ps₁ : PState}
    (hr : Reach id net v ps₁) : v.pend = [] := by
  cases hr with
  | stay hi => exact hi.2.1
  | input _ _ hi _ _ _ _ => exact hi.2.1
  | advance _ hp _ _ _ => exact hp

theorem durableIs_of {S : State} {n : Fin 3} {v w : NodeView} (h : DurableIs S n v)
    (hr : w.ps.role = v.ps.role) (ht : w.ps.term = v.ps.term) (hvo : w.ps.vote = v.ps.vote)
    (hc : w.ps.commit = v.ps.commit) (hl : w.ps.log = v.ps.log) (hdl : w.delivered = v.delivered)
    (hX : w.ps.outbox = []) (hb : w.ps.base = base0)
    (hpre : w.delivered ++ w.ce <+: w.ps.log)
    (hlen : (w.delivered ++ w.ce).length ≤ uint.nat w.ps.commit) : DurableIs S n w := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -, -, h9, h10, h11, -, -⟩ := h
  refine ⟨by rw [ht]; exact h1, by rw [hvo]; exact h2, by rw [hl]; exact h3, by rw [hc]; exact h4,
    by rw [hr]; exact h5, by rw [hdl]; exact h6, hX, hb, by rw [hl]; exact h9, h10, h11, hpre, hlen⟩

theorem leaderPart_of {S : State} {n : Fin 3} {v w : NodeView} (h : LeaderPart S n v)
    (hr : w.ps.role = v.ps.role) (ht : w.ps.term = v.ps.term) (hl : w.ps.log = v.ps.log)
    (hm : v.ps.role = .leader → MatchOk S n v.ps → MatchOk S n w.ps) : LeaderPart S n w := by
  intro hlead
  have hlv : v.ps.role = .leader := hr.symm.trans hlead
  obtain ⟨h1, h2, h3, h4, h5⟩ := h hlv
  obtain ⟨h3', h4'⟩ := hm hlv ⟨h3, h4⟩
  refine ⟨by rw [ht]; exact h1, by rw [ht, hl]; exact h2, h3', h4', ?_⟩
  unfold LeaderConfOk at *; rw [ht, hl]; exact h5

theorem candPart_of {S : State} {n : Fin 3} {v w : NodeView} (h : CandPart S n v)
    (hr : w.ps.role = v.ps.role)
    (hm : v.ps.role = .candidate → VotesOk S n v.ps → VotesOk S n w.ps) : CandPart S n w := by
  intro hc
  have hcv : v.ps.role = .candidate := hr.symm.trans hc
  obtain ⟨h1, h2⟩ := h hcv
  exact ⟨hm hcv h1, h2⟩

/-- **A quiet step keeps the node's part of the relation** (`NodeOk`): an input noted changes
only the drain's `by` and cause (the message sent to it); a state with no `Ready` or a silent
one keeps the durable part (role, term, vote, commit, log), `QKeep` the leader's and candidate's
parts, the leader hint is kept along `Reach`, the silent `Ready`'s messages are `PendOk`
(`pendOk_of_reach`) and none is to the node itself (`reach_selfFree`: `qs` empty). -/
theorem nodeOk_quiet {S : State} {net : List Msg} {n : Fin 3} {v v' : NodeView}
    (hcf : S.cfg = cfg3) (hnet : NetOk S net) (hv : NodeOk S net n v)
    (hq : Quiet (nodeId n) net v v') : NodeOk S net n v' := by
  cases hq with
  | input inp hidle hin =>
    obtain ⟨hd, hlp, hcp, -, -, -, -, hlo⟩ := hv
    refine ⟨hd, hlp, hcp, fun q hq => ?_, fun q hq => ?_, fun h => ?_, fun m hm => ?_, hlo⟩
    · have hq' : q ∈ v.pend := hq
      rw [hidle.2.1] at hq'; cases hq'
    · have hq' : q ∈ v.qs := hq
      rw [hidle.1] at hq'; cases hq'
    · simp [NodeView.noteInput] at h
    · cases inp with
      | recv m' =>
        have hmm : m' = m := Option.some.inj hm
        subst hmm; exact hin m' rfl
      | tick => simp [NodeView.noteInput, Input.cause] at hm
      | propose d => simp [NodeView.noteInput, Input.cause] at hm
  | noReady ps₁ hr hX ht hvo hc hro hl =>
    have hk := quiet_reach hcf hnet hv hr hro ht hl
    have hpe := reach_pend hr
    have hlead := reach_leadOk hnet hv hr
    obtain ⟨hd, hlp, hcp, -, -, htold, hcause, -⟩ := hv
    have hpre : v.delivered ++ v.ce <+: ps₁.log := by
      rw [hl]; exact hd.2.2.2.2.2.2.2.2.2.2.2.1
    have hlen : (v.delivered ++ v.ce).length ≤ uint.nat ps₁.commit := by
      rw [hc]; exact hd.2.2.2.2.2.2.2.2.2.2.2.2
    refine ⟨durableIs_of hd hro ht hvo hc hl rfl hX (hk.1.trans hd.2.2.2.2.2.2.2.1) hpre hlen,
      leaderPart_of hlp hro ht hl (fun hr' hm => hk.2.2.1 (hro.trans hr') hm),
      candPart_of hcp hro (fun hr' hm => hk.2.2.2 (hro.trans hr') hm),
      fun q hq => ?_, (fun q hq => by have : q ∈ ([] : List Msg) := hq; cases this), htold, hcause,
      hlead⟩
    have hq' : q ∈ v.pend := hq
    rw [hpe] at hq'; cases hq'
  | silentReady ps₁ rd hr hro hs =>
    obtain ⟨hR, hT, hV, hC, hL⟩ := silent_eq hro hs
    have hk := quiet_reach hcf hnet hv hr hR hT hL
    have hsf := reach_selfFree hnet hv hr hR hT hL
    have hpend := pendOk_of_reach hnet hv hr hro
    have hlead := reach_leadOk hnet hv hr
    obtain ⟨hd, hlp, hcp, -, -, htold, hcause, -⟩ := hv
    obtain ⟨-, -, -, -, -, -, hqp, -, hpre, hlen, hb, -, -⟩ := hro
    have hf : ps₁.outbox.filter (fun q => decide (q.dst = nodeId n)) = [] :=
      List.filter_eq_nil_iff.mpr fun q hq => by simpa using hsf q hq
    rw [hf] at hqp
    have hqs : rd.qs = [] := hqp.eq_nil
    refine ⟨durableIs_of hd hR hT hV hC hL rfl rfl hb hpre hlen,
      leaderPart_of hlp hR hT hL (fun hr' hm => hk.2.2.1 (hR.trans hr') hm),
      candPart_of hcp hR (fun hr' hm => hk.2.2.2 (hR.trans hr') hm),
      hpend, fun q hq => ?_, htold, hcause, hlead⟩
    have hq' : q ∈ rd.qs := hq
    rw [hqs] at hq'; cases hq'

/-- **`antSim_quiet`**: the steps that report nothing keep the relation, `S` unchanged. -/
theorem antSim_quiet : antSim_quiet.stmt := by
  intro S V net G n v' hsim _ _ hq
  obtain ⟨hsh, hb, hnet, hall⟩ := hsim
  refine ⟨hsh, hb, hnet, fun j => ?_⟩
  unfold setV
  by_cases hj : j = n
  · subst hj; simp only [↓reduceIte]; exact nodeOk_quiet hsh.1 hnet (hall j) hq
  · simp only [hj, ↓reduceIte]; exact hall j

end quiet

end AntSim
end EtcdGrove
end Perennial
