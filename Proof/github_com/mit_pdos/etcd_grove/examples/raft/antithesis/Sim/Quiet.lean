/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: the steps that report nothing (#33 S4)

`antSim_quiet`'s steps keep the node's role, term, log and commit (`Quiet`: an input noted, no
`Ready`, or a `Ready` the harness does not report). What they may move is a leader's `Match` (an
acknowledgement that commits nothing, its ack fact in `msgs` by C4 at the leader's term) and a
candidate's tally (a grant, its fact in `msgs` by C4; its own vote, in `votes` by `QsOk`): this file
shows `LeaderPart`'s and `CandPart`'s facts survive those steps (`MatchOk`, `VotesOk`), that a
silent `Ready` queues for `Advance` at most a pre-candidate's self pre-vote (`reach_selfPre`), and
proves `antSim_quiet_in` (parity B1: over `QuietIn` for the masks below `mskB1p`; the leader hint along `Reach` is `Outbox.lean`'s
`reach_leadOk`, the configuration, ghost prefix and a leader's read-only queue `MsgShape.lean`'s
`reach_keep`, `reach_roOk`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Outbox
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.SendRel
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.MsgShape

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
theorem granted_grant {R : RunCfg} {S : State} (hc : S.cfg = R.cfg) {n j : Fin R.N} (hne : j ≠ n)
    (h : grantF (nameOf (nodeId j)) (nameOf (nodeId n)) (S.currentTerm[n.val]!) ∈ S.msgs) :
    (S.granted n.val).has (nameOf (nodeId j)) = true := by
  unfold State.granted
  simp only [SSet.has, List.contains_iff_mem]
  rw [server_of hc n]
  have hmem : nameOf (nodeId j) ∈ S.cfg.server := by
    have := server_has j
    rw [hc, R.server_eq]; simpa [SSet.has] using this
  have hne' : nameOf (nodeId j) ≠ nameOf (nodeId n) := fun h' => hne (name_inj h')
  have hf := mem_foldl_setAdd (P := fun j' => (j' != nameOf (nodeId n) &&
      S.msgs.contains (grantF j' (nameOf (nodeId n)) (S.currentTerm[n.val]!))) = true)
      (nameOf (nodeId j)) S.cfg.server []
      (.inr ⟨hmem, by simp only [Bool.and_eq_true, bne_iff_ne, List.contains_iff_mem]; exact ⟨hne', h⟩⟩)
  split
  · exact mem_setAdd.mpr (.inl hf)
  · exact hf

/-- A node's own vote at its term, in `votes`, puts it in `Granted(n)` (R 280). -/
theorem granted_self {R : RunCfg} {S : State} (hc : S.cfg = R.cfg) {n : Fin R.N}
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
variable {cf : CfgM} {R : RunCfg} {kk : NodeK}

/-! ## What a quiet step keeps -/

/-- `LeaderPart`'s `Match` facts at a state `s`. -/
def MatchOk (S : State) (n : Fin R.N) (s : PState) : Prop :=
  (∀ (j : Fin R.N) (k : w64), uint.Z k ≤ uint.Z (matchOf s (nodeId j)) →
      plogTermAt s.base s.log k = some s.term →
      AckIn S (nameOf (nodeId j)) (nameOf (nodeId n)) (uint.Z s.term) (uint.Z k)) ∧
  (∀ j : Fin R.N, j ≠ n → matchOf s (nodeId j) = W64 0 ∨
      AckIn S (nameOf (nodeId j)) (nameOf (nodeId n)) (uint.Z s.term)
        (uint.Z (matchOf s (nodeId j))))

/-- `CandPart`'s tally facts at a state `s`. -/
def VotesOk (S : State) (n : Fin R.N) (s : PState) : Prop :=
  ∀ j : Fin R.N, s.votes !! nodeId j = some true → (S.granted n.val).has (nameOf (nodeId j)) = true

/-- What a step from `s` to `s'` that keeps the role keeps: the base, the term, and (for a leader)
the `Match` facts, (for a candidate) the tally facts. -/
def QKeep (S : State) (n : Fin R.N) (s s' : PState) : Prop :=
  s'.base = s.base ∧ s'.term = s.term ∧
  (s'.role = .leader → MatchOk S n s → MatchOk S n s') ∧
  (s'.role = .candidate → VotesOk S n s → VotesOk S n s')

theorem QKeep.same {S : State} {n : Fin R.N} {s s' : PState} (hb : s'.base = s.base)
    (ht : s'.term = s.term) (hl : s'.log = s.log) (hm : s'.matched = s.matched)
    (hv : s'.votes = s.votes) : QKeep S n s s' := by
  refine ⟨hb, ht, fun _ h => ?_, fun _ h => ?_⟩
  · unfold MatchOk matchOf at *; rw [ht, hl, hm, hb]; exact h
  · unfold VotesOk at *; rw [hv]; exact h

theorem QKeep.refl {S : State} {n : Fin R.N} {s : PState} : QKeep S n s s :=
  QKeep.same rfl rfl rfl rfl rfl

theorem QKeep.trans {S : State} {n : Fin R.N} {s s1 s' : PState} (h1 : QKeep S n s s1)
    (h2 : QKeep S n s1 s') (hr1 : s1.role = s'.role) : QKeep S n s s' :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, fun hr h => h2.2.2.1 hr (h1.2.2.1 (hr1 ▸ hr) h),
    fun hr h => h2.2.2.2 hr (h1.2.2.2 (hr1 ▸ hr) h)⟩

theorem AckIn.le {S : State} {src dst : Str} {t k k' : Int} (h : AckIn S src dst t k)
    (hk : k' ≤ k) : AckIn S src dst t k' := by
  obtain ⟨a, ha, h1, h2, h3, h4, h5⟩ := h; exact ⟨a, ha, h1, h2, h3, h4, Int.le_trans hk h5⟩

/-- An acknowledgement raising `Match` of `src` (`MaybeUpdate`) keeps the `Match` facts, its ack
fact at the leader's term in `msgs` when it raises it. -/
theorem matchOk_raise {S : State} {n i : Fin R.N} {s s' : PState} {src x idx : w64}
    (hsrc : src = nodeId i) (hx : s.matched !! src = some x)
    (hack : uint.Z x < uint.Z idx →
      AckIn S (nameOf src) (nameOf (nodeId n)) (uint.Z s.term) (uint.Z idx))
    (ht : s'.term = s.term) (hl : s'.log = s.log) (hb : s'.base = s.base)
    (hm : s'.matched = <[src := if uint.Z x < uint.Z idx then idx else x]> s.matched)
    (h : MatchOk S n s) : MatchOk S n s' := by
  have hmo : ∀ j : Fin R.N, matchOf s' (nodeId j) =
      if nodeId j = src then (if uint.Z x < uint.Z idx then idx else x) else matchOf s (nodeId j) := by
    intro j
    unfold matchOf; rw [hm]
    by_cases hj : nodeId j = src
    · rw [if_pos hj, hj, lookup_insert]; rfl
    · rw [if_neg hj, lookup_insert_ne _ _ (Ne.symm hj)]
  have hxo : matchOf s src = x := by unfold matchOf; rw [hx]; rfl
  obtain ⟨h3, h4⟩ := h
  refine ⟨fun j k hk hkt => ?_, fun j hj => ?_⟩
  · rw [ht, hl, hb] at *
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
theorem votesOk_record {S : State} {n : Fin R.N} {s s' : PState} {src : w64} {b : Bool}
    (hg : b = true → ∀ j : Fin R.N, src = nodeId j → (S.granted n.val).has (nameOf (nodeId j)) = true)
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

/-- The type switch keeps the term (`HandleEndO`: no arm changes it). -/
theorem handle_term {c : CfgM} {id : w64} {s s' : PState} {m : Msg}
    (hsc : m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp ∨ m.ty = .propose)
    (h : HandleEndO kk c id s m s') : s'.term = s.term := by
  unfold HandleEndO at h
  rcases hsc with hty | hty | hty | hty | hty | hty | hty <;> rw [hty] at h <;> simp only at h
  · rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> rfl
  · split at h
    · rcases h with ⟨-, rfl⟩ | ⟨-, mt, ms, -, -, rfl⟩ | ⟨-, rfl⟩ <;> rfl
    · subst h; rfl
  · split at h
    · subst h; rfl
    · rcases h with ⟨-, rfl⟩ | ⟨-, _, _, -, rfl⟩ | ⟨-, -, _, _, -, -, rfl⟩ <;> rfl
  · split at h
    · unfold AppRespEndO at h
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
theorem quiet_handle {S : State} {net : List Msg} {n : Fin R.N} {s s' : PState} {m : Msg}
    (hc : S.cfg = R.cfg) (hnet : NetOk R S net) (hm : m ∈ net) (hmd : m.dst = nodeId n)
    (hsd : m.src ≠ m.dst) (hct : S.currentTerm[n.val]! = uint.Z s.term) (hmt : m.term = s.term)
    (hsc : m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp ∨ m.ty = .propose)
    (h : HandleEndO kk cf (nodeId n) s m s') (hr : s'.role = s.role) (hl : s'.log = s.log) :
    QKeep S n s s' := by
  obtain ⟨-, ⟨i, hsi, -⟩, j, hdj, hj⟩ := hnet.1 m hm
  have hjn : j = n := nodeId_inj (hdj.symm.trans hmd)
  subst hjn
  have hf := hj (by rw [hct, hmt]; exact Int.le_refl _)
  unfold HandleEndO at h
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
      unfold AppRespEndO at h
      rcases h with ⟨-, rfl⟩ | ⟨-, -, ms, -, rfl⟩ | ⟨hrj, x, c, hx, -, ms, -, rfl⟩
      · exact QKeep.refl
      · exact QKeep.same rfl rfl rfl rfl rfl
      · refine ⟨rfl, rfl, fun _ hmo => ?_, fun hl' => absurd (hl'.symm.trans hlead) (by simp [padoptLeader, psendMsgs, pwinState, pappend, pbecomeLeader, pbecomeFollower])⟩
        refine matchOk_raise hsi hx (fun hlt => ?_) rfl rfl rfl rfl hmo
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

/-- **A received message's step (`RecvEndO`, its term not `0`) that keeps the role, the term and
the log keeps `QKeep`**: a higher term's preamble would change the term (the type switch keeps the
preamble's), so the message is at the node's term. -/
theorem quiet_recv {S : State} {net : List Msg} {n : Fin R.N} {s s' : PState} {m : Msg}
    (hc : S.cfg = R.cfg) (hnet : NetOk R S net) (hm : m ∈ net) (hmd : m.dst = nodeId n)
    (hsd : m.src ≠ m.dst) (hm0 : m.term ≠ W64 0) (hct : S.currentTerm[n.val]! = uint.Z s.term)
    (hsc : m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp ∨ m.ty = .propose)
    (h : RecvEndO kk cf (nodeId n) s m s') (hr : s'.role = s.role) (ht : s'.term = s.term)
    (hl : s'.log = s.log) : QKeep S n s s' := by
  rcases h with ⟨h0, -⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, hh⟩
  · exact absurd h0 hm0
  · exact QKeep.refl
  · have ht' := handle_term hsc hh
    rcases hpre with ⟨hlt, rfl⟩ | ⟨hmt, rfl⟩
    · have : s'.term = m.term := ht'
      rw [this] at ht; rw [ht] at hlt; exact absurd hlt (Int.lt_irrefl _)
    · exact quiet_handle hc hnet hm hmd hsd hct hmt hsc hh hr hl

/-! ## A tick, a proposal, `Advance` -/

theorem w64_succ_ne (x : w64) : x + W64 1 ≠ x := by
  intro h
  have h2 := congrArg uint.Z h
  have := uint_Z_nonneg x
  word

/-- A tick that keeps the term: nothing, or a leader's heartbeats. -/
theorem quiet_tick {c : CfgM} {id : w64} {S : State} {n : Fin R.N} {s s' : PState}
    (h : TickEndO kk c id s s') (ht : s'.term = s.term) : QKeep S n s s' := by
  rcases h with rfl | ⟨-, -, peers, cl, -, rfl⟩ | ⟨-, ms, -, rfl⟩
  · exact QKeep.refl
  · exact absurd ht (w64_succ_ne _)
  · exact QKeep.same rfl rfl rfl rfl rfl

/-- A proposal that keeps the log: dropped, an empty batch, or forwarded. -/
theorem quiet_propose {id : w64} {S : State} {n : Fin R.N} {s s' : PState} {m : Msg}
    (h : ProposeEnd cf id s m s') (hl : s'.log = s.log) : QKeep S n s s' := by
  unfold ProposeEnd at h
  split at h
  · rcases h with rfl | ⟨es, ms, -, -, rfl⟩
    · exact QKeep.refl
    · exact QKeep.same rfl rfl hl rfl rfl
  · split at h
    · subst h; exact QKeep.same rfl rfl rfl rfl rfl
    · subst h; exact QKeep.refl

/-- `RecvEndP` keeps `QKeep` when it keeps the term: the answers keep the state, a step-down makes a
follower; a campaign would change the term. -/
theorem quiet_recvP {c : CfgM} {id : w64} {S : State} {n : Fin R.N} {s s' : PState} {m : Msg}
    (ht : s'.term = s.term) (h : RecvEndP kk c id s m s') : QKeep S n s s' := by
  rcases h with ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ |
      ⟨-, -, -, rfl⟩ | ⟨-, rfl | ⟨-, -, -, hcs⟩⟩
  · exact QKeep.same rfl rfl rfl rfl rfl
  · exact QKeep.same rfl rfl rfl rfl rfl
  · exact QKeep.refl
  · exact QKeep.same rfl rfl rfl rfl rfl
  · exact QKeep.same rfl rfl rfl rfl rfl
  · exact ⟨rfl, ht, fun h => by simp [pbecomeFollower] at h, fun h => by simp [pbecomeFollower] at h⟩
  · exact QKeep.refl
  · obtain ⟨peers, -, rfl⟩ := hcs; exact absurd ht (w64_succ_ne _)

/-- `TickEndP` keeps `QKeep`: a pre-candidate and a stepped-down leader are followers. -/
theorem quiet_tickP {c : CfgM} {id : w64} {S : State} {n : Fin R.N} {s s' : PState}
    (h : TickEndP kk c id s s') : QKeep S n s s' := by
  rcases h with ⟨-, -, -, peers, -, rfl⟩ | ⟨-, -, rfl⟩
  · exact ⟨rfl, rfl, fun h => by simp [psendMsgs] at h, fun h => by simp [psendMsgs] at h⟩
  · exact ⟨rfl, rfl, fun h => by simp [pbecomeFollower] at h, fun h => by simp [pbecomeFollower] at h⟩

/-- What `QsOk` says of a self-addressed message `Advance` steps at term `T`. -/
def QMsg (S : State) (n : Fin R.N) (T : w64) (q : Msg) : Prop :=
  SelfMsg (nodeId n) T q ∧
  (q.ty = .appResp → AckIn S (nameOf (nodeId n)) (nameOf (nodeId n)) (uint.Z T) (uint.Z q.index)) ∧
  (q.ty = .voteResp →
    ({ voter := nameOf (nodeId n), term := uint.Z T, cand := nameOf (nodeId n) } : VoteRec) ∈ S.votes)

/-- One step of `Advance`: the term kept, a non-candidate's role kept, and `QKeep` when the role is
kept (the self-acknowledgement's ack fact and the self-vote are `QsOk`'s). -/
theorem quiet_adv_step {S : State} {n : Fin R.N} {T : w64} {s s1 : PState} {q : Msg}
    (hc : S.cfg = R.cfg) (hT : s.term = T) (hct : S.currentTerm[n.val]! = uint.Z T)
    (hq : QMsg S n T q) (h : RecvEndO kk cf (nodeId n) s q s1) :
    s1.term = s.term ∧ (s.role ≠ .candidate → s1.role = s.role) ∧
      (s1.role = s.role → QKeep S n s s1) := by
  obtain ⟨⟨hqs, -, hqt, hrj, hty⟩, hack, hvote⟩ := hq
  have hqt' : q.term = s.term := hqt.trans hT.symm
  have hh : HandleEndO kk cf (nodeId n) s q s1 := by
    rcases h with ⟨-, hh⟩ | ⟨-, hlt, -⟩ | ⟨-, s2, hpre, hh⟩
    · exact hh
    · rw [hqt'] at hlt; exact absurd hlt (Int.lt_irrefl _)
    · rcases hpre with ⟨hlt, -⟩ | ⟨-, rfl⟩
      · rw [hqt'] at hlt; exact absurd hlt (Int.lt_irrefl _)
      · exact hh
  have hrefl : s1 = s → s1.term = s.term ∧ (s.role ≠ .candidate → s1.role = s.role) ∧
      (s1.role = s.role → QKeep S n s s1) := fun h => by subst h; exact ⟨rfl, fun _ => rfl, fun _ => QKeep.refl⟩
  unfold HandleEndO at hh
  rcases hty with hty | hty <;> rw [hty] at hh <;> simp only at hh
  · split at hh
    · unfold AppRespEndO at hh
      rcases hh with ⟨-, rfl⟩ | ⟨h', -⟩ | ⟨-, x, c, hx, -, ms, -, rfl⟩
      · exact hrefl rfl
      · rw [hrj] at h'; cases h'
      · refine ⟨rfl, fun _ => rfl, fun _ => ⟨rfl, rfl, fun _ hmo => ?_, fun _ hv => ?_⟩⟩
        · exact matchOk_raise (i := n) hqs hx (fun _ => by rw [hqs, hT]; exact hack hty) rfl rfl rfl rfl hmo
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

/-- A queued message other than a self pre-vote is `QMsg` at the view's term (`QsOk.notPre`). -/
theorem QsOk.qmsg {S : State} {n : Fin R.N} {v : NodeView} {q : Msg} (h : QsOk R S n v q)
    (hne : q.ty ≠ .preVoteResp) : QMsg S n v.ps.term q := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h.notPre hne
  refine ⟨⟨h1, h2, h3, h4, h5.imp (fun h => h.1) (fun h => h.1)⟩, fun hty => ?_, fun hty => ?_⟩
  · rcases h5 with h5 | h5
    · exact h5.2.2
    · rw [h5.1] at hty; cases hty
  · rcases h5 with h5 | h5
    · rw [h5.1] at hty; cases hty
    · exact h5.2

/-- `Advance`'s run: the term kept, a non-candidate's role kept, and `QKeep` when the role is the
same at the end (a candidate that won or lost stays a leader or follower). -/
theorem quiet_adv_run {S : State} {n : Fin R.N} {T : w64} {s s' : PState} {qs : List Msg}
    (hc : S.cfg = R.cfg) (hct : S.currentTerm[n.val]! = uint.Z T)
    (hqs : ∀ q ∈ qs, QMsg S n T q) (h : AdvanceEndO kk cf (nodeId n) s qs s') (hT : s.term = T) :
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

theorem selfFree_sends {id : w64} {s s' : PState} (h : SendsEnd cf id s s') (hX : SelfFree id s) :
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
    (hh : HandleEndO kk c id s m s') : SelfFree id s' := by
  unfold HandleEndO at hh
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
    · unfold AppRespEndO at hh
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
    (hro : s'.role = s.role) (ht : s'.term = s.term) (hr : RecvEndO kk c id s m s') :
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
    (ht : s'.term = s.term) (h : TickEndO kk c id s s') : SelfFree id s' := by
  rcases h with rfl | ⟨-, -, peers, cl, -, rfl⟩ | ⟨-, ms, hms, rfl⟩
  · exact hX
  · exact absurd ht (w64_succ_ne _)
  · exact selfFree_psend hX fun x hx => (hms x hx).1.2.2.2.1

/-- A proposal that keeps the log queues nothing to the node itself: a leader's batch is never
empty, a forward goes to the leader (another node, the leader hint). -/
theorem selfFree_propose {id : w64} {s s' : PState} {m : Msg} (hX : SelfFree id s)
    (hlead : LeadHint R.N id s) (hne : m.entries ≠ []) (hl : s'.log = s.log)
    (h : ProposeEnd cf id s m s') : SelfFree id s' := by
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
      exact selfFree_one hX (hlead.1 (by rw [hc.1]; decide))
    · subst h; exact hX

/-- `RecvEndP` at a kept term queues nothing to the node itself: its answers go to the sender. -/
theorem selfFree_recvP {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (hX : SelfFree id s)
    (hsrc : m.src ≠ id) (ht : s'.term = s.term) (h : RecvEndP kk c id s m s') : SelfFree id s' := by
  rcases h with ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ |
      ⟨-, -, -, rfl⟩ | ⟨-, rfl | ⟨-, -, -, hcs⟩⟩
  · exact selfFree_one hX hsrc
  · exact selfFree_one hX hsrc
  · exact hX
  · exact selfFree_one hX hsrc
  · exact selfFree_one hX hsrc
  · exact hX
  · exact hX
  · obtain ⟨peers, -, rfl⟩ := hcs; exact absurd ht (w64_succ_ne _)

/-- Every message of `s`'s outbox to the node itself is a pre-candidate's self pre-vote at the
next term `T + 1` (`QsOk`'s third arm): granted, the node a voter of `c` with pre-vote on. -/
def SelfPre (id T : w64) (c : CfgM) (kk : NodeK) (s : PState) : Prop :=
  ∀ q ∈ s.outbox, q.dst = id → q.ty = .preVoteResp ∧ q.src = id ∧ q.reject = false ∧
    q.term = T + W64 1 ∧ id ∈ c.voters ∧ kk.prevote = true

theorem SelfFree.pre {id T : w64} {c : CfgM} {s : PState} (h : SelfFree id s) : SelfPre id T c kk s :=
  fun q hq hd => absurd hd (h q hq)

/-- A pre-campaign queues to the node itself only its self pre-vote; a step-down nothing. -/
theorem selfPre_tickP {c : CfgM} {id : w64} {s s' : PState} (hX : s.outbox = [])
    (h : TickEndP kk c id s s') : SelfPre id s.term c kk s' := by
  rcases h with ⟨-, hk, hid, peers, hp, rfl⟩ | ⟨-, -, rfl⟩
  · intro q hq hd
    rcases List.mem_append.mp (mem_psend hX hq) with hq | hq
    · rw [List.mem_singleton.mp hq]; exact ⟨rfl, rfl, rfl, rfl, hid, hk⟩
    · obtain ⟨d, hdm, rfl⟩ := List.mem_map.mp hq
      exfalso
      have hd' : d ∈ elements (c.voters \ {[id]}) := hp.mem_iff.mp hdm
      rw [GMap.elem_of_elements, GMap.elem_of_difference] at hd'
      exact hd'.2 ((GMap.elem_of_singleton _ _).mpr (by simpa [pvoteReq] using hd))
  · exact SelfFree.pre (fun q hq => by
      have hq' : q ∈ s.outbox := hq
      rw [hX] at hq'; cases hq')

/-- What `Advance`'s steps keep from a state of role `r0`: the candidate role only from a
candidate's start, and a message to the node itself queued only once a candidate's start has
left the candidate role (its win's self-acknowledgement). -/
def AdvSelf (id : w64) (r0 : Role) (s : PState) : Prop :=
  (s.role = .candidate → r0 = .candidate) ∧
  ∀ q ∈ s.outbox, q.dst = id → r0 = .candidate ∧ s.role ≠ .candidate

theorem advSelf_sends {id : w64} {r0 : Role} {s s' : PState} (h : SendsEnd cf id s s')
    (hi : AdvSelf id r0 s) : AdvSelf id r0 s' := by
  obtain ⟨ms, hms, rfl⟩ := h
  refine ⟨hi.1, fun q hq hd => ?_⟩
  rw [psendMsgs_outbox] at hq
  rcases List.mem_append.mp hq with hq | hq
  · exact hi.2 q hq hd
  · exact absurd hd (hms q hq).1.2.2.2.1

theorem advSelf_handle {c : CfgM} {id : w64} {r0 : Role} {s s' : PState} {q : Msg}
    (hi : AdvSelf id r0 s) (hty : q.ty = .appResp ∨ q.ty = .voteResp)
    (hh : HandleEndO kk c id s q s') : AdvSelf id r0 s' := by
  unfold HandleEndO at hh
  rcases hty with hty | hty <;> rw [hty] at hh <;> simp only at hh
  · split at hh
    · unfold AppRespEndO at hh
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
    (h : RecvEndO kk c id s q s1) : AdvSelf id r0 s1 := by
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
    (h : AdvanceEndO kk c id s qs s') (hq : ∀ q ∈ qs, q.ty = .appResp ∨ q.ty = .voteResp)
    (hi : AdvSelf id r0 s) : AdvSelf id r0 s' := by
  induction h with
  | nil => exact hi
  | cons s s1 s' q qs hr _ ih =>
    exact ih (fun x hx => hq x (List.mem_cons_of_mem _ hx))
      (advSelf_step hi (hq q (List.mem_cons_self ..)) hr)

/-! ## Quiet steps along `Reach` -/

/-- **A quiet step's state along `ReachP`** (to a state with the view's role, term and log):
`QKeep` from the view's state (received messages from another node: C4's `NetShape`; the new arms
keep the state, make a follower, or change the term). -/
theorem quiet_reachP {S : State} {net : List Msg} {n : Fin R.N} {v : NodeView} {ps₁ : PState}
    (hc : S.cfg = R.cfg) (hnet : NetOk R S net) (hct : S.currentTerm[n.val]! = uint.Z v.ps.term)
    (hqs : ∀ q ∈ v.qs, q.ty ≠ .preVoteResp → QMsg S n v.ps.term q)
    (hr : ReachP kk cf (nodeId n) net v ps₁)
    (hro : ps₁.role = v.ps.role) (ht : ps₁.term = v.ps.term) (hl : ps₁.log = v.ps.log) :
    QKeep S n v.ps ps₁ := by
  cases hr with
  | stay _ => exact QKeep.refl
  | recv m _ _ _ _ hmn hmd hm0 hs4 h =>
    exact quiet_recv hc hnet hmn hmd (hnet.2.2.1 m hmn).2.1 hm0 hct (ty7_of_s4 hs4) h hro ht hl
  | recvP m _ _ _ _ _ _ _ _ h => exact quiet_recvP ht h
  | tick _ _ _ h => exact quiet_tick h ht
  | tickP _ _ _ h => exact quiet_tickP h
  | propose d _ _ _ hh => exact quiet_propose hh hl
  | advance _ _ _ _ hno h =>
    exact (quiet_adv_run hc hct (fun q hq => hqs q hq (hno q hq)) h rfl).2.2 hro
  | advP _ _ _ _ _ _ _ h =>
    rcases h with rfl | ⟨-, -, hcs⟩
    · exact QKeep.refl
    · obtain ⟨peers, -, rfl⟩ := hcs; exact absurd ht (w64_succ_ne _)

/-- **A quiet step's state** (`Reach` to a state with the view's role, term and log): `QKeep` from
the view's state (`quiet_reachP`). For the runs a mask below `mskB1p` admits. -/
theorem quiet_reach {msk : SimMask} (hmsk : msk ≤ mskB1p) {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {S : State} {net : List Msg} {xnet : List XMsg}
    {n : Fin R.N} {v : NodeView} {r₁ : RState} (hin : InMask msk R net xnet)
    (hc : S.cfg = R.cfg) (hnet : NetOk R S net) (hv : NodeOk R dec S net n v)
    (hr : ReachIn msk R dec Adm net xnet n v r₁)
    (hro : r₁.p.role = v.ps.role) (ht : r₁.p.term = v.ps.term) (hl : r₁.p.log = v.ps.log) :
    QKeep S n v.ps r₁.p := by
  obtain ⟨hmd, hbt, hpar, hspl, -, -, -⟩ := hin.b1p hmsk
  have hdur : v.dur = durOf v.r := (hv.sync (by rw [hmd]) hbt hspl hpar).2.1
  have hct : S.currentTerm[n.val]! = uint.Z v.ps.term := by rw [hv.disk.1, hdur]; rfl
  exact quiet_reachP hc hnet hct (fun q hq hne => (hv.qs q hq).qmsg hne)
    (ReachIn.toP hmsk hin hnet hv hr) hro ht hl

/-- **A quiet step's state queues for `Advance` at most a pre-candidate's self pre-vote**
(`SelfPre`, along `ReachP`): a received message's answer is to its sender (another node), a
campaign changes the term, a win the role, a proposal the log; a forward goes to the leader (the
leader hint); a pre-campaign queues its self pre-vote; `Advance` queues a self-acknowledgement only
at a candidate's win. -/
theorem selfPre_reachP {net : List Msg} {n : Fin R.N} {v : NodeView} {ps₁ : PState}
    (hX : v.ps.outbox = []) (hlo : LeadHint R.N (nodeId n) v.ps)
    (hsd : ∀ m ∈ net, m.dst = nodeId n → m.src ≠ nodeId n)
    (hnp : ∀ m ∈ net, m.ty = .propose → m.term = W64 0)
    (hqs : ∀ q ∈ v.qs, q.ty ≠ .preVoteResp → q.ty = .appResp ∨ q.ty = .voteResp)
    (hr : ReachP kk cf (nodeId n) net v ps₁)
    (hro : ps₁.role = v.ps.role) (ht : ps₁.term = v.ps.term) (hl : ps₁.log = v.ps.log) :
    SelfPre (nodeId n) v.ps.term cf kk ps₁ := by
  have hXf : SelfFree (nodeId n) v.ps := fun q hq => by rw [hX] at hq; cases hq
  cases hr with
  | stay _ => exact hXf.pre
  | recv m _ _ _ _ hmn hmd hm0 hs4 h =>
    exact (selfFree_recv hXf (ty7_of_s4 hs4) (fun hp => hm0 (hnp m hmn hp)) (hsd m hmn hmd) hm0
      hro ht h).pre
  | recvP m _ _ _ _ hmn hmd _ _ h => exact (selfFree_recvP hXf (hsd m hmn hmd) ht h).pre
  | tick _ _ _ h => exact (selfFree_tick hXf ht h).pre
  | tickP _ _ _ h => exact selfPre_tickP hX h
  | propose d _ _ _ hh => exact (selfFree_propose hXf hlo (by simp [propMsg]) hl hh).pre
  | advance _ _ _ _ hno h =>
    have hfin := advSelf_run h (fun q hq => hqs q hq (hno q hq))
      (⟨fun h => h, fun q hq => by rw [hX] at hq; cases hq⟩ : AdvSelf (nodeId n) v.ps.role v.ps)
    exact SelfFree.pre (fun q hq hdq => (hfin.2 q hq hdq).2 (hro.trans (hfin.2 q hq hdq).1))
  | advP _ _ _ _ _ _ _ h =>
    rcases h with rfl | ⟨-, -, hcs⟩
    · exact hXf.pre
    · obtain ⟨peers, -, rfl⟩ := hcs; exact absurd ht (w64_succ_ne _)

/-- **A quiet step's state queues for `Advance` at most a pre-candidate's self pre-vote**
(`selfPre_reachP`). For the runs a mask below `mskB1p` admits. -/
theorem reach_selfPre {msk : SimMask} (hmsk : msk ≤ mskB1p) {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {S : State} {net : List Msg} {xnet : List XMsg}
    {n : Fin R.N} {v : NodeView} {r₁ : RState} (hin : InMask msk R net xnet)
    (hnet : NetOk R S net) (hv : NodeOk R dec S net n v)
    (hr : ReachIn msk R dec Adm net xnet n v r₁)
    (hro : r₁.p.role = v.ps.role) (ht : r₁.p.term = v.ps.term) (hl : r₁.p.log = v.ps.log) :
    SelfPre (nodeId n) v.ps.term v.r.cfg.cfg (R.k n) r₁.p :=
  selfPre_reachP hv.facts.outbox hv.leadOk (fun m hmn hmd => hmd ▸ (hnet.2.2.1 m hmn).2.1)
    (fun m hmn => (hnet.2.2.1 m hmn).2.2) (fun q hq hne => ((hv.qs q hq).self hne).2.2.2.2)
    (ReachIn.toP hmsk hin hnet hv hr) hro ht hl

/-! ## `antSim_quiet` -/

/-- Two reported roles agree when each pre-candidate is a follower: the same pre flag and role. -/
theorem roleStr_eq {p p' : Bool} {r r' : Role} (h : roleStr p r = roleStr p' r')
    (hp : p = true → r = .follower) (hp' : p' = true → r' = .follower) : p = p' ∧ r = r' := by
  cases p <;> cases p'
  · refine ⟨rfl, ?_⟩
    cases r <;> cases r' <;> first | rfl | simp [roleStr, roleOf] at h
  · cases r <;> simp [roleStr, roleOf] at h
  · cases r' <;> simp [roleStr, roleOf] at h
  · exact ⟨rfl, (hp rfl).trans (hp' rfl).symm⟩

theorem leaderPart_of {S : State} {n : Fin R.N} {v w : NodeView} (h : LeaderPart S n v)
    (hr : w.ps.role = v.ps.role) (ht : w.ps.term = v.ps.term) (hf : w.r.full = v.r.full)
    (hm : v.ps.role = .leader → MatchOk S n v.ps → MatchOk S n w.ps) : LeaderPart S n w := by
  intro hlead
  have hlv : v.ps.role = .leader := hr.symm.trans hlead
  obtain ⟨h1, h2, h3, h4, h5⟩ := h hlv
  obtain ⟨h3', h4'⟩ := hm hlv ⟨h3, h4⟩
  refine ⟨by rw [ht]; exact h1, by rw [ht, hf]; exact h2, h3', h4', ?_⟩
  unfold LeaderConfOk at *; rw [ht, hf]; exact h5

theorem candPart_of {S : State} {n : Fin R.N} {v w : NodeView} (h : CandPart S n v)
    (hr : w.ps.role = v.ps.role)
    (hm : v.ps.role = .candidate → VotesOk S n v.ps → VotesOk S n w.ps) : CandPart S n w := by
  intro hc
  have hcv : v.ps.role = .candidate := hr.symm.trans hc
  obtain ⟨h1, h2⟩ := h hcv
  exact ⟨hm hcv h1, h2⟩

/-- A state with the view's full log and ghost prefix has its log. -/
theorem log_of_full {r r' : RState} (hf : r'.full = r.full) (hfp : r'.fp = r.fp) : r'.p.log = r.p.log := by
  have h' : r'.fp ++ r'.p.log = r'.fp ++ r.p.log := by
    have := hf; unfold RState.full at this; rw [hfp] at this ⊢; exact this
  exact List.append_cancel_left h'

/-- **A quiet step keeps the node's part of the relation** (`NodeOk`): an input noted changes only
the drain's `by` and cause (the message sent to it); a state with no `Ready` or a silent one keeps
the disk, the role, term, vote, commit and full log, `QKeep` the leader's and candidate's parts, the
leader hint and a leader's empty read-only queue are kept along `Reach`, the silent `Ready`'s
messages are `PendOk` (`pendOk_of_reach`) and under the mask (`msgShape_core`), and none is to the
node itself but a pre-candidate's self pre-vote (`reach_selfPre`: `qs` is `QsOk`'s third arm). For the
runs a mask below `mskB1p` admits. -/
theorem nodeOk_quiet {msk : SimMask} (hmsk : msk ≤ mskB1p) {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {S : State} {net : List Msg} {xnet : List XMsg}
    {n : Fin R.N} {v v' : NodeView} (hin : InMask msk R net xnet) (hcf : S.cfg = R.cfg)
    (hnet : NetOk R S net) (hv : NodeOk R dec S net n v)
    (hq : QuietIn msk R dec Adm net xnet n v v') : NodeOk R dec S net n v' := by
  obtain ⟨hmd, hbt, hpar, hspl, _, _, _⟩ := hin.b1p hmsk
  have hsy := hv.sync (by rw [hmd]) hbt hspl hpar
  have hdur : v.dur = durOf v.r := hsy.2.1
  have hcc : R.md.confChanges = false := by rw [hmd]
  have hsn : R.md.snapshots = false := by rw [hmd]
  have hfn : EntsNormal v.r.full := (hv.facts.conf0 hcc).2.1
  have hsnap0 := hv.facts.snap0 hsn
  have hconf : v.conf = v.r.cfg ∧ v.confAt = lastConfIdx v.r.full v.r.cidx := by
    rcases hv.confLag with h | ⟨h, -⟩
    · exact h
    · rw [hsnap0.2.2] at h; cases h
  cases hq with
  | input inp hinp hidle hm hx =>
    obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, -, -, -, -, -, -, d17, d18⟩ := hv
    refine ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, ?_, ?_, ?_, ?_, ?_, ?_, d17, d18⟩
    · intro q hq; have hq' : q ∈ v.pend := hq; rw [hidle.2.1] at hq'; cases hq'
    · intro q hq; have hq' : q ∈ v.xpend := hq; rw [hidle.2.2.1] at hq'; cases hq'
    · intro q hq; have hq' : q ∈ v.qs := hq; rw [hidle.1] at hq'; cases hq'
    · intro h; simp [NodeView.noteInput] at h
    · intro m hm0
      rcases Input.inMask_b1p hmsk hinp with ⟨m', rfl⟩ | rfl | ⟨d, rfl⟩ | rfl
      · have : m' = m := Option.some.inj hm0
        subst this; exact hm m' rfl
      all_goals simp [NodeView.noteInput, Input.cause] at hm0
    · intro x hx0
      rcases Input.inMask_b1p hmsk hinp with ⟨m', rfl⟩ | rfl | ⟨d, rfl⟩ | rfl <;>
        simp [NodeView.noteInput, Input.xcause] at hx0
  | noReady r₁ hr hX _ ht hvo hc hro hfl =>
    obtain ⟨⟨hcfg, hfp, hsnap⟩, hpe, hxpe⟩ := reach_keep hmsk hin hv hr
    have hl : r₁.p.log = v.ps.log := log_of_full hfl hfp
    have hkp := quiet_reach hmsk hin hcf hnet hv hr hro ht hl
    have hlead := reach_leadOk hmsk hin hnet hv hr
    have hroOk := reach_roOk hmsk hin hnet hv hr
    obtain ⟨d1, d2, d3, d4, d5, d6, -, d8, d9, d10, -, -, -, d14, d15, d16, -, d18⟩ := hv
    obtain ⟨-, -, f3, f4, f5, f6, f7, f8, f9, -, f11⟩ := d8
    refine ⟨d1, ⟨?_, d2.2⟩, fun a b c e => ⟨(d3 a b c e).1, ?_, (d3 a b c e).2.2⟩, d4, d5, d6,
      .inl ⟨?_, ?_⟩, ⟨hX, fun _ => ⟨hkp.1.trans hsnap0.1, hfp.trans hsnap0.2.1, hsnap.trans hsnap0.2.2⟩,
        fun h => ⟨by show r₁.cfg.cfg = _; rw [hcfg]; exact (f3 h).1, hfl ▸ (f3 h).2.1, (f3 h).2.2⟩, f4, f5, f6, f7,
        by show uint.Z v.dur.term ≤ uint.Z r₁.p.term; rw [ht]; exact f8,
        fun h => hro.trans (f9 h), fun _ => hroOk, f11⟩,
      leaderPart_of d9 hro ht hfl (fun hr' hm => hkp.2.2.1 (hro.trans hr') hm),
      candPart_of d10 hro (fun hr' hm => hkp.2.2.2 (hro.trans hr') hm),
      ?_, ?_, ?_, d14, d15, d16, hlead, fun h => hvo.trans (d18 fun h' => h (hro.trans h'))⟩
    · rw [d2.1]; show roleOf v.ps.role = roleOf r₁.p.role; rw [hro]
    · show v.dur = durOf r₁
      rw [hdur]; simp only [durOf, ht, hvo, hc, hfl]
    · show v.conf = r₁.cfg; rw [hcfg]; exact hconf.1
    · show v.confAt = lastConfIdx r₁.full r₁.cidx
      rw [hconf.2, lastConfIdx_normal hfn, lastConfIdx_normal (hfl ▸ hfn)]
    · intro q hq; have hq' : q ∈ v.pend := hq; rw [hpe] at hq'; cases hq'
    · intro q hq; have hq' : q ∈ v.xpend := hq; rw [hxpe] at hq'; cases hq'
    · intro q hq; cases hq
  | silentReady r₁ rd hr hrop hs =>
    obtain ⟨⟨hcfg, hfp, hsnap⟩, -, -⟩ := reach_keep hmsk hin hv hr
    have hrop' := hrop
    obtain ⟨hR, hpre, hT, hV, hC, hnil, -, hqp, hsync, -, hxm, hpfx, hlen, -, hsnapC, -, -⟩ := hrop
    have h1 : rd.term = v.dur.term := Classical.byContradiction fun h => hs (.inl h)
    have h2 : rd.vote = v.dur.vote := Classical.byContradiction fun h => hs (.inr (.inl h))
    have h3 : rd.commit = v.dur.commit :=
      Classical.byContradiction fun h => hs (.inr (.inr (.inl h)))
    have h4 : rd.ents = [] := Classical.byContradiction fun h => hs (.inr (.inr (.inr (.inl h))))
    have h6 : roleStr rd.pre rd.role = roleS v :=
      Classical.byContradiction fun h => hs (.inr (.inr (.inr (.inr (.inr h)))))
    obtain ⟨hb0, hsn0, hnosnap⟩ := hsnapC hsn
    have hfull : r₁.full = v.dur.log := hnil hsn0 h4
    have hfl : r₁.full = v.r.full := by rw [hfull, hdur]; rfl
    have hpe := roleStr_eq h6 (fun h => (hpre h).1) hv.facts.preRole
    have hRole : r₁.p.role = v.ps.role := hR.symm.trans hpe.2
    have ht : r₁.p.term = v.ps.term := hT.symm.trans (h1.trans (by rw [hdur]; rfl))
    have hvo : r₁.p.vote = v.ps.vote := hV.symm.trans (h2.trans (by rw [hdur]; rfl))
    have hl : r₁.p.log = v.ps.log := log_of_full hfl hfp
    have hkp := quiet_reach hmsk hin hcf hnet hv hr hRole ht hl
    have hsp := reach_selfPre hmsk hin hnet hv hr hRole ht hl
    have hpend := pendOk_of_reach hmsk hin hnet hv hr hrop'
    have hlead := reach_leadOk hmsk hin hnet hv hr
    have hroOk := reach_roOk hmsk hin hnet hv hr
    have hcm : ∀ m, v.cause = some m → m.ty = .app ∨ m.ty = .propose → EntsNormal m.entries :=
      fun m hm => (hnet.2.2.2.2.1 m (hv.cause m hm).1).1 hcc
    have hmsg := (hsync (by rw [hmd])).2
    obtain ⟨-, hms⟩ := msgShape_core hmsk hin hnet hv hr hmsg hfn (hv.facts.roPend (by rw [hmd])) hcm
    have hqq : ∀ q ∈ rd.qs, q ∈ r₁.p.outbox ∧ q.dst = nodeId n := fun q hq => by
      have h' := (hqp.mem_iff).mp hq
      rw [List.mem_filter] at h'
      exact ⟨h'.1, of_decide_eq_true h'.2⟩
    obtain ⟨d1, d2, d3, d4, d5, d6, -, d8, d9, d10, -, -, -, d14, d15, d16, -, d18⟩ := hv
    obtain ⟨-, -, f3, f4, -, -, -, f8, -, -⟩ := d8
    have hcm' : (accepted r₁).p.commit = v.dur.commit := hC.symm.trans h3
    refine ⟨d1, ⟨?_, d2.2⟩, fun a b c e => ⟨(d3 a b c e).1, ?_, (d3 a b c e).2.2⟩, d4, d5, d6,
      .inl ⟨?_, ?_⟩, ⟨rfl, fun _ => ⟨hb0, hfp.trans hsnap0.2.1, hsnap.trans hsnap0.2.2⟩,
        fun h => ⟨by show r₁.cfg.cfg = _; rw [hcfg]; exact (f3 h).1, by show EntsNormal r₁.full; rw [hfull]; exact (f3 h).2.2,
          (f3 h).2.2⟩, f4, by show v.delivered ++ rd.ce <+: v.dur.log; rw [← hfull]; exact hpfx,
        by show (v.delivered ++ rd.ce).length ≤ uint.nat v.dur.commit; rw [← hcm']; exact hlen,
        fun q hq => ?_, by show uint.Z v.dur.term ≤ uint.Z r₁.p.term; rw [← hT, h1]; exact Int.le_refl _,
        (fun h => hR.symm.trans (hpre h).1), fun _ => hroOk, fun h => (hpre h).2⟩,
      leaderPart_of d9 hRole ht hfl (fun hr' hm => hkp.2.2.1 (hRole.trans hr') hm),
      candPart_of d10 hRole (fun hr' hm => hkp.2.2.2 (hRole.trans hr') hm),
      hpend, ?_, ?_, d14, d15, d16, hlead, fun h => hvo.trans (d18 fun h' => h (hRole.trans h'))⟩
    · rw [d2.1]; show roleOf v.ps.role = roleOf r₁.p.role; rw [hRole]
    · show v.dur = durOf (accepted r₁)
      have e : durOf (accepted r₁) = ⟨rd.term, rd.vote, rd.commit, r₁.full⟩ := by
        rw [hT, hV, hC]; rfl
      rw [e, h1, h2, h3, hfull]
    · show v.conf = r₁.cfg; rw [hcfg]; exact hconf.1
    · show v.confAt = lastConfIdx r₁.full (accepted r₁).cidx
      rw [hconf.2, lastConfIdx_normal hfn, lastConfIdx_normal (hfl ▸ hfn)]
    · have hmq := hms q hq
      obtain ⟨-, h2', h3', -, -⟩ := id hmq
      have hqo : q ∈ r₁.p.outbox := (List.mem_filter.mp ((hmsg.mem_iff).mp hq)).1
      exact ⟨fun _ _ => h3', fun _ => hnosnap q hqo, h2', mshape_ctx hnet (fun m hm => (d15 m hm).1) hmq⟩
    · exact hxm
    · intro q hq
      obtain ⟨hqo, hqd⟩ := hqq q hq
      obtain ⟨hty, hsrc, hrj, hterm, hvt, hpv⟩ := hsp q hqo hqd
      refine ⟨hsrc, hqd, hrj, .inr ⟨hty, ?_, ?_, hpv, fun q' hq' => (hsp q' (hqq q' hq').1 (hqq q' hq').2).1⟩⟩
      · show q.term = r₁.p.term + W64 1; rw [ht]; exact hterm
      · show nodeId n ∈ r₁.cfg.cfg.voters; rw [hcfg]; exact hvt

/-- **`antSim_quiet` for the runs a mask below `mskB1p` admits**: the steps that report nothing keep
the relation, `S` unchanged. -/
theorem antSim_quiet_in (msk : SimMask) (hmsk : msk ≤ mskB1p) :
    ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
      (xnet : List XMsg) (G : RaftFacts) (n : Fin R.N) (v' : NodeView),
      InMask msk R net xnet → AntSim R dec S V net xnet → RaftLaws G → GlobalOk R S net G →
      QuietIn msk R dec (admOf G) net xnet n (V n) v' → AntSim R dec S (setV V n v') net xnet := by
  intro R dec S V net xnet G n v' hin hsim _ _ hq
  obtain ⟨hsh, hb, hnet, hxn, hall⟩ := hsim
  refine ⟨hsh, hb, hnet, hxn, fun j => ?_⟩
  unfold setV
  by_cases hj : j = n
  · subst hj; simp only [↓reduceIte]; exact nodeOk_quiet hmsk hin hsh.1 hnet (hall j) hq
  · simp only [hj, ↓reduceIte]; exact hall j

end quiet

end AntSim
end EtcdGrove
end Perennial
