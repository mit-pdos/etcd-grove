/-
The protocol's step relation at a joint configuration (2026-10-13, reconfiguration stage A1),
Lean-first: pure, no ghost state.

`Step cfg id` (`Model.lean`) is a node's step at the fixed voter set `cfg`. `StepC c id` is
the same relation at a configuration `c : CfgM` as raft's `confchange` package keeps it --
incoming and outgoing voters, learners, staged learners, `AutoLeave` -- where only the voters
matter to the protocol:

* a quorum is a quorum of *both* halves, Go's `JointConfig` (`JQuorum`): `MajQ s q` is a
  majority of `s` or `s` empty -- Go's convention that an empty `MajorityConfig` wins every
  vote (`VoteResult`) and has committed everything (`CommittedIndex` is `MaxUint64`), which
  makes the empty outgoing half of a non-joint configuration neutral;
* an election is lost when either half is (`JLost`): `JointConfig.VoteResult` answers
  `VoteLost` when one half's non-rejecting voters are not a majority of it;
* a campaign is by a voter of either half, and asks every other voter of either half
  (`campaign`'s `r.trk.Voters.IDs()`, the union);
* the read-index acknowledgement test is `JQuorum` too (`JQuorumAcked`).

The other rules are `Step`'s, unchanged. `step_iff_stepC` relates the two at a non-joint
configuration with voters `cfg ≠ ∅` (learners arbitrary): the relations are equal, so the
generalization loses nothing of what was proved at a fixed voter set. Nothing uses `StepC`
yet: the ghost state and the refinement stay at `Step` (stage A1 is code-level only; the
protocol at joint configurations is later work).

`CfgM` itself (moved here from `InvConfchange.lean` on 2026-10-13 so that this pure file can
name it) is a `tracker.Config` abstractly.
-/
module

public import Proof.go_etcd_io.raft.v3.Protocol.Model

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open GMap go_etcd_io.raft.v3

/-- A `tracker.Config`, abstractly: the incoming and outgoing voter sets (`Voters[0]`,
`Voters[1]`), the learners, the staged learners (`LearnersNext`) and `AutoLeave`. (The
`confchange` model, `InvConfchange.lean`, works on it.) -/
structure CfgM where
  incoming : GSet w64
  outgoing : GSet w64
  learners : GSet w64
  learnersNext : GSet w64
  autoLeave : Bool

/-- The voters of either half: what `JointConfig.IDs` returns. -/
def CfgM.voters (c : CfgM) : GSet w64 := c.incoming ∪ c.outgoing

/-- A configuration with the voters `cfg`, the learners `lrn`, not joint. -/
def CfgM.simple (cfg lrn : GSet w64) : CfgM :=
  { incoming := cfg, outgoing := ∅, learners := lrn, learnersNext := ∅, autoLeave := false }

/-- `q` is a majority of `s`, by Go's convention for an empty `MajorityConfig`: every set is
a majority of the empty one. -/
def MajQ (s q : GSet w64) : Prop := s = ∅ ∨ IsQuorum s q

/-- `q` is a quorum of the joint configuration: a majority of both halves. -/
def JQuorum (c : CfgM) (q : GSet w64) : Prop := MajQ c.incoming q ∧ MajQ c.outgoing q

/-- The election is lost (`JointConfig.VoteResult = VoteLost`): in one half, the voters that
have not rejected are not a majority. -/
def JLost (c : CfgM) (votes : GMap w64 Bool) : Prop :=
  ¬ MajQ c.incoming (c.incoming \ rejected votes) ∨ ¬ MajQ c.outgoing (c.outgoing \ rejected votes)

/-- `QuorumAcked` at a joint configuration. -/
def JQuorumAcked (c : CfgM) (f : w64 → w64) (N : w64) : Prop :=
  ∃ Q, JQuorum c Q ∧ ∀ v ∈ Q, uint.Z N ≤ uint.Z (f v)

/-! ### Joint quorums at a non-joint configuration -/

theorem MajQ_empty (q : GSet w64) : MajQ ∅ q := Or.inl rfl

theorem MajQ_of_ne {s : GSet w64} (q : GSet w64) (h : s ≠ ∅) : MajQ s q ↔ IsQuorum s q := by
  unfold MajQ; simp [h]

theorem CfgM.voters_simple (cfg lrn : GSet w64) : (CfgM.simple cfg lrn).voters = cfg :=
  union_empty_r_L cfg

/-- The voters of a non-joint configuration are the incoming ones. -/
theorem CfgM.voters_of_out {c : CfgM} (h : c.outgoing = ∅) : c.voters = c.incoming := by
  unfold CfgM.voters; rw [h, union_empty_r_L]

theorem JQuorum_of_out {c : CfgM} (hi : c.incoming ≠ ∅) (ho : c.outgoing = ∅) (q : GSet w64) :
    JQuorum c q ↔ IsQuorum c.incoming q := by
  unfold JQuorum; rw [ho, MajQ_of_ne q hi]
  exact ⟨fun h => h.1, fun h => ⟨h, MajQ_empty q⟩⟩

theorem JLost_of_out {c : CfgM} (hi : c.incoming ≠ ∅) (ho : c.outgoing = ∅)
    (votes : GMap w64 Bool) :
    JLost c votes ↔ ¬ IsQuorum c.incoming (c.incoming \ rejected votes) := by
  unfold JLost; rw [ho, MajQ_of_ne _ hi]
  exact ⟨fun h => h.elim id (fun h' => absurd (MajQ_empty _) h'), Or.inl⟩

theorem JQuorumAcked_of_out {c : CfgM} (hi : c.incoming ≠ ∅) (ho : c.outgoing = ∅)
    (f : w64 → w64) (N : w64) : JQuorumAcked c f N ↔ QuorumAcked c.incoming f N := by
  unfold JQuorumAcked QuorumAcked
  simp only [JQuorum_of_out hi ho]

/-! ### Overlapping configurations (moved from `CfgOverlap.lean` in stage B4: the ghost
state's definitions read it) -/

/-- Every joint quorum of `c1` meets every joint quorum of `c2`. -/
def QOverlap (c1 c2 : CfgM) : Prop :=
  ∀ q1 q2, JQuorum c1 q1 → JQuorum c2 q2 → ∃ x, x ∈ q1 ∧ x ∈ q2

theorem QOverlap.symm {c1 c2 : CfgM} (h : QOverlap c1 c2) : QOverlap c2 c1 :=
  fun q1 q2 h1 h2 => (h q2 q1 h2 h1).elim fun x hx => ⟨x, hx.2, hx.1⟩

/-- A joint quorum of a configuration with an incoming voter is a majority of its incoming
voters. -/
theorem JQuorum_incoming {c : CfgM} {q : GSet w64} (hi : c.incoming ≠ ∅) (h : JQuorum c q) :
    IsQuorum c.incoming q :=
  (MajQ_of_ne q hi).1 h.1

/-- Two joint quorums of one configuration (with an incoming voter) meet. -/
theorem JQuorum_intersect {c : CfgM} (hi : c.incoming ≠ ∅) {q1 q2 : GSet w64}
    (h1 : JQuorum c q1) (h2 : JQuorum c q2) : ∃ x, x ∈ q1 ∧ x ∈ q2 :=
  quorums_intersect c.incoming q1 q2 (JQuorum_incoming hi h1) (JQuorum_incoming hi h2)

theorem QOverlap.refl {c : CfgM} (hi : c.incoming ≠ ∅) : QOverlap c c :=
  fun _ _ h1 h2 => JQuorum_intersect hi h1 h2

/-- Whether the configuration `c` is joint: `len(r.trk.Config.Voters[1]) > 0`, `stepLeader`'s
`alreadyJoint` (moved here from `Spec/stepLeader.lean` in stage B3, for `StepR`'s proposals). -/
def CfgM.joint (c : CfgM) : Bool := decide (0 < GMap.size c.outgoing)

theorem CfgM.joint_simple (cfg lrn : GSet w64) : (CfgM.simple cfg lrn).joint = false := by
  simp [CfgM.joint, CfgM.simple, GMap.map_size_empty]

/-! ### Conf-change entries of a log (moved here from `CfgOverlap.lean` and `StepRInv.lean`
in stage B5: the ghost state's dynamic facts read them) -/

section conf
variable [FfiSyntax]

/-- The number of conf-change entries of `l`. -/
def confCount (l : List raftpb.Entry) : Nat := l.countP fun e => decide (IsConfEnt e)

theorem confCount_append (l1 l2 : List raftpb.Entry) :
    confCount (l1 ++ l2) = confCount l1 + confCount l2 := by
  unfold confCount; exact List.countP_append ..

theorem confCount_cons (e : raftpb.Entry) (l : List raftpb.Entry) :
    confCount (e :: l) = confCount l + (if IsConfEnt e then 1 else 0) := by
  unfold confCount
  rw [List.countP_cons]
  by_cases h : IsConfEnt e <;> simp [h]

/-- A conf-change entry at position `k` of `l` (2026-10-14, stage B5). -/
def IsConfPos (l : List raftpb.Entry) (k : Nat) : Prop := ∃ e, l[k]? = some e ∧ IsConfEnt e

/-- I1: of two conf-change entries of `l`, the first is at a position below `c`. -/
def ConfI1 (l : List raftpb.Entry) (c : Nat) : Prop :=
  ∀ (k1 k2 : Nat) (e1 e2 : raftpb.Entry), k1 < k2 → l[k1]? = some e1 → l[k2]? = some e2 →
    IsConfEnt e1 → IsConfEnt e2 → k1 < c

theorem confCount_pos {l : List raftpb.Entry} {k : Nat} {e : raftpb.Entry} (h : l[k]? = some e)
    (hc : IsConfEnt e) : 0 < confCount l := by
  unfold confCount
  rw [List.countP_pos_iff]
  exact ⟨e, List.mem_of_getElem? h, by simpa using hc⟩

theorem two_le_confCount {l : List raftpb.Entry} {k1 k2 : Nat} {e1 e2 : raftpb.Entry}
    (hlt : k1 < k2) (h1 : l[k1]? = some e1) (h2 : l[k2]? = some e2) (c1 : IsConfEnt e1)
    (c2 : IsConfEnt e2) : 2 ≤ confCount l := by
  rw [← List.take_append_drop k2 l, confCount_append]
  have a : 0 < confCount (l.take k2) :=
    confCount_pos (k := k1) (by rw [List.getElem?_take, if_pos hlt]; exact h1) c1
  have b : 0 < confCount (l.drop k2) :=
    confCount_pos (k := 0) (by rw [List.getElem?_drop, Nat.add_zero]; exact h2) c2
  omega

/-! #### Conf positions and counts (2026-10-14, stage B5: the far cases' pure core) -/

instance IsConfPos.dec (l : List raftpb.Entry) (k : Nat) : Decidable (IsConfPos l k) :=
  match h : l[k]? with
  | some e =>
    if hc : IsConfEnt e then isTrue ⟨e, h, hc⟩
    else isFalse (by rintro ⟨e', he', hc'⟩; rw [h] at he'; cases he'; exact hc hc')
  | none => isFalse (by rintro ⟨e', he', -⟩; rw [h] at he'; cases he')

theorem confCount_take_mono (l : List raftpb.Entry) {i j : Nat} (h : i ≤ j) :
    confCount (l.take i) ≤ confCount (l.take j) := by
  have : l.take j = l.take i ++ (l.drop i).take (j - i) := by
    have h2 := List.take_add (l := l) (i := i) (j := j - i)
    rwa [Nat.add_sub_cancel' h] at h2
  rw [this, confCount_append]; omega

theorem confCount_take_succ (l : List raftpb.Entry) (k : Nat) :
    confCount (l.take (k + 1)) = confCount (l.take k) + (if IsConfPos l k then 1 else 0) := by
  by_cases hk : k < l.length
  · rw [List.take_succ, confCount_append, List.getElem?_eq_getElem hk]
    simp only [Option.toList_some]
    by_cases hc : IsConfEnt l[k]
    · have : IsConfPos l k := ⟨l[k], List.getElem?_eq_getElem hk, hc⟩
      rw [if_pos this]
      unfold confCount; simp [hc]
    · have : ¬ IsConfPos l k := by
        rintro ⟨e, he, hce⟩
        rw [List.getElem?_eq_getElem hk] at he
        cases he; exact hc hce
      rw [if_neg this]
      unfold confCount; simp [hc]
  · have h1 : l.take (k + 1) = l.take k := by
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
    have h2 : ¬ IsConfPos l k := by
      rintro ⟨e, he, -⟩
      rw [List.getElem?_eq_none (by omega)] at he; cases he
    rw [h1, if_neg h2]; rfl

/-- The `j`-th conf entry (0-based) below `a`. -/
theorem exists_confPos (l : List raftpb.Entry) (a j : Nat) (h : j < confCount (l.take a)) :
    ∃ k, k < a ∧ IsConfPos l k ∧ confCount (l.take k) = j := by
  induction a with
  | zero => simp [confCount] at h
  | succ a ih =>
    rw [confCount_take_succ] at h
    by_cases hj : j < confCount (l.take a)
    · obtain ⟨k, hk, hc, he⟩ := ih hj
      exact ⟨k, by omega, hc, he⟩
    · by_cases hc : IsConfPos l a
      · rw [if_pos hc] at h
        exact ⟨a, by omega, hc, by omega⟩
      · rw [if_neg hc] at h; omega

/-- A conf entry whose prefix has at least the conf entries of the prefix of length `a` is at
or past `a`. -/
theorem confPos_ge_of_count (l : List raftpb.Entry) {a k : Nat} (hk : IsConfPos l k)
    (hc : confCount (l.take a) ≤ confCount (l.take k)) : a ≤ k := by
  refine Nat.le_of_not_lt fun hlt => ?_
  have h1 := confCount_take_mono l (show k + 1 ≤ a by omega)
  rw [confCount_take_succ, if_pos hk] at h1
  omega

theorem confPos_lt_of_count (l : List raftpb.Entry) {k1 k2 : Nat}
    (hc : confCount (l.take k1) < confCount (l.take k2)) : k1 < k2 := by
  refine Nat.lt_of_not_le fun h => ?_
  have := confCount_take_mono l (show k2 ≤ k1 by omega)
  omega

theorem IsConfPos_of_take {l l' : List raftpb.Entry} {m k : Nat} (h : l'.take m = l.take m)
    (hk : k < m) (hp : IsConfPos l k) : IsConfPos l' k := by
  obtain ⟨e, he, hc⟩ := hp
  refine ⟨e, ?_, hc⟩
  have := congrArg (fun x => x[k]?) h
  simp only [List.getElem?_take, hk, ite_true] at this
  rw [this]; exact he

theorem confCount_take_agree {l l' : List raftpb.Entry} {m k : Nat} (h : l'.take m = l.take m)
    (hk : k ≤ m) : confCount (l'.take k) = confCount (l.take k) := by
  have := congrArg (List.take k) h
  simp only [List.take_take, Nat.min_eq_left hk] at this
  rw [this]

/-- The far case "older commit fact" (the paper's section 7, `j_c ≥ j_m + 2`): a log with at
most one conf entry at or past `a` cannot agree up to `k` with a log whose prefix of length `k`
has two more conf entries than its own prefix of length `a`. -/
theorem far_newer {F F0 : List raftpb.Entry} {a k : Nat} (hI1 : ConfI1 F a)
    (hag : F.take k = F0.take k) (hc : confCount (F.take a) + 2 ≤ confCount (F0.take k)) :
    False := by
  have hck : confCount (F.take a) + 2 ≤ confCount (F.take k) := by rw [hag]; exact hc
  obtain ⟨k1, hk1, hp1, he1⟩ := exists_confPos F k (confCount (F.take a)) (by omega)
  obtain ⟨k2, hk2, hp2, he2⟩ := exists_confPos F k (confCount (F.take a) + 1) (by omega)
  have h12 : k1 < k2 := confPos_lt_of_count F (by omega)
  have ha1 : a ≤ k1 := confPos_ge_of_count F hp1 (by omega)
  obtain ⟨e1, he1', hc1⟩ := hp1
  obtain ⟨e2, he2', hc2⟩ := hp2
  have := hI1 k1 k2 e1 e2 h12 he1' he2' hc1 hc2
  omega

/-- The far case "older winner" (the paper's section 7, `j_c ≤ j_m - 2`, and section 5): a
campaign log with at most one conf entry at or past `k` cannot agree, up to and including a conf
entry `k2` of `F`, with `F` when `F`'s prefix before `k2` has one more conf entry than the
campaign's prefix of length `k`. -/
theorem far_older {F F0 : List raftpb.Entry} {k k2 : Nat} (hI1 : ConfI1 F0 k)
    (hag : F0.take (k2 + 1) = F.take (k2 + 1)) (hp2 : IsConfPos F k2)
    (hc : confCount (F.take k2) = confCount (F0.take k) + 1) : False := by
  obtain ⟨k1, hk1, hp1, he1⟩ := exists_confPos F k2 (confCount (F0.take k)) (by omega)
  have hp1' := IsConfPos_of_take hag (by omega) hp1
  have hp2' := IsConfPos_of_take hag (by omega) hp2
  have hc1 : confCount (F0.take k1) = confCount (F.take k1) :=
    confCount_take_agree hag (by omega)
  have hk : k ≤ k1 := confPos_ge_of_count F0 hp1' (by omega)
  obtain ⟨e1, he1', hc1'⟩ := hp1'
  obtain ⟨e2, he2', hc2'⟩ := hp2'
  have := hI1 k1 k2 e1 e2 hk1 he1' he2' hc1' hc2'
  omega

end conf

section model
variable [FfiSyntax]

-- `c` is the node's configuration; `id` the node being described.
variable (c : CfgM) (id : w64)

/-- `Step` at the configuration `c` (see the file header): the rules `campaign`, `win`,
`lose`, `commit` and `readAck` read the voters of both halves; the others are `Step`'s. The
rules' documentation is `Step`'s. -/
inductive StepC : PState → List Msg → PState → Prop where
  | refl (s : PState) : StepC s [] s
  | trans (s₀ : PState) (r₁ : List Msg) (s₁ : PState) (r₂ : List Msg) (s₂ : PState) :
      StepC s₀ r₁ s₁ → StepC s₁ r₂ s₂ → StepC s₀ (r₁ ++ r₂) s₂
  | higherTerm (m : Msg) (s : PState) :
      uint.Z s.term < uint.Z m.term →
      m.dst = id →
      (fromLeader m.ty = true → m.src ≠ id) →
      StepC s [m] (pbecomeFollower s m.term (if fromLeader m.ty then m.src else W64 0))
  | campaign (s : PState) (peers : List w64) (cl : List w8) :
      s.role ≠ .leader →
      id ∈ c.voters →
      uint.Z s.term + 1 < 2 ^ 64 →
      peers ≡ₚ elements (c.voters \ {[id]}) →
      StepC s []
        (psendMsgs (pbecomeCandidate id s)
          ([Msg.plain .voteResp id id (pbecomeCandidate id s).term false] ++
           peers.map (fun dst => pvoteReq id dst (pbecomeCandidate id s).term
                                   (plogLast s.base s.log) cl)))
  | grantVote (m : Msg) (s : PState) :
      m.ty = .vote →
      m.dst = id →
      m.src ≠ W64 0 →
      m.term = s.term →
      PCanVote s m.src →
      plogUpToDate s.base s.log (entryID.mk m.logterm m.index) = true →
      StepC s [m]
        (psendMsgs { s with vote := m.src } [Msg.plain .voteResp id m.src s.term false])
  | rejectVote (m : Msg) (s : PState) :
      m.ty = .vote →
      m.dst = id →
      StepC s [m] (psendMsgs s [Msg.plain .voteResp id m.src s.term true])
  | recordVote (m : Msg) (s : PState) :
      m.ty = .voteResp →
      m.dst = id →
      m.term = s.term →
      s.role = .candidate →
      StepC s [m] { s with votes := recordVote s.votes m.src (!m.reject) }
  | win (s : PState) (mt : GMap w64 w64) (ms : List Msg) :
      s.role = .candidate →
      JQuorum c (granted s.votes) →
      plogLastIndexZ s.base s.log + 1 < 2 ^ 64 →
      LeaderMatchOk id s mt →
      (∀ m ∈ ms, ReplOk id (pwinState id s mt) m) →
      StepC s [] (psendMsgs (pwinState id s mt) ([pselfAck id (pwinState id s mt)] ++ ms))
  | lose (s : PState) :
      s.role = .candidate →
      JLost c s.votes →
      StepC s [] (pbecomeFollower s s.term (W64 0))
  | drain (s : PState) (o' : List Msg) :
      o'.Subperm s.outbox →
      StepC s [] { s with outbox := o' }
  | appAccept (m : Msg) (s : PState) (lastnewi : w64) (es' : List raftpb.Entry) :
      m.ty = .app →
      m.dst = id →
      m.src ≠ id →
      m.term = s.term →
      s.role ≠ .leader →
      uint.Z s.commit ≤ uint.Z m.index →
      plogMaybeAppend s.base s.log (entryID.mk m.logterm m.index) m.entries
        = some (lastnewi, es') →
      (plogFindConflict s.base s.log m.entries = W64 0 ∨
        uint.Z s.commit < uint.Z (plogFindConflict s.base s.log m.entries)) →
      StepC s [m]
        (psendMsgs
          { padoptLeader s m.src with
              log := es',
              commit := plogCommitTo s.commit
                          (if uint.Z m.commit < uint.Z lastnewi then m.commit else lastnewi) }
          [Msg.mk .appResp id m.src s.term false lastnewi (W64 0) (W64 0) (W64 0) []])
  | appStale (m : Msg) (s : PState) :
      m.ty = .app →
      m.dst = id →
      m.src ≠ id →
      m.term = s.term →
      s.role ≠ .leader →
      uint.Z m.index < uint.Z s.commit →
      StepC s [m]
        (psendMsgs (padoptLeader s m.src)
          [Msg.mk .appResp id m.src s.term false s.commit (W64 0) (W64 0) (W64 0) []])
  | appReject (m : Msg) (s : PState) (hint hintterm : w64) :
      m.ty = .app →
      m.dst = id →
      m.src ≠ id →
      m.term = s.term →
      s.role ≠ .leader →
      uint.Z s.commit ≤ uint.Z m.index →
      ¬ PlogMatches s.base s.log (entryID.mk m.logterm m.index) →
      StepC s [m]
        (psendMsgs (padoptLeader s m.src)
          [Msg.mk .appResp id m.src s.term true m.index hintterm (W64 0) hint []])
  | heartbeat (m : Msg) (s : PState) :
      m.ty = .heartbeat →
      m.dst = id →
      m.src ≠ id →
      m.term = s.term →
      s.role ≠ .leader →
      uint.Z m.commit ≤ plogLastIndexZ s.base s.log →
      StepC s [m]
        (psendMsgs
          { padoptLeader s m.src with commit := plogCommitTo s.commit m.commit }
          [{ Msg.plain .heartbeatResp id m.src s.term false with ctx := m.ctx }])
  | beat (s : PState) (ms : List Msg) :
      s.role = .leader →
      (∀ m ∈ ms, HeartbeatOk id s m) →
      (∀ m ∈ ms, HbCtxOk s.rd.ro m.ctx) →
      StepC s [] (psendMsgs s ms)
  | appResp (m : Msg) (s : PState) (x : w64) :
      m.ty = .appResp →
      m.dst = id →
      m.term = s.term →
      s.role = .leader →
      m.reject = false →
      s.matched !! m.src = some x →
      StepC s [m]
        { s with matched :=
            <[m.src := if uint.Z x < uint.Z m.index then m.index else x]> s.matched }
  | commit (s : PState) (n : w64) :
      s.role = .leader →
      uint.Z s.commit < uint.Z n →
      uint.Z n ≤ plogLastIndexZ s.base s.log →
      plogTermAt s.base s.log n = some s.term →
      JQuorum c (ackedBy s n) →
      StepC s [] { s with commit := n }
  | sendApps (s : PState) (ms : List Msg) :
      s.role = .leader →
      (∀ m ∈ ms, ReplOk id s m) →
      StepC s [] (psendMsgs s ms)
  | propose (m : Msg) (s : PState) (ents : List raftpb.Entry) :
      m.ty = .propose →
      PropRepl m.entries ents →
      s.role = .leader →
      plogLastIndexZ s.base s.log + (ents.length : Int) < 2 ^ 64 →
      StepC s [m]
        (psendMsgs (pappend s (ents.mapIdx (stamp s.term (plastIndex s))))
          [pselfAck id (pappend s (ents.mapIdx (stamp s.term (plastIndex s))))])
  | propForward (m : Msg) (s : PState) :
      m.ty = .propose →
      s.role = .follower →
      s.lead ≠ W64 0 →
      StepC s [m]
        (psendMsgs s
          [Msg.mkV .propose id s.lead (W64 0) m.reject m.index m.logterm m.commit
             m.rejecthint m.entries [] m.ctx])
  | snapRestore (m : Msg) (s : PState) :
      m.ty = .snap →
      m.dst = id →
      m.src ≠ id →
      m.term = s.term →
      s.role ≠ .leader →
      uint.Z s.commit < uint.Z m.index →
      ¬ PlogMatches s.base s.log (entryID.mk m.logterm m.index) →
      StepC s [m]
        (psendMsgs
          { padoptLeader s m.src with
              base := entryID.mk m.logterm m.index, log := [], commit := m.index }
          [Msg.mk .appResp id m.src s.term false m.index (W64 0) (W64 0) (W64 0) []])
  | snapFastfwd (m : Msg) (s : PState) :
      m.ty = .snap →
      m.dst = id →
      m.src ≠ id →
      m.term = s.term →
      s.role ≠ .leader →
      uint.Z s.commit < uint.Z m.index →
      PlogMatches s.base s.log (entryID.mk m.logterm m.index) →
      StepC s [m]
        (psendMsgs { padoptLeader s m.src with commit := m.index }
          [Msg.mk .appResp id m.src s.term false m.index (W64 0) (W64 0) (W64 0) []])
  | snapStale (m : Msg) (s : PState) :
      m.ty = .snap →
      m.dst = id →
      m.src ≠ id →
      m.term = s.term →
      s.role ≠ .leader →
      uint.Z m.index ≤ uint.Z s.commit →
      StepC s [m]
        (psendMsgs (padoptLeader s m.src)
          [Msg.mk .appResp id m.src s.term false s.commit (W64 0) (W64 0) (W64 0) []])
  | takeReads (s : PState) :
      StepC s [] ({ s with rd := { s.rd with states := [] } })
  | readFwd (m : Msg) (s : PState) :
      m.ty = .readIndex → s.role ≠ .leader → s.lead ≠ W64 0 →
      StepC s [m] (psendMsgs s [{ m with
        src := if m.src = W64 0 then id else m.src
        dst := s.lead
        term := W64 0 }])
  | readPend (m : Msg) (s : PState) (pm : raftpb.Message) :
      m.ty = .readIndex → s.role = .leader → m.src = pm.From' →
      StepC s [m] ({ s with rd := { s.rd with pend := s.rd.pend ++ [(pm, m.entries)] } })
  | readArrive (m : Msg) (s : PState) :
      m.ty = .readIndex → s.role = .leader →
      plogTermAt s.base s.log s.commit = some s.term →
      StepC s [m] ({ s with rd := { s.rd with
                     ro := readonlyArrive s.rd.ro id ⟨s.commit, m.src, m.entries⟩ } })
  | readRelease (s : PState) :
      s.role = .leader → plogTermAt s.base s.log s.commit = some s.term →
      StepC s [] ({ s with rd := { s.rd with
        pend := []
        ro := readonlyRelease s.rd.ro id s.commit s.rd.pend } })
  | readAck (m : Msg) (s : PState) (N : w64) :
      m.ty = .heartbeatResp → m.dst = id → m.term = s.term → s.role = .leader →
      m.ctx ≠ [] →
      JQuorumAcked c (fun v => ((readonlyRecvAck s.rd.ro m.src m.ctx).acks !! v).getD (W64 0))
        N →
      StepC s [m] (preadRespondAll id
        ({ s with rd := { s.rd with
             ro := (readonlyAdvance (readonlyRecvAck s.rd.ro m.src m.ctx) N).1 } })
        (readonlyAdvance (readonlyRecvAck s.rd.ro m.src m.ctx) N).2)
  | readState (m : Msg) (s : PState) (e : raftpb.Entry) :
      m.ty = .readIndexResp → m.entries = [e] →
      StepC s [m] ({ s with rd := { s.rd with states := s.rd.states ++ [⟨m.index, e.Data'⟩] } })
  | sendFree (s : PState) (m : Msg) :
      (m.ty = .preVote ∨ m.ty = .preVoteResp) →
      m.src = id →
      StepC s [] (psendMsgs s [m])
  | abandon (s : PState) :
      s.role ≠ .leader →
      StepC s [] (pbecomeFollower s s.term (W64 0))
  | zeroAck (s : PState) (dst : w64) :
      StepC s [] (psendMsgs s [Msg.mk .appResp id dst s.term false
                                (W64 0) (W64 0) (W64 0) (W64 0) []])
  | reMatch (s : PState) (mt : GMap w64 w64) :
      s.role = .leader →
      (∀ v i, mt !! v = some i → uint.Z i = 0 ∨ s.matched !! v = some i) →
      StepC s [] { s with matched := mt }

end model

section equiv
variable [FfiSyntax]

/-- `Step` at the voters of a non-joint configuration is `StepC` there. -/
theorem stepC_of_step (c : CfgM) (id : w64) (hi : c.incoming ≠ ∅) (ho : c.outgoing = ∅)
    {s : PState} {ms : List Msg} {s' : PState} (h : Step c.incoming id s ms s') :
    StepC c id s ms s' := by
  have Hv := CfgM.voters_of_out ho
  induction h with
  | refl s => exact .refl s
  | trans _ _ _ _ _ _ _ ih1 ih2 => exact .trans _ _ _ _ _ ih1 ih2
  | campaign s peers cl h1 h2 h3 h4 =>
    exact .campaign s peers cl h1 (Hv ▸ h2) h3 (Hv ▸ h4)
  | win s mt ms h1 h2 h3 h4 h5 => exact .win s mt ms h1 ((JQuorum_of_out hi ho _).2 h2) h3 h4 h5
  | lose s h1 h2 => exact .lose s h1 ((JLost_of_out hi ho _).2 h2)
  | commit s n h1 h2 h3 h4 h5 => exact .commit s n h1 h2 h3 h4 ((JQuorum_of_out hi ho _).2 h5)
  | readAck m s N h1 h2 h3 h4 h5 h6 =>
    exact .readAck m s N h1 h2 h3 h4 h5 ((JQuorumAcked_of_out hi ho _ _).2 h6)
  | _ =>
    first
    | (apply StepC.higherTerm <;> assumption)
    | (apply StepC.grantVote <;> assumption)
    | (apply StepC.rejectVote <;> assumption)
    | (apply StepC.recordVote <;> assumption)
    | (apply StepC.drain <;> assumption)
    | (apply StepC.appAccept <;> assumption)
    | (apply StepC.appStale <;> assumption)
    | (apply StepC.appReject <;> assumption)
    | (apply StepC.heartbeat <;> assumption)
    | (apply StepC.beat <;> assumption)
    | (apply StepC.appResp <;> assumption)
    | (apply StepC.sendApps <;> assumption)
    | (apply StepC.propose <;> assumption)
    | (apply StepC.propForward <;> assumption)
    | (apply StepC.snapRestore <;> assumption)
    | (apply StepC.snapFastfwd <;> assumption)
    | (apply StepC.snapStale <;> assumption)
    | (apply StepC.takeReads <;> assumption)
    | (apply StepC.readFwd <;> assumption)
    | (apply StepC.readPend <;> assumption)
    | (apply StepC.readArrive <;> assumption)
    | (apply StepC.readRelease <;> assumption)
    | (apply StepC.readState <;> assumption)
    | (apply StepC.sendFree <;> assumption)
    | (apply StepC.abandon <;> assumption)
    | (apply StepC.zeroAck <;> assumption)
    | (apply StepC.reMatch <;> assumption)

/-- `StepC` at a non-joint configuration is `Step` at its voters. -/
theorem step_of_stepC (c : CfgM) (id : w64) (hi : c.incoming ≠ ∅) (ho : c.outgoing = ∅)
    {s : PState} {ms : List Msg} {s' : PState} (h : StepC c id s ms s') :
    Step c.incoming id s ms s' := by
  have Hv := CfgM.voters_of_out ho
  induction h with
  | refl s => exact .refl s
  | trans _ _ _ _ _ _ _ ih1 ih2 => exact .trans _ _ _ _ _ ih1 ih2
  | campaign s peers cl h1 h2 h3 h4 =>
    exact .campaign s peers cl h1 (Hv ▸ h2) h3 (Hv ▸ h4)
  | win s mt ms h1 h2 h3 h4 h5 => exact .win s mt ms h1 ((JQuorum_of_out hi ho _).1 h2) h3 h4 h5
  | lose s h1 h2 => exact .lose s h1 ((JLost_of_out hi ho _).1 h2)
  | commit s n h1 h2 h3 h4 h5 => exact .commit s n h1 h2 h3 h4 ((JQuorum_of_out hi ho _).1 h5)
  | readAck m s N h1 h2 h3 h4 h5 h6 =>
    exact .readAck m s N h1 h2 h3 h4 h5 ((JQuorumAcked_of_out hi ho _ _).1 h6)
  | _ =>
    first
    | (apply Step.higherTerm <;> assumption)
    | (apply Step.grantVote <;> assumption)
    | (apply Step.rejectVote <;> assumption)
    | (apply Step.recordVote <;> assumption)
    | (apply Step.drain <;> assumption)
    | (apply Step.appAccept <;> assumption)
    | (apply Step.appStale <;> assumption)
    | (apply Step.appReject <;> assumption)
    | (apply Step.heartbeat <;> assumption)
    | (apply Step.beat <;> assumption)
    | (apply Step.appResp <;> assumption)
    | (apply Step.sendApps <;> assumption)
    | (apply Step.propose <;> assumption)
    | (apply Step.propForward <;> assumption)
    | (apply Step.snapRestore <;> assumption)
    | (apply Step.snapFastfwd <;> assumption)
    | (apply Step.snapStale <;> assumption)
    | (apply Step.takeReads <;> assumption)
    | (apply Step.readFwd <;> assumption)
    | (apply Step.readPend <;> assumption)
    | (apply Step.readArrive <;> assumption)
    | (apply Step.readRelease <;> assumption)
    | (apply Step.readState <;> assumption)
    | (apply Step.sendFree <;> assumption)
    | (apply Step.abandon <;> assumption)
    | (apply Step.zeroAck <;> assumption)
    | (apply Step.reMatch <;> assumption)

/-- The two step relations agree at a non-joint configuration with voters `cfg ≠ ∅`,
whatever its learners: `Step cfg` is `StepC (CfgM.simple cfg lrn)`. -/
theorem step_iff_stepC (cfg lrn : GSet w64) (id : w64) (hne : cfg ≠ ∅)
    (s : PState) (ms : List Msg) (s' : PState) :
    Step cfg id s ms s' ↔ StepC (CfgM.simple cfg lrn) id s ms s' :=
  ⟨stepC_of_step (CfgM.simple cfg lrn) id hne rfl, step_of_stepC (CfgM.simple cfg lrn) id hne rfl⟩

end equiv

end EtcdGrove
end Perennial
