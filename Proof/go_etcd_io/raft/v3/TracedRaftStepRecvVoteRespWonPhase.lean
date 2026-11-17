/-
Lean-first (no Rocq counterpart). **`raft.Step`'s traced bundle on a candidate's won election: the
phases** (2026-11-11, trace-check Q8 stage 1 slice 27b, `notes/decisions.md`, "Q8 stage 1 (slice
27b)").

A candidate's vote response of its term that wins the election logs, in one `Step` call: the receive
line (`HandleRequestVoteResponse`), `becomeLeader`'s `BecomeLeader` line (after `reset`, before the
empty entry's append), the empty entry's `Replicate` line (`ClientRequest`), the self-acknowledgement's
`SendAppendEntriesResponse` line (`AppendEntriesToSelf`) and one `SendAppendEntriesRequest` per peer.
This file has the phases between them:

- **the won tally's quorum** (`isQuorum_of_jquorum`: raft's `JQuorum` at the step's configuration is
  the specification's `isQuorum` of raft's granted voters, given them configured), handed from the
  receive line, where the receive law gives the configured-ness (amendment A6, Q23: `PhaseStepR`'s
  premises, `wonVote_quorum`), to the `BecomeLeader` line in the receive line's result phase
  (`WonRecvPin`, `phaseStepR_voteRespWon`);
- **the leader's phase** (`phaseStepB_becomeLeader`): the idle relation at `becomeLeaderPre`'s state
  with `reset`'s `Match` values, which the event's state (`becomeLeaderPre`, whose `Progress` values
  are still the candidate's) does not carry: the phases name a `Progress` map with them, `wonPvs` (the
  node's own `Match` its last index, every other `0`; `reset`'s once the node is in its own `Progress`
  map, `wonPvs_reset`), the node events reading no `Progress` (`nodeEvOf_prvals`);
- **the empty entry's `Replicate` line** (`phaseStepB_replicateB`: slice 24a's, with the log past the
  bootstrap entries given, `hbl`, since a new leader's last entry is not of its term);
- **the end state** (`wonEnd`: `StepEnd`'s won outcome, the broadcast and `reset`'s `Match` values).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStepPropBundle
public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvVoteResp
public import Proof.go_etcd_io.raft.v3.TracedWinGhost

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section pure
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-! ### `reset`'s `Match` values -/

/-- A `Progress` value with `Match` `li` (the node's own after `reset`). -/
def wonProg (li : w64) : Progress :=
  ⟨li, W64 0, W64 0, .probe, W64 0, false, ⟨0, 0, 0, 0⟩, false⟩

/-- **A `Progress` map with `reset`'s `Match` values**: every peer's `0`, the node's own `li`, the node
in it whether or not it was. -/
def wonPvs (id li : w64) (pvs : GMap w64 Progress) : GMap w64 Progress :=
  <[id := wonProg li]> ((fun p => { p with matched := W64 0 }) <$> pvs)

theorem prvalsMatch_wonPvs (id li : w64) (pvs : GMap w64 Progress) (k : w64) :
    prvalsMatch (wonPvs id li pvs) !! k = if k = id then some li else (pvs !! k).map (fun _ => W64 0) := by
  simp only [prvalsMatch, wonPvs, GMap.fmap_eq, GMap.lookup_fmap]
  by_cases hk : k = id
  · subst hk; rw [GMap.lookup_insert_eq]; simp [wonProg]
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk), GMap.lookup_fmap]
    simp only [hk, ↓reduceIte]
    cases pvs !! k <;> rfl

/-- `wonPvs`' `Match` values are a new leader's (`Step.win`'s premise), at its last index. -/
theorem wonPvs_leaderOk (id li : w64) (pvs : GMap w64 Progress) (ps : PState) (h : plastIndex ps = li) :
    LeaderMatchOk id ps (prvalsMatch (wonPvs id li pvs)) := by
  refine ⟨by rw [prvalsMatch_wonPvs]; simp [h], fun v x hv hx => ?_⟩
  simp only [prvalsMatch_wonPvs, hv, ↓reduceIte] at hx
  cases h' : pvs !! v with
  | none => rw [h'] at hx; cases hx
  | some _ => rw [h'] at hx; simp at hx; exact hx.symm

/-- With the node in its `Progress` map, `wonPvs`' `Match` values are `reset`'s. -/
theorem wonPvs_reset (id li : w64) (pvs : GMap w64 Progress) (hid : id ∈ domSet pvs) :
    prvalsMatch (wonPvs id li pvs) = resetMatched id li pvs := by
  apply GMap.map_eq; intro k
  rw [prvalsMatch_wonPvs, resetMatched, GMap.lookup_imap]
  by_cases hk : k = id
  · subst hk
    obtain ⟨p, hp⟩ := (GMap.elem_of_dom pvs k).1 hid
    simp [hp]
  · simp only [hk, ↓reduceIte]
    cases pvs !! k <;> simp

/-! ### The states -/

/-- `becomeLeader`'s state at its `BecomeLeader` and `Replicate` lines, at `reset`'s `Match` values (the
phases' state; the lines' events read no `Progress`). -/
abbrev wonL (id : w64) (s : NState) (m : MessageM) : NState :=
  { becomeLeaderPre id (votedState s m) with prvals := wonPvs id (logLast s.logst) s.prvals }

/-- The state after the empty entry's append, at `reset`'s `Match` values (the self-acknowledgement's
and the broadcast's phases). -/
abbrev wonLg (id : w64) (s : NState) (m : MessageM) : NState :=
  { becomeLeaderLog id (votedState s m) with prvals := wonPvs id (logLast s.logst) s.prvals }

theorem toPState_wonL (id : w64) (s : NState) (m : MessageM) :
    toPState (wonL id s m) = pbecomeLeader id (toPState (votedState s m))
      (prvalsMatch (wonPvs id (logLast s.logst) s.prvals)) := by
  simp only [toPState, becomeLeaderPre, resetTo, resetTo0, pbecomeLeader, ite_true, rdNL_ite]
  simp [rdNL, proleRole]

/-- The node's last index at the tally's state is the log's. -/
theorem plastIndex_voted (s : NState) (m : MessageM) :
    plastIndex (toPState (votedState s m)) = logLast s.logst := by
  rw [plastIndex_toPState]

/-- The empty entry's `Replicate` state is the appended state. -/
theorem propK_wonL_one (id : w64) (s : NState) (m : MessageM) :
    toPState (propK (wonL id s m) [zero_val EntryM] 1) = toPState (wonLg id s m) := by
  simp [propK, propAppended, toPState, becomeLeaderLog, becomeLeaderPre, leaderEntry, resetTo, resetTo0,
    logAppend]

theorem simIdleS_wonL_one (id : w64) (s : NState) (m : MessageM) (C : List w64) :
    SimIdleS C (propK (wonL id s m) [zero_val EntryM] 1) = SimIdleS C (wonLg id s m) := by
  unfold SimIdleS
  rw [propK_wonL_one]
  rfl

/-! ### The won tally's quorum -/

/-- **Raft's joint quorum is the specification's**: at a configuration whose incoming voters are `C`
(nonempty, no outgoing half), a joint quorum of raft's granted voters (`JQuorum`), all of them
configured (`hv`), is the specification's `isQuorum` of their abstraction (the outgoing half not read). -/
theorem isQuorum_of_jquorum (C : List w64) (c : CfgM) (votes : GMap w64 Bool)
    (hin : (elements c.incoming).Perm C) (hC : C ≠ [])
    (hv : ∀ k w, votes !! k = some w → idAbs k ∈ confAbs C)
    (hq : JQuorum c (granted votes)) :
    Etcdraft.isQuorum
      (Etcdraft.SetIds.mk (((GMap.toList votes).filter (fun p => p.2)).map (fun p => idAbs p.1)))
      (confAbs C) = true := by
  have hnd : C.Nodup := hin.nodup_iff.1 (GMap.NoDup_elements _)
  obtain ⟨x0, hx0⟩ := List.exists_mem_of_ne_nil C hC
  have hne : c.incoming ≠ ∅ := by
    intro h
    have : x0 ∈ c.incoming := (GMap.elem_of_elements _ _).1 (hin.mem_iff.2 hx0)
    rw [h] at this; exact GMap.not_elem_of_empty _ this
  have hIQ := JQuorum_incoming hne hq
  unfold IsQuorum at hIQ
  have hsz : GMap.size c.incoming = C.length := by
    rw [← GMap.length_elements]; exact hin.length_eq
  have hset : granted votes ∩ c.incoming =
      GMap.listToSet (C.filter (fun j => decide (j ∈ granted votes))) := by
    apply GMap.set_eq; intro j
    rw [GMap.elem_of_intersection, GMap.elem_of_list_to_set, List.mem_filter, decide_eq_true_iff,
      ← GMap.elem_of_elements c.incoming j, hin.mem_iff]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  rw [hset, GMap.size_list_to_set _ (hnd.filter _), hsz] at hIQ
  have hgr : ∀ j, j ∈ granted votes ↔ votes !! j = some true := by
    intro j
    unfold granted
    rw [GMap.elem_of_dom, GMap.lookup_filter]
    cases h : votes !! j with
    | none => simp
    | some v => cases v <;> simp
  have hndS : (Etcdraft.SetIds.mk (((GMap.toList votes).filter (fun p => p.2)).map (fun p => idAbs p.1))).Nodup :=
    (setIds_mk_sorted _).imp (fun h => Nat.ne_of_lt h)
  have hsub : (C.filter (fun j => decide (j ∈ granted votes))).map idAbs ⊆
      Etcdraft.SetIds.mk (((GMap.toList votes).filter (fun p => p.2)).map (fun p => idAbs p.1)) := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    rw [List.mem_filter, decide_eq_true_iff, hgr] at hj
    rw [setIds_mk_mem, mem_grantedAbs]
    exact ⟨j, hj.2, rfl⟩
  have hndM : ((C.filter (fun j => decide (j ∈ granted votes))).map idAbs).Nodup :=
    List.Pairwise.map idAbs (fun _ _ h e => h (TraceSim.idAbs_inj.1 e)) (hnd.filter _)
  have hle := List.Nodup.length_le_of_subset hndM hsub
  rw [List.length_map] at hle
  unfold Etcdraft.isQuorum
  rw [Bool.and_eq_true, decide_eq_true_iff, confAbs_length C hnd]
  refine ⟨?_, by omega⟩
  unfold Etcdraft.SetIds.subset
  rw [List.all_eq_true]
  intro x hx
  rw [setIds_mk_mem, mem_grantedAbs] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  rw [List.contains_iff_mem]; exact hv k true hk

/-- **A won election is not lost** (`poll`'s outcome): a joint quorum of grants is a majority of the
voters that did not refuse, in either half. -/
theorem jquorum_not_jlost (c : CfgM) (votes : GMap w64 Bool) (hq : JQuorum c (granted votes)) :
    ¬ JLost c votes := by
  have hdis : ∀ j, j ∈ granted votes → j ∉ rejected votes := by
    intro j hg hr
    unfold granted at hg; unfold rejected at hr
    rw [GMap.elem_of_dom, GMap.lookup_filter] at hg hr
    obtain ⟨v, hv⟩ := hg; obtain ⟨w, hw⟩ := hr
    cases h : votes !! j with
    | none => rw [h] at hv; cases hv
    | some b => rw [h] at hv hw; cases b <;> simp at hv hw
  have hmono : ∀ S : GSet w64, MajQ S (granted votes) → MajQ S (S \ rejected votes) := by
    intro S h
    rcases h with h | h
    · exact .inl h
    · right
      unfold IsQuorum at h ⊢
      have : granted votes ∩ S ⊆ (S \ rejected votes) ∩ S := by
        rw [GMap.elem_of_subseteq]; intro j hj
        rw [GMap.elem_of_intersection] at hj ⊢
        exact ⟨(GMap.elem_of_difference _ _ _).2 ⟨hj.2, hdis j hj.1⟩, hj.2⟩
      have := GMap.subseteq_size this
      omega
  rintro (h | h)
  · exact h (hmono _ hq.1)
  · exact h (hmono _ hq.2)

/-- **The receive line's result phase on a won election**: the tally's pinned idle phase, the
specification's granted voters a quorum of the voters (the `BecomeLeader` guard). -/
abbrev WonRecvPin (s : NState) (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg) :
    List w64 → ServerC → List Etcdraft.Msg → Prop :=
  fun C cs P => IdlePin s C0 cs0 P0 C cs P ∧ Etcdraft.isQuorum cs.votesGranted (confAbs C) = true

/-- `leaderOf` on the share's server (`toC`). -/
def leaderC (srv : Etcdraft.SetIds) (i : Etcdraft.ID) (cs : ServerC) : ServerC :=
  { cs with state := Etcdraft.leader, lead := i,
            matchIndex := srv.map (fun j => if j = i then (cs.log.length : Int) else 0) }

theorem toC_leaderOf (srv : Etcdraft.SetIds) (i : Etcdraft.ID) (a : Etcdraft.Server) :
    toC srv (leaderOf i a) = leaderC srv i (toC srv a) := rfl


end pure

section phases
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] [GoSemanticsFunctions]

/-- **A won vote response's receive line's phase step** (`phaseStepR_voteRespCand`, its result phase
strengthened by the quorum): the receive law's premises (amendment A6, Q23) give the response's source
and the candidate's responded voters configured, so raft's tally's voters are (`votesIn_of_responded`,
`votesIn_recordVote`), its won joint quorum the specification's (`isQuorum_of_jquorum`) and the
specification's granted voters a quorum (`wonVote_quorum`). -/
theorem phaseStepR_voteRespWon (id : w64) (c : CfgM) (s : NState) (m : MessageM)
    (ents : List EntryM) (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg)
    (a0 : Etcdraft.Server) (ha0 : toC (confAbs C0) a0 = cs0)
    (ma : Etcdraft.Msg) (hev : RecvEvTy (absMsg .voteResp m ents) (W64 16)) (hto : m.To' = id)
    (hterm : m.Term' = s.term) (hc : s.role = .candidate)
    (hb : (absMsg .voteResp m ents).NumsBelow traceNumBound)
    (hma : TraceSim.msgAbs C0 C0.length (absMsg .voteResp m ents) = some ma)
    (hq : JQuorum c (granted (recordVote s.votes m.From' (!m.Reject')))) :
    PhaseStepR id c ma (SendEvOf (W64 16) id s c (absMsg .voteResp m ents)) (fun _ => False) (recvPhantoms ma)
      (IdlePin s C0 cs0 P0)
      (WonRecvPin (votedState s m) C0 (toC (confAbs C0) (respSrv a0 ma)) P0) := by
  intro C cs P hΦ hpre e he
  obtain ⟨h1, h2, h3, h4⟩ := phaseStepR_voteRespCand id c s m ents (W64 16) C0 cs0 P0 a0 ha0 ma hev hto hterm hc
    hb hma C cs P hΦ hpre e he
  refine ⟨h1, h2, h3, fun a ha => ?_⟩
  obtain ⟨a', P', hΦ', hsrc, hle⟩ := h4 a ha
  refine ⟨a', P', ⟨hΦ', ?_⟩, hsrc, hle⟩
  obtain ⟨hin, hout, hC, hsC, hresp⟩ := hpre
  obtain ⟨rfl, rfl, rfl, ⟨b0, hb0, hR0, -⟩⟩ := hΦ
  obtain ⟨-, -, -, ⟨b1, hb1, hR1, -⟩⟩ := hΦ'
  have hpre' : s.role ≠ .preCandidate := by rw [hc]; decide
  have hpc : (toPState s).role = .candidate := by simp [toPState_role, hc, proleRole]
  have hvc : (toPState (votedState s m)).role = .candidate := hpc
  -- raft's tally before the response: configured voters
  have hv0 : ∀ k w, s.votes !! k = some w → idAbs k ∈ confAbs C := by
    have hvr := (hR0.2.2.2.2.2.2.2.2.2.1 hpc).1
    have hvs : (toPState s).votes = s.votes := toPState_votes_nonpre _ hpre'
    rw [hvs] at hvr
    refine votesIn_of_responded C s.votes b0.votesResponded hvr (fun k hk => hresp k ?_)
    rw [← hb0]; exact hk
  obtain ⟨-, -, hmsrc, -, -, -, -⟩ := msgAbs_recvTy hev hma
  have hvs1 : (toPState (votedState s m)).votes = recordVote s.votes m.From' (!m.Reject') := by
    simp [toPState, hpre']
  have hT := (hR1.2.2.2.2.2.2.2.2.2.1 hvc).2
  rw [hvs1] at hT
  have hgq := isQuorum_of_jquorum C c _ hin (List.ne_nil_of_mem hC)
    (votesIn_recordVote C s.votes m.From' (!m.Reject') hv0 (by rw [← show ma.source = idAbs m.From' from hmsrc]; exact hsC)) hq
  have hw := wonVote_quorum C s.votes m.From' (!m.Reject') ma b1.votesGranted hmsrc hsC hv0 hT hgq
  have hg : (toC (confAbs C) a').votesGranted = b1.votesGranted := by
    rw [← hb1]; rfl
  rw [hg]; exact hw

/-- **The `BecomeLeader` line's phase step**: from the receive line's result phase (the tally's idle
server, its granted voters a quorum) to the leader's idle server at `becomeLeaderPre`'s state with
`reset`'s `Match` values (`wonL`), the share's server `leaderC`'d, its list kept
(`lineEffect_becomeLeader`, `sim_becomeLeader`). -/
theorem phaseStepB_becomeLeader (id : w64) (c : CfgM) (s : NState) (m : MessageM)
    (C0 : List w64) (cs1 : ServerC) (P0 : List Etcdraft.Msg) (hrole : s.role = .candidate) :
    PhaseStepB id c (NodeEvOf (W64 3) id (becomeLeaderPre id (votedState s m)) c)
      (WonRecvPin (votedState s m) C0 cs1 P0)
      (PinAt (wonL id s m) C0 (leaderC (confAbs C0) (idAbs id) cs1) P0 s.outbox) := by
  rintro C cs P ⟨⟨rfl, rfl, rfl, hI⟩, hq⟩ ⟨hin, hout, hC⟩ e he
  obtain ⟨a1, ha1, hR1, hs1, hP1, bt, bc, bl⟩ := hI
  have hname' : gsStr e.name = "BecomeLeader" := by
    have hname := he.1
    simp only [evtNames] at hname
    have : e.name = go!"BecomeLeader" := by have := hname; simp at this; exact this.symm
    rw [this]; rfl
  refine ⟨he.2.1, by rw [hname']; decide, ?_⟩
  intro a ha
  have hR : SimServerR C C.length (toPState (votedState s m)) a := simServerR_toC (ha1.trans ha.symm) hR1
  have hpre' : s.role ≠ .preCandidate := by rw [hrole]; decide
  have hcand : a.state = Etcdraft.candidate := by
    rw [hR.2.1]; simp [toPState, hrole, proleRole, roleAbs]
  have hcfg : a.config.incoming = confAbs C := by rw [hR.2.2.2.2.2.2.2.1]
  have hq' : Etcdraft.isQuorum a.votesGranted (confAbs C) = true := by
    have : (toC (confAbs C) a).votesGranted = a.votesGranted := rfl
    rw [← this, ha]; exact hq
  have hRL : SimServerR C C.length (toPState (wonL id s m)) (leaderOf (idAbs id) a) := by
    rw [toPState_wonL]
    exact sim_becomeLeader C C.length (toPState (votedState s m)) a id _ hR hs1
      (wonPvs_leaderOk id _ s.prvals _ (plastIndex_voted s m))
  have hsL : LogShapeOk C.length (toPState (wonL id s m)) := hs1
  have he' : NodeEvOf (W64 3) id (wonL id s m) c e := he
  refine ⟨leaderOf (idAbs id) a, [], ⟨rfl, by rw [toC_leaderOf, ha], by rw [List.append_nil],
    ⟨leaderOf (idAbs id) a, rfl, hRL, hsL, bt, bc, bl⟩, ?_⟩, by simp, ?_⟩
  · rw [List.append_nil, hP1]; exact List.Perm.refl _
  · exact lineEffect_becomeLeader C e id (wonL id s m) c a _ he' hin hout hC hcand hcfg hq' hRL hsL rfl bt bc bl

/-- **The idle relation after a `Replicate` line, the log past the bootstrap entries given** (`hbl`:
slice 24a's `simIdleS_rep` derives it from a last entry of the leader's term, which a new leader's is
not). -/
theorem simIdleS_repB (C : List w64) (s : NState) (es : List EntryM) (k : Nat) (e : EntryM)
    (he : es[k]? = some e) (hbl0 : C.length ≤ (toPState s).log.length)
    (hbnd : plogLastIndexZ (toPState s).base (toPState s).log + es.length < 2 ^ 63)
    (cs : ServerC) (h : SimIdleS C (propK s es k) cs) : SimIdleS C (propK s es (k + 1)) (repC cs) := by
  obtain ⟨a0, ha0, hR0, hs, bt, bc, bl⟩ := h
  have hk : k < es.length := (List.getElem?_eq_some_iff.1 he).1
  have hbl : C.length ≤ (toPState (propK s es k)).log.length := by rw [propK_len]; omega
  have hst : (stamp s.term (logLast s.logst) k e).Term' = (propK s es k).term := rfl
  have hR1 := simServerR_append C C.length (propK s es k) _ a0 hR0 hbl hst
  have hs1 := logShapeOk_append C.length (propK s es k) _ hs hbl (stamp_index_propK s es k e hk hbnd)
  rw [← propK_succ s es k e he] at hR1 hs1
  refine ⟨repSrv a0, by rw [toC_repSrv_eq, ha0], hR1, hs1, bt, bc, ?_⟩
  have hb0 : uint.Z s.logst.prev.index' = 0 := by
    have := hs.1; simp only [toPState, propK, propAppended, logAppend] at this; rw [this]; rfl
  simp only [plastIndex, plogLastIndexZ]
  rw [propK_len]
  simp only [toPState, propK, propAppended, logAppend] at hbnd ⊢
  simp only [plogLastIndexZ] at hbnd
  have hmin : min (k + 1) es.length ≤ es.length := Nat.min_le_right _ _
  rw [hb0] at hbnd ⊢
  have hL' : ((s.logst.sents ++ s.logst.uents).length : Int) + es.length < 2 ^ 63 := by omega
  generalize min (k + 1) es.length = n at hmin ⊢
  generalize (s.logst.sents ++ s.logst.uents).length = L at hL' ⊢
  have : ((L + n : Nat) : Int) < 2 ^ 63 := by push_cast; omega
  word

/-- **A `Replicate` line's phase step, the log past the bootstrap entries given** (`phaseStepB_replicate`
with `simIdleS_repB`). -/
theorem phaseStepB_replicateB (id : w64) (c : CfgM) (s : NState) (es : List EntryM) (o : List Msg)
    (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg)
    (k : Nat) (e : EntryM) (he : es[k]? = some e) (hlead : s.role = .leader)
    (hbl0 : C0.length ≤ (toPState s).log.length)
    (hbnd : plogLastIndexZ (toPState s).base (toPState s).log + es.length < 2 ^ 63) :
    PhaseStepB id c (NodeEvOf (W64 5) id s c) (RepPin s es o C0 cs0 P0 k) (RepPin s es o C0 cs0 P0 (k + 1)) := by
  rintro C cs P ⟨rfl, rfl, rfl, hI, hP⟩ ⟨-, hout, hC⟩ ev hev
  refine ⟨hev.2.1, isBootstrapName_bf _ (nodeEvOf_notBoot hev (by decide) (by decide) (by decide)), ?_⟩
  intro a ha
  have hst : a.state = Etcdraft.leader := simIdleS_leader hlead (by rw [ha]; exact hI)
  have hI1 := simIdleS_repB C s es k e he hbl0 hbnd _ hI
  have hle := lineEffect_replicate C ev id s c a (fun _ => False) hev hout hC hst
  refine ⟨repSrv a, [], ⟨rfl, by rw [toC_repSrv_eq, ha]; rfl, List.append_nil _, by
    rw [toC_repSrv_eq, ha]; exact hI1, by rw [List.append_nil]; exact hP⟩, fun _ h => (by cases h), hle⟩


end phases

section endst
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- **The end state of a won election** (`StepEnd`'s won outcome; `raft__Step/VoteWin.lean`'s
`voteWin_end`, which a module outside `raft__Step/` may not import, from the outbox's growth instead of
the close's log: a pending or lost tally queues nothing): the won state's broadcast `ms` with `reset`'s
`Match` values. -/
theorem wonEnd {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM} {ctx : List w8}
    {s s' : NState} (hty : m.Type' = MsgVoteResp) (hrole : s.role = .candidate) (hterm : m.Term' = s.term)
    (hlen : s.outbox.length < s'.outbox.length) (Hend : StepEnd c id m ents ctx s s') :
    ∃ (ms : List Msg) (pvs : GMap w64 Progress),
      s' = { sendMsgs (becomeLeader id (votedState s m)) ms with prvals := pvs } ∧
      prvalsMatch pvs = resetMatched id (logLast s.logst) s.prvals := by
  have hety : StepEndTy m.Type' := by rw [hty]; unfold StepEndTy; simp
  have hns : ¬ StaleMsg s m := fun h => absurd h.2 (by rw [hterm]; omega)
  have hnh : m.Type' ≠ MsgHup := by rw [hty]; simp only [MsgVoteResp, MsgHup, ne_eq]; exact of_decide_eq_true rfl
  have hnv : m.Type' ≠ MsgVote := by rw [hty]; simp only [MsgVoteResp, MsgVote, ne_eq]; exact of_decide_eq_true rfl
  have hnbf : ¬ PreBF m s := fun h => absurd h.1 (by rw [hterm]; omega)
  obtain ⟨pvs0, h⟩ := (Hend hety).2.2.2 hns hnh hnv
  rw [show preState s m pvs0 = s by simp [preState, hnbf]] at h
  obtain ⟨scfg, sv, d, c', hf⟩ := h.2.1 (.inl hrole)
  unfold CandidateStepResultC at hf
  obtain ⟨-, hf⟩ := hf
  rw [ite_eq_left hty] at hf
  obtain ⟨-, hf⟩ := hf
  rw [ite_eq_right (by rw [hrole]; decide)] at hf
  obtain ⟨won, lost, ms, pvs, hw, hl, -, hs'⟩ := hf
  cases won with
  | true =>
    obtain ⟨-, -, hpm⟩ := hw rfl
    refine ⟨ms, pvs, ?_, hpm⟩
    rw [hs']
    simp [voteRespResult]
  | false =>
    exfalso
    rw [hs'] at hlen
    cases lost <;> simp [voteRespResult, becomeFollower, resetTo, resetTo0] at hlen

end endst

end EtcdGrove
end Perennial
