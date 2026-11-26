/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: a leader's commit `Ready` (#33 S4, `antSim_ready`; parity B1)

The `cmt` kind (`ReadyKind.cmt`: a leader's new commit, on an acknowledgement received or its own
in `Advance`): `InMemory`'s `cmt` (`inMemory_lcommit`) and `OnDisk` (`onDisk_lcommit`) evaluated,
the side conditions `ReadyOk`. Raft's quorum of `Match` values (`CmtOk` at the initial voters
`R.voters0`) is the binding's `Acked` quorum (B 252) of the initial configuration
(`jq_isQuorum`) through `LeaderPart`'s ack facts (`quietP_reach` carries them to the `Ready`'s
state).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Ready

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open AntCheck go_etcd_io.raft.v3 GMap

theorem cmt_precand_ne_leader : (go!"precandidate" : Str) ≠ leader := by decide

section cmt
variable [GooseExts]

/-! ## Quorums of the initial voters -/

/-- The initial voters are `K` ids. -/
theorem size_voters0 (R : RunCfg) : size R.voters0 = R.K := by
  have hK := R.hK
  have hnd : ((List.range R.K).map fun (i : Nat) => W64 ((i : Int) + 1)).Nodup := by
    unfold List.Nodup
    rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp_of_mem fun ha hb hab e =>
      Nat.ne_of_lt hab (small_inj (by have := List.mem_range.mp ha; omega)
        (by have := List.mem_range.mp hb; omega) e)
  have h := size_eq_length_set R.voters0 _ hnd (fun x => by
    unfold RunCfg.voters0; exact (elem_of_list_to_set x _).symm)
  rw [h, List.length_map, List.length_range]

/-- A member of the initial voters is a node's id, the node among the first `K`. -/
theorem mem_voters0_iff {R : RunCfg} {x : w64} :
    x ∈ R.voters0 ↔ ∃ j : Fin R.N, j.val < R.K ∧ x = nodeId j := by
  constructor
  · intro h
    unfold RunCfg.voters0 at h
    rw [elem_of_list_to_set, List.mem_map] at h
    obtain ⟨i, hi, rfl⟩ := h
    have hi := List.mem_range.mp hi
    exact ⟨⟨i, by have := R.hK; omega⟩, hi, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact (mem_voters0 R j.isLt).mpr hj

/-- **A quorum of the initial voters** (raft's `JQuorum` at `CfgM.simple R.voters0 ∅`) holds more
than half of the `K` voters: a list `l` of nodes, none twice, each among the first `K` with its
id in the quorum, `K < 2 * l.length`. -/
theorem jq_voters {R : RunCfg} {Q : GSet w64} (hq : JQuorum (CfgM.simple R.voters0 ∅) Q) :
    ∃ l : List (Fin R.N), l.Nodup ∧ (∀ j ∈ l, j.val < R.K ∧ nodeId j ∈ Q) ∧ R.K < 2 * l.length := by
  classical
  have hsz := size_voters0 R
  have hq1 : R.K < 2 * size (Q ∩ R.voters0) := by
    rcases hq.1 with h0 | h1
    · exfalso
      have h0' : R.voters0 = ∅ := h0
      have : size R.voters0 = 0 := by rw [h0']; exact size_empty
      have := R.hK.1
      omega
    · have h1' : size R.voters0 < 2 * size (Q ∩ R.voters0) := h1
      omega
  refine ⟨(List.finRange R.N).filter (fun j => decide (j.val < R.K ∧ nodeId j ∈ Q)),
    (List.nodup_finRange R.N).sublist (by apply List.filter_sublist),
    fun j hj => of_decide_eq_true (List.mem_filter.mp hj).2, ?_⟩
  have hsub : elements (Q ∩ R.voters0) ⊆
      ((List.finRange R.N).filter (fun j => decide (j.val < R.K ∧ nodeId j ∈ Q))).map nodeId := by
    intro x hx
    rw [elem_of_elements, elem_of_intersection] at hx
    obtain ⟨hxQ, hxV⟩ := hx
    obtain ⟨j, hj, rfl⟩ := mem_voters0_iff.mp hxV
    exact List.mem_map.mpr ⟨j, List.mem_filter.mpr ⟨List.mem_finRange j, decide_eq_true ⟨hj, hxQ⟩⟩, rfl⟩
  have := (NoDup_elements (Q ∩ R.voters0)).length_le_of_subset hsub
  rw [length_elements, List.length_map] at this
  omega

/-- **Two nodes of a quorum** of the initial voters, when there are at least two voters. -/
theorem jq_two {R : RunCfg} {Q : GSet w64} (hq : JQuorum (CfgM.simple R.voters0 ∅) Q) (hK : 2 ≤ R.K) :
    ∃ a b : Fin R.N, a ≠ b ∧ nodeId a ∈ Q ∧ nodeId b ∈ Q := by
  obtain ⟨l, hnd, hl, hlen⟩ := jq_voters hq
  rcases l with _ | ⟨a, _ | ⟨b, t⟩⟩
  · simp only [List.length_nil] at hlen; omega
  · simp only [List.length_cons, List.length_nil] at hlen; omega
  · refine ⟨a, b, fun e => (List.nodup_cons.mp hnd).1 (by rw [e]; exact List.mem_cons_self ..),
      (hl a (List.mem_cons_self ..)).2, (hl b (List.mem_cons_of_mem _ (List.mem_cons_self ..))).2⟩

/-- **A node of a quorum other than `n`**, when there are at least two initial voters. -/
theorem jq_other {R : RunCfg} {Q : GSet w64} (hq : JQuorum (CfgM.simple R.voters0 ∅) Q) (hK : 2 ≤ R.K)
    (n : Fin R.N) : ∃ j : Fin R.N, j ≠ n ∧ nodeId j ∈ Q := by
  obtain ⟨a, b, hab, ha, hb⟩ := jq_two hq hK
  by_cases han : a = n
  · exact ⟨b, fun h => hab (han.trans h.symm), hb⟩
  · exact ⟨a, han, ha⟩

/-- **A quorum of the initial voters** (raft's `JQuorum (CfgM.simple R.voters0 ∅)`) whose members'
names are in `s` makes `s` a quorum of the binding's initial configuration (`IsQuorum`, R 129,
at `R.cfg.initConf`: `cin` the first `K` names, `cout` empty). -/
theorem jq_isQuorum {R : RunCfg} {Q : GSet w64} {s : SSet} (hq : JQuorum (CfgM.simple R.voters0 ∅) Q)
    (hs : ∀ j : Fin R.N, nodeId j ∈ Q → s.has (nameOf (nodeId j)) = true) :
    isQuorum s R.cfg.initConf = true := by
  obtain ⟨l, hnd, hl, hlen⟩ := jq_voters hq
  have hsub : l.map (fun j => nameOf (nodeId j)) ⊆ s.filter (fun x => SSet.has (namesL R.K) x) := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hjK, hjQ⟩ := hl j hj
    refine List.mem_filter.mpr ⟨by simpa [SSet.has] using hs j hjQ, ?_⟩
    exact server_has (⟨j.val, hjK⟩ : Fin R.K)
  have hnd' : (l.map (fun j => nameOf (nodeId j))).Nodup := by
    unfold List.Nodup; rw [List.pairwise_map]
    exact hnd.imp fun h e => h (name_inj e)
  have h2 := hnd'.length_le_of_subset hsub
  rw [List.length_map] at h2
  have hl3 : (namesL R.K).length = R.K := namesL_length R.K
  unfold isQuorum majority interCount Config.initConf
  rw [R.initVoters_eq]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.length_nil, beq_self_eq_true, Bool.true_or,
    and_true, hl3]
  omega

/-- The binding's view of a configuration whose voters are the initial ones, not joint: the
initial configuration. -/
theorem confView_voters0 {R : RunCfg} {cs : CCState} (h : cs.cfg = CfgM.simple R.voters0 ∅) :
    confView R.N cs = R.cfg.initConf := by
  have e : confView R.N cs = confView R.N R.c0 := by unfold confView; rw [h]; rfl
  rw [e, confView_c0]

/-- An ack fact from `j` to `n` at `t` with index at least `k` puts `j` in `Acked(n, t, k)`
(R 344-347). -/
theorem acked_of {R : RunCfg} {S : State} (hc : S.cfg = R.cfg) {n j : Fin R.N} {t k : Int}
    (h : AckIn S (nameOf (nodeId j)) (nameOf (nodeId n)) t k) :
    (S.acked n.val t k).has (nameOf (nodeId j)) = true := by
  obtain ⟨a, ha, h1, h2, h3, h4, h5⟩ := h
  unfold State.acked
  simp only [SSet.has, List.contains_iff_mem]
  rw [server_of hc n]
  have hmem : nameOf (nodeId j) ∈ S.cfg.server := by
    have := server_has j
    rw [hc, R.server_eq]; simpa [SSet.has] using this
  refine mem_foldl_setAdd (P := fun j' => (S.msgs.any (fun a => a.type == go!"ack" && a.src == j' &&
      a.dst == nameOf (nodeId n) && a.term == t && decide (a.index ≥ k))) = true)
    (nameOf (nodeId j)) S.cfg.server [] (.inr ⟨hmem, ?_⟩)
  exact List.any_eq_true.mpr ⟨a, ha, by simp [h1, h2, h3, h4, h5]⟩


/-! ## The leader's term and `termLen` -/

/-- Setting a term's value twice is setting it to the second value. -/
theorem with_with {α : Type} (f : TermFn α) (t : Int) (v w : α) :
    (f.with t v).with t w = f.with t w := by
  induction f with
  | nil => simp [TermFn.with]
  | cons p ps ih =>
    by_cases h1 : t ≤ p.1
    · have e1 : TermFn.with (p :: ps) t v = (t, v) :: (if p.1 = t then ps else p :: ps) := by
        simp only [TermFn.with, if_pos h1]
      have e2 : TermFn.with (p :: ps) t w = (t, w) :: (if p.1 = t then ps else p :: ps) := by
        simp only [TermFn.with, if_pos h1]
      rw [e1, e2]
      simp only [TermFn.with, Int.le_refl, if_true]
    · have e1 : TermFn.with (p :: ps) t v = p :: TermFn.with ps t v := by
        simp only [TermFn.with, if_neg h1]
      have e2 : TermFn.with (p :: ps) t w = p :: TermFn.with ps t w := by
        simp only [TermFn.with, if_neg h1]
      rw [e1, e2]
      simp only [TermFn.with, if_neg h1, ih]

/-- The binding's leader role is raft's (a pre-candidate is reported as `precandidate`). -/
theorem roleS_eq_leader {v : NodeView} (h : roleS v = leader) : v.ps.role = .leader := by
  unfold roleS roleStr at h
  split at h
  · exact absurd h cmt_precand_ne_leader
  · exact (roleOf_leader_iff _).mp h

/-- **Election safety in the binding**: a leader `k` at its term, and a leader record of `n` at that
term, are the same node (`GlobalOk`'s leaders are raft's, `RaftLaws`' election safety). -/
theorem lead_unique {R : RunCfg} {dec : CCDec} {S : State} {V : Fin R.N → NodeView} {net : List Msg}
    {xnet : List XMsg} {G : RaftFacts} {n k : Fin R.N}
    (hs : AntSim R dec S V net xnet) (hgo : GlobalOk R S net G) (hl : RaftLaws G)
    (hdk : ∀ k : Fin R.N, (V k).dur = durOf (V k).r)
    (hk : S.role[k.val]! = leader)
    (hn : S.leaders.contains { server := nameOf (nodeId n), term := S.currentTerm[k.val]! } = true) :
    k = n := by
  have hv := hs.2.2.2.2 k
  have hvk : (V k).ps.role = .leader := by
    have h := hv.mem.1
    rw [hk] at h
    exact roleS_eq_leader h.symm
  have hkm := List.contains_iff_mem.mp (hv.leader hvk).1
  have hnm := List.contains_iff_mem.mp hn
  obtain ⟨a, ta, ha, hsa, hta⟩ := hgo.1 _ hnm
  obtain ⟨b, tb, hb, hsb, htb⟩ := hgo.1 _ hkm
  have hct : S.currentTerm[k.val]! = uint.Z (V k).ps.term := by rw [hv.disk.1, hdk k]; rfl
  have hta' : S.currentTerm[k.val]! = uint.Z ta := hta
  have htb' : uint.Z (V k).ps.term = uint.Z tb := htb
  have htt : ta = tb := uint_Z_inj.mp (by omega)
  have hab : a = b := hl.1 _ ha _ hb htt
  have hsa' : nameOf (nodeId n) = nameOf a := hsa
  have hsb' : nameOf (nodeId k) = nameOf b := hsb
  exact name_inj (by rw [hsb', hsa', hab])

/-- **A quiet step's state along `ReachP`** (`quiet_reach` read on the protocol): `QKeep` from the
view's state, for a step that keeps the role, term and log. -/
theorem quietP_reach {R : RunCfg} {kk : NodeK} {c : CfgM} {S : State} {net : List Msg}
    {n : Fin R.N} {v : NodeView} {ps₁ : PState}
    (hc : S.cfg = R.cfg) (hnet : NetOk R S net) (hqs : ∀ q ∈ v.qs, QsOk S n v q)
    (hct : S.currentTerm[n.val]! = uint.Z v.ps.term) (hin : ∀ m ∈ net, InMsg m)
    (hr : ReachP kk c (nodeId n) net v ps₁)
    (hro : ps₁.role = v.ps.role) (ht : ps₁.term = v.ps.term) (hl : ps₁.log = v.ps.log) :
    QKeep S n v.ps ps₁ := by
  cases hr with
  | stay _ => exact QKeep.refl
  | recv m _ _ _ _ hmn hmd hm0 hs =>
    exact quiet_recv hc hnet hmn hmd (hin m hmn).2.2.1 hm0 hct (hin m hmn).1 hs hro ht hl
  | tick _ _ _ hs => exact quiet_tick hs ht
  | propose d _ _ _ hs => exact quiet_propose hs hl
  | advance _ _ _ _ ha =>
    refine (quiet_adv_run hc hct (fun q hq => ?_) ha rfl).2.2 hro
    obtain ⟨h1, h2, h3, h4, h5⟩ := hqs q hq
    refine ⟨⟨h1, h2, h3, h4, h5.imp (fun h => h.1) (fun h => h.1)⟩, fun hty => ?_, fun hty => ?_⟩
    · rcases h5 with h5 | h5
      · exact h5.2.2
      · rw [h5.1] at hty; cases hty
    · rcases h5 with h5 | h5
      · rw [h5.1] at hty; cases hty
      · exact h5.2

/-- **Normal entries leave the configuration**: the fold of entries none of which is a conf change
(type 0) is its start. -/
theorem cfgFold_normal {dec : CCDec} {s : CCState} {l : List EntryM} (h : EntsNormal l) :
    cfgFold dec s l = some s := by
  unfold cfgFold
  suffices hs : ∀ pre : List EntryM, cfgFoldFrom dec pre s l = some s from hs []
  induction l with
  | nil => intro pre; rfl
  | cons e l ih =>
    intro pre
    have hn : ¬ IsConfEnt e := by
      have h0 : e.Type' = W32 0 := h e (List.mem_cons_self ..)
      have e0 : uint.Z (W32 0) = 0 := rfl
      have e1 : uint.Z (W32 1) = 1 := rfl
      have e2 : uint.Z (W32 2) = 2 := rfl
      rintro (hc | hc)
      · have h' : uint.Z (W32 0) = uint.Z (W32 1) := by rw [← h0, hc]
        rw [e0, e1] at h'; omega
      · have h' : uint.Z (W32 0) = uint.Z (W32 2) := by rw [← h0, hc]
        rw [e0, e2] at h'; omega
    simp only [cfgFoldFrom, entStep_not_conf dec pre s e hn, Option.bind_some]
    exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) _

variable {R : RunCfg} {dec : CCDec} {S : State} {V : Fin R.N → NodeView} {net : List Msg}
  {xnet : List XMsg} {evs : List Event} {G : RaftFacts} {n : Fin R.N} {r₁ : RState} {rd : ReadyD}
  {S1 : State}

set_option maxHeartbeats 4000000 in
/-- **`antSim_ready` for a leader's commit** (`ReadyKind.cmt`). The `Acked` quorum (B 252) is read
in the leader configuration at the node's term, the initial one: with conf changes off the leader
log has no conf entry (`LedConfOk`), so its fold is the start (`cfgFold_normal`). -/
theorem ready_cmt (hx : RdCtx R dec S V net xnet evs G n r₁ rd S1)
    (hvl : (V n).ps.role = .leader) (hpl : r₁.p.role = .leader) (hpt : r₁.p.term = (V n).ps.term)
    (hpv : r₁.p.vote = (V n).ps.vote) (hplog : r₁.p.log = (V n).ps.log) (hents : rd.ents = [])
    (hlt : uint.Z (V n).ps.commit < uint.Z r₁.p.commit)
    (hcm : CmtOk (CfgM.simple R.voters0 ∅) r₁.p r₁.p.commit) (hns : NoSelf (nodeId n) r₁.p) :
    ReadyGoal R dec V net xnet evs G n r₁ rd := by
  have hbE := reach_byE hx.hr hx.hro hx.hrep
  have hb := hx.hs1.2.1
  have hnet := hx.hs1.2.2.1
  have hv := hx.hs1.2.2.2.2 n
  have hc : S1.cfg = R.cfg := hx.hc
  have hsh := hx.hs1.1
  have hrl : S1.role.length = R.N := hsh.2.2.2.2.2.2.1
  have hn3 := hx.hn3
  have hfl : r₁.full = r₁.p.log := hx.hfl
  obtain ⟨lp1, lp2, lp3, lp4, lp5⟩ := hv.leader hvl
  have hfull : logOf (V n).r.full = logOf (V n).ps.log := by
    rw [← hx.d3, hv.disk.2.2.1, hx.hdk n]; rfl
  have hlenF : (V n).r.full.length = (V n).ps.log.length := by
    have := congrArg List.length hfull
    rw [logOf_length, logOf_length] at this; exact this
  have hMO : MatchOk S1 n r₁.p :=
    (quietP_reach hc hnet hv.qs hx.d1 hx.hin hx.hr (hpl.trans hvl.symm) hpt hplog).2.2.1 hpl ⟨lp3, lp4⟩
  have hbase : r₁.p.base = base0 := hx.hro.2.2.2.2.2.2.2.2.2.2.1
  have hT : S1.currentTerm[n.val]! = uint.Z r₁.p.term := by rw [hx.d1, hpt]
  have hlogn : S1.log[n.val]! = logOf r₁.p.log := by rw [hx.d3, hplog]
  have hrole : S1.role[n.val]! = leader := by rw [hx.d5, hvl]; rfl
  have hll : S1.ledLog.get (uint.Z r₁.p.term) = .ok (logOf r₁.p.log) := by
    rw [hpt, hplog, ← hfull]; exact lp2
  have hlc : S1.ledConf.get (uint.Z r₁.p.term) = .ok R.cfg.initConf := by
    obtain ⟨l, a, cs, -, -, h3, h4, h5⟩ := hb.ledConfOk _ (TermFn.has_of_get hll)
    have e : cfgFold dec R.c0 (l.take a) = some R.c0 :=
      cfgFold_normal (fun e he => h5 hx.hcc e (List.mem_of_mem_take he))
    rw [h3] at e
    rw [h4, Option.some.inj e, confView_c0]
  have hcG : r₁.p.log.take (uint.nat r₁.p.commit) = G.committed.take (uint.nat r₁.p.commit) := by
    rw [← hfl]; exact hx.hrf.2.2.1
  have hcL0 : uint.Z r₁.p.commit ≤ r₁.p.log.length := by
    have := nat_commit_le hx.hrf; rw [hfl] at this; exact this
  have hcL : uint.Z r₁.p.commit ≤ (logOf r₁.p.log).length := by rw [logOf_length]; exact hcL0
  have hc0 : 0 < uint.Z r₁.p.commit := by have := uint_Z_nonneg (V n).ps.commit; omega
  have hcmi : S1.commitIndex[n.val]! < uint.Z r₁.p.commit := by rw [hx.d4]; exact hlt
  have hk : tlOld S1.termLen (uint.Z r₁.p.term) < uint.Z r₁.p.commit := by
    have := (hb.termLenOk.2 n hrole).2; rw [hT] at this; omega
  have hplT : plogTermAt base0 r₁.p.log r₁.p.commit = some r₁.p.term := by rw [← hbase]; exact hcm.2.1
  have hterm : termAt (logOf r₁.p.log) (uint.Z r₁.p.commit) = uint.Z r₁.p.term := (termAt_of_plog hplT).2
  have hq : isQuorum (S1.acked n.val (uint.Z r₁.p.term) (uint.Z r₁.p.commit)) R.cfg.initConf = true :=
    jq_isQuorum hcm.2.2 fun j hj => by
      obtain ⟨y, hy, hle⟩ := mem_ackedBy.mp hj
      have hmo : matchOf r₁.p (nodeId j) = y := by unfold matchOf; rw [hy]; rfl
      exact acked_of hc (hMO.1 j r₁.p.commit (by rw [hmo]; exact hle) hcm.2.1)
  have hcGc := hx.hrf.2.2.2.1
  have hm' := inMemory_lcommit n hc (V n).byE hbE r₁.p.term r₁.p.vote r₁.p.commit (logOf r₁.p.log)
    R.cfg.initConf hrole hT hll hlc hcL hc0 hk hterm hq (cs_ok hx.hgo1.2.2.2.2.1 hcG)
    (lc_ok hx.hl hx.hgo1.2.2.2.1 hcGc hcG)
  -- the new `chain` and `termLen`
  have himax : imax (tlOld S1.termLen (uint.Z r₁.p.term)) (uint.Z r₁.p.commit) = uint.Z r₁.p.commit := by
    unfold imax; split <;> omega
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := commit_fields (n := n) (T := r₁.p.term) hb hx.hgo1 hcL0 hcG
    hx.hrf.2.1 hcGc hcmi
  simp only [hcmi, true_and, himax] at f1 f2 f3 f4 f5 f6 f7
  generalize hch : (if (S1.chain.length : Int) < uint.Z r₁.p.commit then
    (logOf r₁.p.log).take (uint.Z r₁.p.commit).toNat else S1.chain) = ch at f1 f2 f3 f4 f5 f6 f7 hm'
  generalize htl : S1.termLen.with (uint.Z r₁.p.term) (uint.Z r₁.p.commit) = tl at f1 f2 f3 f4 f5 f6 f7 hm'
  have hsend : sendableIn S1.leaders S1.ledLog ch tl (AppendFact.mk (nameOf (nodeId n))
      (nameOf (nodeId n)) (uint.Z r₁.p.term) 0 0 [] (uint.Z r₁.p.commit)) = .ok true := by
    have h := sendable_leader (S := { S1 with chain := ch, termLen := tl }) (src := nameOf (nodeId n))
      (dst := nameOf (nodeId n)) (lg := r₁.p.log) (T := uint.Z r₁.p.term) (p := 0) (pt := 0) (es := [])
      (c := uint.nat r₁.p.commit) (by rw [hpt]; exact lp1) hll (by unfold termAt; simp) (Nat.zero_le _) rfl
      (.inr ⟨by word, by have := f2.1; word,
        by obtain ⟨q, hq, h1, h2⟩ := f4.resolve_left (by omega); exact ⟨q, hq, h1, by word⟩,
        by have := f2.2; rw [uZ_toNat_nat] at this; exact this⟩)
    have e : ((uint.nat r₁.p.commit : Nat) : Int) = uint.Z r₁.p.commit := by word
    rw [e] at h; exact h
  obtain ⟨p, hpm, hod⟩ := onDisk_lcommit n hc (V n).byE r₁.p.term r₁.p.vote r₁.p.commit
    (if (V n).byE = go!"recv" then S1.pending[n.val]! else []) (S1.role.set n.val leader) S1.leaders
    S1.ledLog ch tl S1.viol hT.symm (by rw [hx.d2, hpv]) (get!_set_self _ hn3) hsend hcmi
    (by rw [hlogn]; exact hcL)
    ⟨by rw [lp5.1, hpt], by have := lp5.2; rw [hlenF, ← hplog] at this; omega⟩
    (by rw [hlogn]; exact cs_ok f6 hcG) (by rw [hlogn]; exact lc_ok hx.hl hx.hgo1.2.2.2.1 hcGc hcG)
    (by rw [hlogn]; exact ch_ok f6 hcG)
  have hchl : ¬ (S1.commitIndex[n.val]! < uint.Z r₁.p.commit ∧ (ch.length : Int) < uint.Z r₁.p.commit) :=
    fun h => by have := f2.1; omega
  have htl2 : tl.with (uint.Z r₁.p.term) (imax (tlOld tl (uint.Z r₁.p.term)) (uint.Z r₁.p.commit)) = tl := by
    rw [← htl, tlOld_with, if_pos rfl, with_with]
    unfold imax; simp
  rw [if_neg hchl, htl2] at hod
  unfold ReadyGoal
  rw [hpl, hents]
  have hcf : (S1.confirmed.set n.val (S1.confirmed[n.val]!))[n.val]! = S1.confirmed[n.val]! :=
    get!_set_self _ (by rw [hsh.2.2.2.2.2.2.2.2.2.2.1]; exact n.isLt)
  have ha := hx.ha
  refine hx.finish (ready_of hx.hq0 hm' rfl (queued_ready _ _ _ _ _ _ _ _ _) hod) ?_
  exact {
    hterm := rfl
    tge := Int.le_of_eq hT
    hvote := .inl ⟨hT.symm, by show S1.vote n.val = nameOf r₁.p.vote; rw [hx.d2, hpv]⟩
    hlog := hlogn
    hcommit := rfl
    cge := Int.le_of_lt hcmi
    hrole := by
      rw [get!_set_self _ hn3]
      show leader = roleStr rd.pre r₁.p.role
      rw [hx.hpf, hpl]; rfl
    rlen := by rw [List.length_set, hrl]
    rother := fun k hk => get!_set_ne _ _ (fun h => hk (Fin.ext h))
    rstay := fun _ _ => get!_set_self _ hn3
    hdel := ha.hdel
    hfp := ha.hfp
    hdur := ha.hdur
    hundo := ha.hundo
    hmade := ha.hmade
    hmems := ha.hmems
    hreads := ha.hreads
    hcfg := ha.hcfg
    confLag := ha.confLag
    facts := ha.facts
    hmem := ⟨rfl, rfl⟩
    hviol := hb.1
    pre := hpm
    msub := fun f hf => hf
    mnew := fun f hf hn => absurd hf hn
    vsub := fun y hy => hy
    vnew := fun y hy hn => absurd hy hn
    vin := fun h => absurd rfl h
    lsub := fun l hl => hl
    lnew := fun l hl hn => absurd hl hn
    glead := fun _ => (hx.hrf.2.2.2.2.1 hpl).1
    hll := .inl rfl
    hchain := f1
    chainC := by rw [hlogn]; exact f2
    tlLen := f3
    tlC := f4
    tlDom := f5
    chainG := f6
    tlG := f7
    logG := by show r₁.p.log ∈ G.logs; rw [← hfl]; exact hx.hrf.1
    cmono := .inl rfl
    hconf := fun l hl => hb.2.2.2.2.1 n l hl
    lpart := fun _ => ⟨by
        show S1.leaders.contains { server := nameOf (nodeId n), term := uint.Z r₁.p.term } = true
        rw [hpt]; exact lp1,
      by show S1.ledLog.get (uint.Z r₁.p.term) = .ok (logOf r₁.full); rw [hfl]; exact hll,
      hMO.1, hMO.2,
      by show (S1.confirmed.set n.val (S1.confirmed[n.val]!))[n.val]!.term = uint.Z r₁.p.term ∧
          (r₁.full.length : Int) ≤ (S1.confirmed.set n.val (S1.confirmed[n.val]!))[n.val]!.index
         rw [hcf, lp5.1, hpt, hfl, hplog, ← hlenF]; exact ⟨rfl, lp5.2⟩⟩
    cpart := fun h => absurd (h.symm.trans hpl) (by decide)
    hpend := ha.hpend
    hxpend := ha.hxpend
    hqs := fun q hq => by
      have hq' := (hx.hro.2.2.2.2.2.2.1.mem_iff).mp hq
      rw [List.mem_filter] at hq'
      exact (hns q hq'.1 (of_decide_eq_true hq'.2)).elim
    drain := ha.drain
    hlead := ha.hlead
    hvself := hx.hvs1
    rnf := fun _ _ => by rw [hrole]; decide
    tlMono := fun T' => by
      rw [← htl, tlOld_with]
      by_cases h : T' = uint.Z r₁.p.term
      · rw [if_pos h, h]; omega
      · rw [if_neg h]; exact Int.le_refl _
    tlNew := fun T' h => by
      rw [← htl, tlOld_with] at h
      have hT' : T' = uint.Z r₁.p.term := by
        by_cases e : T' = uint.Z r₁.p.term
        · exact e
        · rw [if_neg e] at h; omega
      have lp1' : S1.leaders.contains { server := nameOf (nodeId n), term := uint.Z r₁.p.term } = true := by
        rw [hpt]; exact lp1
      refine ⟨hT', ⟨_, List.contains_iff_mem.mp lp1', rfl⟩, fun k hkn hkl hkt => ?_⟩
      exact absurd (lead_unique hx.hs1 hx.hgo1 hx.hl hx.hdk hkl (by rw [hkt, hpt]; exact lp1)) hkn
    tlSelf := fun _ => ⟨fun _ => by rw [← htl, tlOld_with, if_pos rfl]; exact Int.le_refl _, by
      rw [← htl, tlOld_with, if_pos rfl]; exact Int.le_refl _⟩
    lconf := hb.ledConfOk
    tlSort := by rw [← htl]; exact with_sorted _ _ hb.tlSorted }

end cmt

end AntSim
end EtcdGrove
end Perennial
