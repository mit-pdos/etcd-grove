/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: a candidate's win `Ready` (#33 S4, `antSim_ready`)

The `win` kind (`ReadyKind.win`: a candidate's tally a quorum, on a received grant or its own vote
in `Advance`; `becomeLeader`'s empty entry of its term appended): `InMemory`'s win
(`inMemory_win`: B 231-246's guards, `ld1`/`ll1`/`lc1`, the `LeaderCompleteness` check of B 270-272)
and `OnDisk`'s store (`onDisk_lstore`) evaluated, the side conditions `ReadyOk`. The term is new to
the binding's leaders (election safety against C3's leaders conjunct: the node is still a candidate
at it), so `ledLog` lacks it and `termLen` records nothing at it; the candidate's committed prefix is
in its campaign log (`commitIn_camp`), whose terms are below its term (`CampTermsOk`), so its commit
is at no entry of its term and the win commits nothing (`win_commit`: the other voters' `Match`
values are `0`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.ReadyProp

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open AntCheck go_etcd_io.raft.v3 GMap

section win
variable [GooseExts]

/-! ## Helpers -/

theorem win_granted {vs : GMap w64 Bool} {x : w64} (h : x ∈ granted vs) : vs !! x = some true := by
  unfold granted at h
  rw [GMap.elem_of_dom] at h
  obtain ⟨b, hb⟩ := h
  rw [GMap.mapLookup_filter_Some] at hb
  obtain ⟨hv, hb⟩ := hb
  cases b
  · exact absurd hb (by decide)
  · exact hv

theorem win_oneWaiting (S : State) (i : Nat) (l : List EntryM) (h0 : S.confAt[i]! = 0) :
    S.oneWaiting i (logOf l) = .ok true := by
  have hf : (logOf l).filter isConf = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha
    obtain ⟨e, -, rfl⟩ := List.mem_map.mp ha
    simp [entOf_isConf]
  unfold State.oneWaiting confsAfterCount
  rw [h0]
  simp [hf]
  rfl

theorem termAt_lt_of {l : List EntryM} {k T : Int} (h : ∀ e ∈ l, uint.Z e.Term' < T) (hT : 0 < T) :
    termAt (logOf l) k < T := by
  unfold termAt
  split
  · rename_i hk
    rw [logOf_length] at hk
    have hlt : (k - 1).toNat < l.length := by omega
    rw [logOf_getElem! (List.getElem?_eq_getElem hlt), entOf_term]
    exact h _ (List.getElem_mem hlt)
  · exact hT

/-- `LeaderCompleteness`'s check at a win (B 270-272) passes. -/
theorem anyM_wlc {tl : TermFn Int} {ch L : List Entry} {T : Int}
    (h : ∀ p ∈ tl, p.1 < T → ∃ l, subSeq ch 1 p.2 = .ok l ∧ isPrefix l L = .ok true) :
    anyM tl (fun p => AntCheck.andM (Except.ok (decide (p.fst < T)))
      (AntCheck.notM (subSeq ch 1 p.snd >>= fun a => isPrefix a L))) = .ok false := by
  induction tl with
  | nil => rfl
  | cons p ps ih =>
    unfold anyM
    have ih' := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    by_cases hp : p.1 < T
    · obtain ⟨l, h1, h2⟩ := h p (List.mem_cons_self ..) hp
      simp only [decide_eq_true hp, andM_true, h1, eok_bind, h2, notM_ok, Bool.not_true,
        Bool.false_eq_true, ite_false]
      exact ih'
    · simp only [decide_eq_false hp, andM_false, eok_bind, Bool.false_eq_true, ite_false]
      exact ih'

/-- **A candidate's win in memory**: the guards of B 233-246 (a candidate at its term, a term
`ledLog` lacks, `Granted` a quorum, at most one configuration waiting, none applied), its log the
term's leader log with the empty entry appended, its commit not a new one (`cmt`) and recorded, the
`LeaderCompleteness` check passing (`hlc`). -/
theorem inMemory_win {S : State} (n : Fin 3) (hc : S.cfg = cfg3) (b : Str)
    (hb : b = go!"recv" ∨ b = go!"tick" ∨ b = go!"propose" ∨ b = go!"boot")
    (t v c : w64) (e : EntryM) (lT : List Entry)
    (hrole : S.role[n.val]! = candidate) (ht : S.currentTerm[n.val]! = uint.Z t)
    (hlog : S.log[n.val]! = lT) (hnl : S.ledLog.has (uint.Z t) = false)
    (hq : isQuorum (S.granted n.val) (S.config[n.val]!) = true)
    (how : S.oneWaiting n.val lT = .ok true) (hca : S.confAt[n.val]! = 0)
    (hfirst : uint.Z e.Index' = (lT.length : Int) + 1) (hterm : uint.Z e.Term' = uint.Z t)
    (hcL : uint.Z c ≤ (lT ++ logOf [e]).length)
    (hcm : (decide (uint.Z c > tlOld S.termLen (uint.Z t)) &&
      (termAt (lT ++ logOf [e]) (uint.Z c) == uint.Z t)) = false)
    (hrec : uint.Z c = 0 ∨ recordedIn S.chain S.termLen (lT ++ logOf [e]) (uint.Z c) (uint.Z t) = .ok true)
    (hlc : ∀ p ∈ S.termLen, p.1 < uint.Z t → ∃ l, subSeq S.chain 1 p.2 = .ok l ∧ isPrefix l lT = .ok true) :
    S.inMemory n.val (evReady (nodeId n) b .leader t v c [e]) =
      .ok { ok := true, role := S.role.set n.val leader,
            leaders := lset.add S.leaders { server := nameOf (nodeId n), term := uint.Z t },
            ledLog := (S.ledLog.with (uint.Z t) lT).with (uint.Z t) (lT ++ logOf [e]),
            ledConf := S.ledConf.with (uint.Z t) (S.config[n.val]!), config := S.config, confAt := S.confAt,
            ledAt := S.ledAt.with (uint.Z t) (S.confAt[n.val]!), elAt := S.elAt.with (uint.Z t) (S.confAt[n.val]!),
            chain := S.chain, termLen := S.termLen, viol := S.viol } := by
  have hknown : (if S.termLen.has (uint.Z t) then S.termLen.get (uint.Z t) else .ok 0) =
      (.ok (tlOld S.termLen (uint.Z t)) : EvalM Int) := tl_old_ok _ _
  have hcL' : decide (uint.Z c ≤ ((lT ++ logOf [e]).length : Int)) = true := decide_eq_true hcL
  have hct : (S.currentTerm[n.val]! == uint.Z t) = true := by rw [ht]; exact beq_self_eq_true _
  have hfe : (firstOf [e] != (lT.length : Int) + 1) = false := by
    show (uint.Z e.Index' != _) = _; rw [hfirst]; exact bne_self_eq_false _
  have hts := anyM_terms [e] (uint.Z t) (fun x hx => by rw [List.mem_singleton.mp hx]; exact hterm)
  have hbad := anyM_notConf [e]
  have hca' : (S.confAt[n.val]! == 0) = true := by rw [hca]; rfl
  have hlc' := anyM_wlc hlc
  have hlogw : S.log[n.val]! = lT := hlog
  unfold State.inMemory
  by_cases h0 : uint.Z c = 0
  · have hc0 : decide (uint.Z c > 0) = false := decide_eq_false (by omega)
    rcases hb with rfl | rfl | rfl | rfl <;>
    simp (config := { decide := true }) only [evReady, InMem.ok, InMem.T, InMem.role1, InMem.leads,
        InMem.wins, InMem.es, InMem.ld1, InMem.ll1, InMem.lc1, InMem.snapsM, InMem.app, InMem.ll2,
        InMem.cmt, InMem.known, InMem.L, InMem.c, InMem.newC, fieldEq, need, eok_bind, epure, roleOf,
        str_beq, str_bne, leader, follower, candidate, decide_false, decide_true, Bool.not_true,
        Bool.not_false, Bool.false_eq_true, ite_true, ite_false, andM_false, andM_true, orM_true, orM_false,
        server_of hc n, Option.isSome_none, Option.isSome_some, Bool.false_and, Bool.and_false, Bool.true_and,
        Bool.and_true, hrole, hlogw, hnl, hq, how, hca', hknown, hcL', hct, stores_cons, hfe,
        TermFn.get_with_self, TermFn.has_with_self, hts, hbad, notM_ok, od_andM_ok, od_orM_ok, hcm, hc0, hlc']
  · have hcn : 0 ≤ uint.Z c := by word
    have hc0 : decide (uint.Z c > 0) = true := decide_eq_true (by omega)
    have hrc := hrec.resolve_left h0
    rcases hb with rfl | rfl | rfl | rfl <;>
    simp (config := { decide := true }) only [evReady, InMem.ok, InMem.T, InMem.role1, InMem.leads,
        InMem.wins, InMem.es, InMem.ld1, InMem.ll1, InMem.lc1, InMem.snapsM, InMem.app, InMem.ll2,
        InMem.cmt, InMem.known, InMem.L, InMem.c, InMem.newC, fieldEq, need, eok_bind, epure, roleOf,
        str_beq, str_bne, leader, follower, candidate, decide_false, decide_true, Bool.not_true,
        Bool.not_false, Bool.false_eq_true, ite_true, ite_false, andM_false, andM_true, orM_true, orM_false,
        server_of hc n, Option.isSome_none, Option.isSome_some, Bool.false_and, Bool.and_false, Bool.true_and,
        Bool.and_true, hrole, hlogw, hnl, hq, how, hca', hknown, hcL', hct, stores_cons, hfe,
        TermFn.get_with_self, TermFn.has_with_self, hts, hbad, notM_ok, od_andM_ok, od_orM_ok, hcm, hrc, hc0,
        hlc']

set_option maxHeartbeats 8000000 in
/-- **`antSim_ready` for a candidate's win** (`ReadyKind.win`). -/
theorem ready_win (S : State) (V : Fin 3 → NodeView) (net : List Msg) (evs : List Event)
    (G : RaftFacts) (n : Fin 3) (ps₁ : PState) (rd : ReadyD)
    (hp : Prefix cfg3 evs S) (hs : AntSim S V net) (hl : RaftLaws G) (hgo : GlobalOk S net G)
    (hr : Reach (nodeId n) net (V n) ps₁) (hro : ReadyOutP (nodeId n) (V n) ps₁ rd)
    (hrep : Reported (V n) rd) (hrf : ReadyFacts G (nodeId n) ps₁)
    (src : w64) (rej : Bool) (mt : GMap w64 w64) (hvc : (V n).ps.role = .candidate)
    (hsrc : (∃ m, RecvAt (nodeId n) net (V n) m ∧ m.ty = .voteResp ∧ m.term = (V n).ps.term ∧ m.src = src ∧
          m.reject = rej) ∨
        (src = nodeId n ∧ rej = false ∧ ∃ q ∈ (V n).qs, q.ty = .voteResp))
    (hq : JQuorum cfgM3 (granted (recordVote (V n).ps.votes src (!rej))))
    (hlm : LeaderMatchOk (nodeId n) (V n).ps mt)
    (hL : LeadC (nodeId n) (pwinState (nodeId n) { (V n).ps with votes := recordVote (V n).ps.votes src (!rej) } mt)
        ps₁)
    (hents : rd.ents = [pleaderEntry (V n).ps]) :
    ReadyGoal S V net evs G n ps₁ rd := by
  have hbE := reach_byE hr hro hrep
  obtain ⟨S1, hgc, hs1, hgo1⟩ := antSim_gc S V net G hs hl hgo
  have hs1' := hs1
  obtain ⟨hsh, hb, hnet, hno⟩ := hs1'
  have hc : S1.cfg = cfg3 := hsh.1
  have hrl : S1.role.length = 3 := hsh.2.2.2.2.2.2.1
  have hn3 : n.val < S1.role.length := by rw [hrl]; exact n.isLt
  obtain ⟨hd, -, hCP, -, hQ, -, -, hlo, hvsN⟩ := hno n
  obtain ⟨d1, d2, d3, d4, d5, -, d7, -, -, d10, d11, -, -⟩ := hd
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18,
    hb19⟩ := id hb
  have hq0 : S1.queue[n.val]! = [] := (hb2 n).1
  obtain ⟨-, -, -, -, -, -, -, -, hpre, hlen, hbase, hidx, -⟩ := id hro
  have hin : ∀ m ∈ net, InMsg m := fun m hm => ⟨(hnet.1 m hm).1, hnet.2.2.1 m hm⟩
  have hqsS : ∀ q ∈ (V n).qs, SelfMsg (nodeId n) (V n).ps.term q := fun q hq => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hQ q hq
    exact ⟨h1, h2, h3, h4, h5.imp (fun h => h.1) (fun h => h.1)⟩
  have hso := selfOut_reach hr d7 hlo hin hqsS
  -- `LeadC` from the won state
  obtain ⟨hpl, hpt, hpv, -, hplog, hmatch, hcmt⟩ := hL
  have hpt' : ps₁.term = (V n).ps.term := hpt
  have hpv' : ps₁.vote = (V n).ps.vote := hpv
  have hplog' : ps₁.log = (V n).ps.log ++ [pleaderEntry (V n).ps] := hplog
  have hmt : ∀ j : Fin 3, j ≠ n → matchOf ps₁ (nodeId j) = W64 0 := by
    intro j hj
    have hne : nodeId j ≠ nodeId n := fun h => hj (nodeId_inj h)
    unfold matchOf
    rw [hmatch _ hne]
    show ((mt !! nodeId j).getD (W64 0)) = W64 0
    cases h : mt !! nodeId j with
    | none => rfl
    | some x => exact hlm.2 _ x hne h
  -- the win commits nothing: the other voters' `Match` values are `0`
  have hpc : ps₁.commit = (V n).ps.commit := by
    rcases hcmt with h | ⟨hlt, hcm⟩
    · exact h
    · exfalso
      have hlt' : uint.Z (V n).ps.commit < uint.Z ps₁.commit := hlt
      obtain ⟨a, b, hab, ha, hb'⟩ := jq_two hcm.2.2
      obtain ⟨j, hjn, hj⟩ : ∃ j : Fin 3, j ≠ n ∧ nodeId j ∈ ackedBy ps₁ ps₁.commit := by
        by_cases han : a = n
        · exact ⟨b, fun h => hab (han.trans h.symm), hb'⟩
        · exact ⟨a, han, ha⟩
      obtain ⟨y, hy, hle⟩ := mem_ackedBy.mp hj
      have h0 := hmt j hjn
      unfold matchOf at h0; rw [hy] at h0
      simp only [Option.getD_some] at h0
      rw [h0] at hle
      have : uint.Z (W64 0) = 0 := rfl
      have := uint_Z_nonneg (V n).ps.commit
      omega
  -- the term
  have hT : S1.currentTerm[n.val]! = uint.Z ps₁.term := by rw [d1, hpt']
  have hboot : S1.bootTerm = 0 := by unfold State.bootTerm; rw [hc]; rfl
  have hvn : (V n).ps.vote = nodeId n := hvsN (by rw [hvc]; decide)
  have hvS : S1.vote n.val = nameOf (nodeId n) := by rw [d2, hvn]
  have hTpos : 0 < uint.Z ps₁.term := by
    have hne : nameOf (nodeId n) ≠ [] := by have := ready_name_ne n; simpa using this
    have hv := hvS
    unfold State.vote State.voteOf at hv
    rw [hboot] at hv
    split at hv
    · rename_i h
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      rw [← hT]; exact h.2
    · exact absurd hv.symm hne
  have hGl := hrf.2.2.2.2.1 hpl
  have hnoL : ∀ l ∈ S1.leaders, l.term ≠ uint.Z ps₁.term := by
    intro l hlm0 hlt
    obtain ⟨j, t', hj, hs', ht'⟩ := hgo1.1 l hlm0
    have htt : t' = ps₁.term := uZ_inj (by rw [← ht', hlt])
    have hjn : j = nodeId n := hl.1 _ hj _ hGl.1 (by simp only; exact htt)
    rcases hb10 n l hlm0 (by rw [hs', hjn]) with h | ⟨-, h⟩
    · rw [hlt, hT] at h; exact Int.lt_irrefl _ h
    · rw [d5, hvc] at h; exact absurd h (by decide)
  have hnl : S1.ledLog.has (uint.Z ps₁.term) = false := by
    cases h : S1.ledLog.has (uint.Z ps₁.term) with
    | false => rfl
    | true =>
      exfalso
      unfold TermFn.has at h
      obtain ⟨p, hp, hpe⟩ := List.any_eq_true.mp h
      obtain ⟨l, hl', hlt⟩ := hb9 p hp
      exact hnoL l hl' (by rw [hlt]; simpa using hpe)
  have htl0 : tlOld S1.termLen (uint.Z ps₁.term) = 0 := by
    rcases tlOld_cases S1.termLen (uint.Z ps₁.term) with h | ⟨q, hq, h1, h2⟩
    · exact h
    · have h0 := (hgo1.2.2.2.2.2.1 q hq).1
      refine Classical.byContradiction fun hne => ?_
      have hpos : 0 < tlOld S1.termLen (uint.Z ps₁.term) := by omega
      rcases hb17.1 _ hpos with ⟨l, hl', hlt⟩ | hall
      · exact hnoL l hl' hlt
      · have := hall n; rw [hT] at this; exact Int.lt_irrefl _ this
  -- the campaign log
  obtain ⟨l0, hcamp, hl0p⟩ := hGl.2
  have hl0T : ∀ e ∈ l0, uint.Z e.Term' < uint.Z ps₁.term := hl.2.2.2.2.2.2 _ hcamp
  have hl0O : l0 <+: (V n).ps.log := by
    rw [hplog'] at hl0p
    rcases List.prefix_concat_iff.mp hl0p with h | h
    · exfalso
      have := hl0T (pleaderEntry (V n).ps) (by rw [h]; simp)
      have e : (pleaderEntry (V n).ps).Term' = ps₁.term := by rw [hpt']; rfl
      rw [e] at this; exact Int.lt_irrefl _ this
    · exact h
  -- the commit
  have hcmi : S1.commitIndex[n.val]! = uint.Z ps₁.commit := by rw [d4, hpc]
  have hcmL : uint.Z ps₁.commit ≤ (V n).ps.log.length := by
    obtain ⟨h1, h2⟩ := hb5 n
    have hlen := congrArg List.length h2
    rw [d3] at hlen
    simp only [List.length_take, logOf_length] at hlen
    rw [← hcmi]; omega
  have hcnZ : ((uint.nat ps₁.commit : Nat) : Int) = uint.Z ps₁.commit := by word
  have hcT : 0 < uint.Z ps₁.commit →
      termAt (logOf (V n).ps.log) (uint.Z ps₁.commit) < uint.Z ps₁.term := by
    intro hc0
    rcases hb6 n with h | ⟨p, hp, hp1, hp2⟩
    · omega
    · rw [hT] at hp1
      rw [hcmi] at hp2
      rcases Int.lt_or_eq_of_le hp1 with hlt | heq
      · obtain ⟨hp0, x, hx, hxc⟩ := hgo1.2.2.2.2.2.1 p hp
        have hpre := (hl.2.2.2.2.2.1 _ hxc).2 _ hcamp (by simp only; omega)
        have hk : uint.nat ps₁.commit ≤ p.2.toNat := by omega
        have hpk : G.committed.take (uint.nat ps₁.commit) <+: l0 := by
          have := (List.take_prefix (uint.nat ps₁.commit) (G.committed.take p.2.toNat)).trans hpre
          rwa [List.take_take, Nat.min_eq_left hk] at this
        have hOk : (V n).ps.log.take (uint.nat ps₁.commit) = G.committed.take (uint.nat ps₁.commit) := by
          rw [← hrf.2.2.1, hplog', List.take_append_of_le_length (by omega)]
        have hsub : ∀ e ∈ (V n).ps.log.take (uint.nat ps₁.commit), uint.Z e.Term' < uint.Z ps₁.term :=
          fun e he => hl0T e (hpk.subset (hOk ▸ he))
        have := termAt_lt_of (k := uint.Z ps₁.commit) hsub hTpos
        rw [← List.take_append_drop (uint.nat ps₁.commit) (logOf (V n).ps.log),
          rr_termAt_append _ _ _ (by rw [List.length_take, logOf_length]; omega), logOf_take]
        exact this
      · have := tlOld_mem hb19 hp
        rw [heq, htl0] at this
        omega
  have hLeq : logOf (V n).ps.log ++ logOf [pleaderEntry (V n).ps] = logOf ps₁.log := by
    rw [hplog']; unfold logOf; rw [List.map_append]
  have htermc : termAt (logOf ps₁.log) (uint.Z ps₁.commit) =
      termAt (logOf (V n).ps.log) (uint.Z ps₁.commit) := by
    rw [← hLeq]; exact rr_termAt_append _ _ _ (by rw [logOf_length]; exact hcmL)
  have hcm : (decide (uint.Z ps₁.commit > tlOld S1.termLen (uint.Z ps₁.term)) &&
      (termAt (logOf (V n).ps.log ++ logOf [pleaderEntry (V n).ps]) (uint.Z ps₁.commit) == uint.Z ps₁.term))
      = false := by
    rw [htl0, hLeq, htermc]
    by_cases h0 : uint.Z ps₁.commit = 0
    · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; left; omega
    · have := hcT (by have := uint_Z_nonneg ps₁.commit; omega)
      simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]; right; omega
  have hrec : uint.Z ps₁.commit = 0 ∨ recordedIn S1.chain S1.termLen
      (logOf (V n).ps.log ++ logOf [pleaderEntry (V n).ps]) (uint.Z ps₁.commit) (uint.Z ps₁.term) = .ok true := by
    rcases commit_recorded (c := uint.nat ps₁.commit) hb d3 (by rw [hcnZ, hcmi]; exact Int.le_refl _)
      with h0 | ⟨h1, h2, ⟨x, hx, hx1, hx2⟩, h4⟩
    · left; omega
    · right
      rw [hLeq, ← hcnZ]
      refine recordedIn_true (by rw [logOf_length, hplog', List.length_append]; omega) h2
        ⟨x, hx, by rw [hT] at hx1; exact hx1, hx2⟩ ?_
      rw [h4, ← hLeq, List.take_append_of_le_length (by rw [logOf_length]; exact h1)]
  have hlc : ∀ p ∈ S1.termLen, p.1 < uint.Z ps₁.term →
      ∃ l, subSeq S1.chain 1 p.2 = .ok l ∧ isPrefix l (logOf (V n).ps.log) = .ok true := by
    intro p hp hlt
    obtain ⟨hp0, x, hx, hxc⟩ := hgo1.2.2.2.2.2.1 p hp
    have hpre := (hl.2.2.2.2.2.1 _ hxc).2 _ hcamp (by simp only; omega)
    obtain ⟨c', -, hch⟩ := hgo1.2.2.2.2.1
    have hp2 : p.2 ≤ S1.chain.length := hb4 p hp
    refine ⟨S1.chain.take p.2.toNat, ?_, ?_⟩
    · have := subSeq_one S1.chain p.2.toNat (by omega)
      rwa [Int.toNat_of_nonneg hp0] at this
    · apply isPrefix_of_prefix
      rw [hch, logOf_take]
      apply logOf_prefix
      have e : (G.committed.take c').take p.2.toNat =
          (G.committed.take p.2.toNat).take (min p.2.toNat c') := by
        rw [List.take_take, List.take_take]; congr 1; omega
      rw [e]; exact ((List.take_prefix _ _).trans hpre).trans hl0O
  -- `Granted(n)` a quorum
  have hgr : isQuorum (S1.granted n.val) (S1.config[n.val]!) = true := by
    rw [d10]
    refine jq_isQuorum hq fun j hj => ?_
    have hj' := win_granted hj
    by_cases hjn : j = n
    · rw [hjn]
      refine granted_self hc ?_
      have := hb13 n (by rw [hvS]; exact fun h => by have := ready_name_ne n; simp [h] at this)
      rw [hvS] at this; exact this
    · unfold recordVote at hj'
      split at hj'
      · exact (hCP hvc).1 j hj'
      · by_cases hjs : src = nodeId j
        · rw [hjs, lookup_insert] at hj'
          have hr : rej = false := by cases rej; rfl; simp at hj'
          rcases hsrc with ⟨m, hm, hty, hmt', hms, hmr⟩ | ⟨hs0, -, -⟩
          · obtain ⟨-, -, j', hj'd, hjj⟩ := hnet.1 m hm.2.2.1
            have hj'n : j' = n := nodeId_inj (hj'd.symm.trans hm.2.2.2.1)
            rw [hj'n] at hjj
            have hle : S1.currentTerm[n.val]! ≤ uint.Z m.term := by rw [hT, hpt', hmt']; exact Int.le_refl _
            have hg := (hjj hle).2.2.1 ⟨hty, by rw [hmr, hr]⟩
            apply granted_grant hc hjn
            have e1 : m.src = nodeId j := hms.trans hjs
            rw [e1, hm.2.2.2.1, hmt', ← hpt', ← hT] at hg
            exact hg
          · exact absurd (nodeId_inj (hs0.symm.trans hjs)) (Ne.symm hjn)
        · rw [lookup_insert_ne _ _ hjs] at hj'; exact (hCP hvc).1 j hj'
  -- `InMemory`
  have hfirst0 : uint.Z (pleaderEntry (V n).ps).Index' = ((V n).ps.log.length : Int) + 1 := by
    have h := hidx (V n).ps.log.length (pleaderEntry (V n).ps)
      (by rw [hplog', List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl)
    exact h
  have hm' := inMemory_win n hc (V n).byE hbE ps₁.term ps₁.vote ps₁.commit (pleaderEntry (V n).ps)
    (logOf (V n).ps.log) (by rw [d5, hvc]; rfl) hT d3 hnl hgr (win_oneWaiting _ _ _ d11) d11
    (by rw [logOf_length]; exact hfirst0) (by rw [hpt']; rfl)
    (by rw [hLeq, logOf_length]; exact nat_commit_le hrf) hcm hrec hlc
  rw [with_with, hLeq] at hm'
  -- `OnDisk`
  have hL1eq : (S1.log[n.val]!).take (uint.Z (pleaderEntry (V n).ps).Index' - 1).toNat ++
      logOf [pleaderEntry (V n).ps] = logOf ps₁.log := by
    rw [d3, hfirst0, List.take_of_length_le (by rw [logOf_length]; omega), hLeq]
  have hcG := hrf.2.2.1
  have hcch : uint.Z ps₁.commit ≤ S1.chain.length := by rw [← hcmi]; exact (hb5 n).1
  obtain ⟨eqb, heqb⟩ := entriesEqual_logOf ps₁.log (V n).ps.log
  have hldm : { server := nameOf (nodeId n), term := uint.Z ps₁.term } ∈
      lset.add S1.leaders ({ server := nameOf (nodeId n), term := uint.Z ps₁.term } : LeaderRec) :=
    mem_lset_add.mpr (.inr rfl)
  have hsend : sendableIn (lset.add S1.leaders { server := nameOf (nodeId n), term := uint.Z ps₁.term })
      (S1.ledLog.with (uint.Z ps₁.term) (logOf ps₁.log)) S1.chain S1.termLen
      (AppendFact.mk (nameOf (nodeId n)) (nameOf (nodeId n)) (uint.Z ps₁.term)
        (uint.Z (pleaderEntry (V n).ps).Index' - 1)
        (termAt (logOf ps₁.log) (uint.Z (pleaderEntry (V n).ps).Index' - 1))
        (logOf [pleaderEntry (V n).ps]) 0) = .ok true := by
    have h := sendable_leader (S := { S1 with
        leaders := lset.add S1.leaders { server := nameOf (nodeId n), term := uint.Z ps₁.term },
        ledLog := S1.ledLog.with (uint.Z ps₁.term) (logOf ps₁.log) })
      (src := nameOf (nodeId n)) (dst := nameOf (nodeId n)) (lg := ps₁.log) (T := uint.Z ps₁.term)
      (p := (V n).ps.log.length) (pt := termAt (logOf ps₁.log) ((V n).ps.log.length : Int))
      (es := [pleaderEntry (V n).ps]) (c := 0)
      (List.contains_iff_mem.mpr hldm) (TermFn.get_with_self _ _ _) rfl
      (by rw [hplog']; simp) (by rw [hplog']; simp) (.inl rfl)
    have e1 : (((V n).ps.log.length : Nat) : Int) = uint.Z (pleaderEntry (V n).ps).Index' - 1 := by omega
    rw [e1] at h; exact h
  obtain ⟨p, hpm, hod⟩ := onDisk_lstore n hc (V n).byE ps₁.term ps₁.vote ps₁.commit (pleaderEntry (V n).ps) []
    (if (V n).byE = go!"recv" then S1.pending[n.val]! else []) (S1.role.set n.val leader)
    (lset.add S1.leaders { server := nameOf (nodeId n), term := uint.Z ps₁.term })
    (S1.ledLog.with (uint.Z ps₁.term) (logOf ps₁.log)) S1.chain S1.termLen S1.viol (logOf ps₁.log) eqb
    hT.symm (by rw [d2, hpv']) (get!_set_self _ hn3) (by rw [d3, logOf_length]; exact hfirst0)
    (TermFn.get_with_self _ _ _) hsend hcmi.symm (by rw [hL1eq, d3]; exact heqb)
    (by rw [hL1eq]; exact lm_ok hl hrf.1 hgo1.2.2.1 hsh.2.2.2.2.1) hcch
    (by rw [hL1eq]; exact ch_ok hgo1.2.2.2.2.1 hcG hcch)
  have hlast : uint.Z (pleaderEntry (V n).ps).Index' - 1 + (((([] : List EntryM).length + 1 : Nat)) : Int) =
      (ps₁.log.length : Int) := by
    rw [hplog', List.length_append]; simp only [List.length_nil, List.length_singleton]; push_cast; omega
  rw [hL1eq, hlast] at hod
  unfold ReadyGoal
  rw [hpl, hents]
  have hcf : (S1.confirmed.set n.val (Confirmed.mk (uint.Z ps₁.term) (ps₁.log.length : Int)))[n.val]! =
      Confirmed.mk (uint.Z ps₁.term) (ps₁.log.length : Int) :=
    get!_set_self _ (by rw [hsh.2.2.2.2.2.2.2.2.2.2.1]; exact n.isLt)
  have hmsub : ∀ f ∈ S1.msgs, f ∈ lset.add S1.msgs (ackFact (nameOf (nodeId n)) (nameOf (nodeId n))
      (uint.Z ps₁.term) (ps₁.log.length : Int)) := fun f hf => mem_lset_add.mpr (.inl hf)
  have hackN : ackFact (nameOf (nodeId n)) (nameOf (nodeId n)) (uint.Z ps₁.term) (ps₁.log.length : Int) ∈
      lset.add S1.msgs (ackFact (nameOf (nodeId n)) (nameOf (nodeId n)) (uint.Z ps₁.term)
        (ps₁.log.length : Int)) := mem_lset_add.mpr (.inr rfl)
  have hlenlt : (ps₁.log.length : Int) < 2 ^ 64 := by
    refine logIdx_len_lt hidx ?_
    rw [hplog']; simp
  refine ready_finish hp hgc hs1 hgo1 hl
    (ready_of hq0 hm' rfl (queued_ready _ _ _ _ _ _ _ _ _) hod) ?_
  exact {
    hterm := rfl
    tge := Int.le_of_eq hT
    hvote := .inl ⟨hT.symm, by show S1.vote n.val = nameOf ps₁.vote; rw [d2, hpv']⟩
    hlog := rfl
    hcommit := rfl
    cge := Int.le_of_eq hcmi
    hrole := by rw [get!_set_self _ hn3]; show leader = roleOf ps₁.role; rw [hpl]; rfl
    rlen := by rw [List.length_set, hrl]
    rother := fun k hk => get!_set_ne _ _ (fun h => hk (Fin.ext h))
    rstay := fun _ _ => get!_set_self _ hn3
    hdel := rfl
    wf := ⟨rfl, hbase, hidx, hpre, hlen⟩
    hmem := ⟨rfl, rfl⟩
    hviol := hb1
    made := hpm
    msub := hmsub
    mnew := fun f hf hn => by
      rcases mem_lset_add.mp hf with h | h
      · exact absurd h hn
      · subst h
        exact .inr ⟨rfl, rfl, ⟨n, rfl⟩, rfl, .inl ⟨rfl, Int.le_refl _⟩⟩
    vsub := fun y hy => hy
    vnew := fun y hy hn => absurd hy hn
    vin := fun h => absurd rfl h
    lsub := fun l hl' => mem_lset_add.mpr (.inl hl')
    lnew := fun l hl' hn => by
      rcases mem_lset_add.mp hl' with h | h
      · exact absurd h hn
      · exact ⟨h, get!_set_self _ hn3, hGl.1⟩
    glead := fun _ => hGl.1
    hll := .inr ⟨rfl, get!_set_self _ hn3, hT.symm,
      fun l hl' => absurd (TermFn.has_of_get hl') (by rw [hnl]; decide), hldm,
      ⟨ps₁.term, l0, rfl, hcamp, hl0p⟩⟩
    hchain := List.prefix_refl _
    chainC := ⟨hcch, ch_ok hgo1.2.2.2.2.1 hcG hcch⟩
    tlLen := hb4
    tlC := by
      rcases hb6 n with h | ⟨q, hq, h1, h2⟩
      · exact .inl (by rw [← hcmi]; exact h)
      · exact .inr ⟨q, hq, by rw [← hT]; exact h1, by rw [← hcmi]; exact h2⟩
    tlDom := fun q hq => ⟨q, hq, rfl, Int.le_refl _⟩
    chainG := hgo1.2.2.2.2.1
    tlG := hgo1.2.2.2.2.2.1
    logG := hrf.1
    cmono := .inr ⟨rfl, TermFn.has_with_self _ _ _, fun ht => by
      show (S1.confirmed[n.val]!).index ≤ (ps₁.log.length : Int)
      rcases (hb16 n).1 with h | h | h
      · rw [h]; omega
      · rw [ht, hnl] at h; cases h
      · have := h n; rw [ht, hT] at this; exact absurd this (Int.lt_irrefl _)⟩
    hconf := fun l hl' => by
      change (S1.ledLog.with (uint.Z ps₁.term) (logOf ps₁.log)).get (uint.Z ps₁.term) = .ok l at hl'
      rw [TermFn.get_with_self] at hl'; cases hl'
      refine ⟨by rw [logOf_length]; exact Int.le_refl _, by rw [logOf_length]; exact Int.le_refl _, rfl⟩
    lpart := fun _ => ⟨List.contains_iff_mem.mpr hldm,
      by
        show (S1.ledLog.with (uint.Z ps₁.term) (logOf ps₁.log)).get (uint.Z ps₁.term) = .ok (logOf ps₁.log)
        exact TermFn.get_with_self _ _ _,
      fun j k hk hkt => by
        have hkt' : plogTermAt base0 ps₁.log k = some ps₁.term := hkt
        obtain ⟨hkl, -⟩ := termAt_of_plog hkt'
        by_cases hjn : j = n
        · subst hjn
          exact ⟨_, hackN, rfl, rfl, rfl, rfl, hkl⟩
        · exfalso
          change uint.Z k ≤ uint.Z (matchOf ps₁ (nodeId j)) at hk
          rw [hmt j hjn] at hk
          have hk0 : uint.Z k = 0 := by
            have : uint.Z (W64 0) = 0 := rfl
            have := uint_Z_nonneg k; omega
          have hb0 : uint.Z (base0 : go_etcd_io.raft.v3.entryID).index' = 0 := rfl
          have hbt : uint.Z (base0 : go_etcd_io.raft.v3.entryID).term' = 0 := rfl
          unfold plogTermAt at hkt'
          rw [hb0, if_neg (by omega), if_pos hk0] at hkt'
          have := congrArg (fun o => (o.map uint.Z)) hkt'
          simp only [Option.map_some] at this
          have := Option.some.inj this
          omega,
      fun j hjn => .inl (hmt j hjn),
      by
        show (S1.confirmed.set n.val (Confirmed.mk (uint.Z ps₁.term) (ps₁.log.length : Int)))[n.val]!.term =
            uint.Z ps₁.term ∧ (ps₁.log.length : Int) ≤
            (S1.confirmed.set n.val (Confirmed.mk (uint.Z ps₁.term) (ps₁.log.length : Int)))[n.val]!.index
        rw [hcf]; exact ⟨rfl, Int.le_refl _⟩⟩
    cpart := fun h => absurd (h.symm.trans hpl) (by decide)
    hpend := pendOk_of_reach hnet (hno n) hr hro
    hqs := fun q hq => by
      obtain ⟨⟨h1, h2, h3, h4, -⟩, hk⟩ := qs_self hro hso q hq
      rcases hk with ⟨-, rfl⟩ | ⟨hc', -⟩
      · refine ⟨h1, h2, h3, h4, .inl ⟨rfl, ?_⟩⟩
        refine ⟨_, hackN, rfl, rfl, rfl, rfl, ?_⟩
        show uint.Z (plastIndex ps₁) ≤ (ps₁.log.length : Int)
        unfold plastIndex plogLastIndexZ
        rw [hbase]
        have hb0 : uint.Z (base0 : go_etcd_io.raft.v3.entryID).index' = 0 := rfl
        rw [hb0]
        have : uint.Z (W64 (0 + (ps₁.log.length : Int))) = (ps₁.log.length : Int) := by
          rw [Int.zero_add]; word
        omega
      · exact absurd (hc'.symm.trans hpl) (by decide)
    drain := ⟨rfl, rfl⟩
    hlead := fun h => absurd hpl h
    hvself := fun _ => by show ps₁.vote = nodeId n; rw [hpv']; exact hvn
    rnf := fun _ _ => by rw [d5, hvc]; decide
    tlMono := fun _ => Int.le_refl _
    tlNew := fun _ h => absurd h (Int.lt_irrefl _)
    tlSelf := fun _ => ⟨fun h => by
        rw [htl0]
        rw [htermc] at h
        by_cases h0 : uint.Z ps₁.commit = 0
        · omega
        · have := hcT (by have := uint_Z_nonneg ps₁.commit; omega)
          omega,
      by rw [htl0]; exact uint_Z_nonneg _⟩
    lconf := fun T' h => by
      show (S1.ledConf.with (uint.Z ps₁.term) (S1.config[n.val]!)).get T' = _
      by_cases e : T' = uint.Z ps₁.term
      · rw [e, TermFn.get_with_self, d10]
      · rw [rr_get_with_ne _ _ e]
        rcases has_with_cases h with h' | h'
        · exact absurd h' e
        · exact hb.ledConfOk T' h'
    tlSort := hb19 }

end win

end AntSim
end EtcdGrove
end Perennial
