/-
Lean-first (no Rocq counterpart).

# Parity B2: a `-parallel` leader's `mem`, per kind (#33 parity B2, Sim round 17)

`memNode_lead`'s and `mem_relD`'s kind-dependent premises at a leader's `mem` for each of
`ReadyKind`'s leader kinds (a win, a proposal, a commit): `InMemory`'s result and its `MemOk`
(`memOk_win`, `memOk_prop`, `memOk_cmt`, from `win_mem`, `prop_mem`, `cmt_mem`), and a commit's leader
part (`memLead_lpCmt`: the `Match` facts along `ReachP` at the state without the other nodes' unmade
acknowledgements, `stripU`) and recorded commit (`memCommitOk_of`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.MemKinds
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.ReadyCmt
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.QuietP

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open GMap go_etcd_io.raft.v3 AntCheck

section memLead
variable [GooseExts]


/-- `commit_fields` over C3's bound on `termLen` alone (what it reads of `BindingOk`). -/
theorem commit_fieldsM {R : RunCfg} {S : State} {net : List Msg} {G : RaftFacts} {n : Fin R.N}
    {l : List EntryM} {cc T : w64} (hb4 : ∀ p ∈ S.termLen, p.2 ≤ S.chain.length) (hgo : GlobalOk R S net G)
    (hcL : uint.Z cc ≤ l.length) (hcG : l.take (uint.nat cc) = G.committed.take (uint.nat cc))
    (hcGl : uint.nat cc ≤ G.committed.length) (hcm : (T, uint.nat cc) ∈ G.commits)
    (hold : S.commitIndex[n.val]! < uint.Z cc) :
    S.chain <+: (if S.commitIndex[n.val]! < uint.Z cc ∧ (S.chain.length : Int) < uint.Z cc then
        (logOf l).take (uint.Z cc).toNat else S.chain) ∧
    (uint.Z cc ≤ (if S.commitIndex[n.val]! < uint.Z cc ∧ (S.chain.length : Int) < uint.Z cc then
        (logOf l).take (uint.Z cc).toNat else S.chain).length ∧
      (if S.commitIndex[n.val]! < uint.Z cc ∧ (S.chain.length : Int) < uint.Z cc then
        (logOf l).take (uint.Z cc).toNat else S.chain).take (uint.Z cc).toNat =
        (logOf l).take (uint.Z cc).toNat) ∧
    (∀ q ∈ S.termLen.with (uint.Z T) (imax (tlOld S.termLen (uint.Z T)) (uint.Z cc)),
      q.2 ≤ (if S.commitIndex[n.val]! < uint.Z cc ∧ (S.chain.length : Int) < uint.Z cc then
        (logOf l).take (uint.Z cc).toNat else S.chain).length) ∧
    (uint.Z cc = 0 ∨ ∃ q ∈ S.termLen.with (uint.Z T) (imax (tlOld S.termLen (uint.Z T)) (uint.Z cc)),
      q.1 ≤ uint.Z T ∧ uint.Z cc ≤ q.2) ∧
    (∀ q ∈ S.termLen, ∃ q' ∈ S.termLen.with (uint.Z T) (imax (tlOld S.termLen (uint.Z T)) (uint.Z cc)),
      q'.1 = q.1 ∧ q.2 ≤ q'.2) ∧
    (∃ c' ≤ G.committed.length, (if S.commitIndex[n.val]! < uint.Z cc ∧ (S.chain.length : Int) < uint.Z cc
        then (logOf l).take (uint.Z cc).toNat else S.chain) = logOf (G.committed.take c')) ∧
    (∀ q ∈ S.termLen.with (uint.Z T) (imax (tlOld S.termLen (uint.Z T)) (uint.Z cc)),
      0 ≤ q.2 ∧ ∃ x, uint.Z x = q.1 ∧ (x, q.2.toNat) ∈ G.commits) := by
  obtain ⟨c', hc', hch⟩ := hgo.2.2.2.2.1
  have hnc : (uint.Z cc).toNat = uint.nat cc := uZ_toNat_nat cc
  have hnew : (logOf l).take (uint.Z cc).toNat = logOf (G.committed.take (uint.nat cc)) := by
    rw [hnc, logOf_take, hcG]
  have hchl : (S.chain.length : Int) = c' := by
    rw [hch, logOf_take_len]; omega
  have hcz : (uint.nat cc : Int) = uint.Z cc := by word
  -- the new chain
  have hP : S.chain <+: (if S.commitIndex[n.val]! < uint.Z cc ∧ (S.chain.length : Int) < uint.Z cc then
        (logOf l).take (uint.Z cc).toNat else S.chain) ∧
      (uint.Z cc ≤ (if S.commitIndex[n.val]! < uint.Z cc ∧ (S.chain.length : Int) < uint.Z cc then
        (logOf l).take (uint.Z cc).toNat else S.chain).length ∧
      (if S.commitIndex[n.val]! < uint.Z cc ∧ (S.chain.length : Int) < uint.Z cc then
        (logOf l).take (uint.Z cc).toNat else S.chain).take (uint.Z cc).toNat =
        (logOf l).take (uint.Z cc).toNat) ∧
      (∃ c' ≤ G.committed.length, (if S.commitIndex[n.val]! < uint.Z cc ∧ (S.chain.length : Int) < uint.Z cc
        then (logOf l).take (uint.Z cc).toNat else S.chain) = logOf (G.committed.take c')) := by
    by_cases h : S.commitIndex[n.val]! < uint.Z cc ∧ (S.chain.length : Int) < uint.Z cc
    · rw [if_pos h, hnew, hch]
      refine ⟨?_, ⟨?_, ?_⟩, uint.nat cc, hcGl, rfl⟩
      · apply List.IsPrefix.map
        have : c' ≤ uint.nat cc := by omega
        have e : G.committed.take c' = (G.committed.take (uint.nat cc)).take c' := by
          rw [List.take_take]; congr 1; omega
        rw [e]; exact List.take_prefix _ _
      · rw [logOf_take_len]; omega
      · rw [hnc, List.take_of_length_le (by rw [logOf_take_len]; omega)]
    · rw [if_neg h]
      have hge : uint.Z cc ≤ S.chain.length := by omega
      refine ⟨List.prefix_refl _, ⟨hge, ?_⟩, c', hc', hch⟩
      rw [hnew, hch, hnc, logOf_take, List.take_take]; congr 2; omega
  obtain ⟨hP1, hP2, hP3⟩ := hP
  have hlen : (S.chain.length : Int) ≤ (if S.commitIndex[n.val]! < uint.Z cc ∧ (S.chain.length : Int) < uint.Z cc
        then (logOf l).take (uint.Z cc).toNat else S.chain).length := by
    have := hP1.length_le; omega
  have hold0 : 0 ≤ tlOld S.termLen (uint.Z T) ∧ tlOld S.termLen (uint.Z T) ≤ S.chain.length ∧
      (tlOld S.termLen (uint.Z T) = 0 ∨ (T, (tlOld S.termLen (uint.Z T)).toNat) ∈ G.commits) := by
    rcases tlOld_cases S.termLen (uint.Z T) with h | ⟨q, hq, h1, h2⟩
    · rw [h]; exact ⟨Int.le_refl _, by omega, .inl rfl⟩
    · obtain ⟨g0, x, hx, hxg⟩ := hgo.2.2.2.2.2.1 q hq
      have hxT : x = T := uZ_inj (by rw [hx, h1])
      rw [← h2]
      exact ⟨g0, hb4 q hq, .inr (by rw [← hxT]; exact hxg)⟩
  have hcz0 : 0 ≤ uint.Z cc := by word
  refine ⟨hP1, hP2, ?_, .inr ⟨_, rd_with_self _ _ _, Int.le_refl _, by unfold imax; split <;> omega⟩,
    rd_with_dom _ _ _ (by unfold imax; split <;> omega), hP3, ?_⟩
  · intro q hq
    rcases rd_with_mem hq with hq | rfl
    · have := hb4 q hq; omega
    · show imax _ _ ≤ _
      have := hP2.1
      unfold imax; split <;> omega
  · intro q hq
    rcases rd_with_mem hq with hq | rfl
    · exact hgo.2.2.2.2.2.1 q hq
    · refine ⟨by unfold imax; split <;> omega, T, rfl, ?_⟩
      show (T, (imax _ _).toNat) ∈ G.commits
      unfold imax
      split
      · rcases hold0.2.2 with h0 | h0
        · rename_i hge
          have : uint.Z cc = 0 := by omega
          rw [h0]; rw [this] at hnc; rw [← hnc] at hcm; exact hcm
        · exact h0
      · rw [hnc]; exact hcm

variable {R : RunCfg} {dec : CCDec} {S : State} {V : Fin R.N → NodeView} {net : List Msg}
  {xnet : List XMsg} {G : RaftFacts} {n : Fin R.N} {r : MemResult} {i : Int}
  {r₁ : RState} {rd : ReadyD}

/-- `MemCommitOk` from its parts. -/
theorem memCommitOk_of {S' : State} {v : NodeView}
    (h1 : uint.Z v.ps.commit ≤ S'.chain.length)
    (h2 : S'.chain.take (uint.Z v.ps.commit).toNat = (logOf v.r.full).take (uint.Z v.ps.commit).toNat)
    (h3 : uint.Z v.ps.commit = 0 ∨ ∃ q ∈ S'.termLen, q.1 ≤ uint.Z v.ps.term ∧ uint.Z v.ps.commit ≤ q.2) :
    MemCommitOk S' v := by
  intro _
  refine ⟨h1, by rw [← uZ_toNat_nat]; exact h2, ?_⟩
  rcases h3 with h | h
  · exact .inl (by word)
  · exact .inr h

/-- **A leader commit's leader part** at the `mem`: the `Match` facts along `ReachP` (`quiet_reachP`,
the role, term and log kept) at the state without the other nodes' unmade acknowledgements
(`stripU`), so acknowledgements outside them (`AckInX`); the leader log the `mem`'s (unchanged); the
confirmation the old one (the disk unchanged). -/
theorem memLead_lpCmt (hs : AntSimD R dec S V net xnet) (hx : LdCtx R.syncOff dec V net xnet G n r₁ rd S)
    (ha : R.md.async = false) (hbat : R.drv.batch = false)
    (hm : (V n).mems = []) (hpar0 : (V n).parts = [])
    (hvl : (V n).ps.role = .leader) (hpl : r₁.p.role = .leader) (hpt : r₁.p.term = (V n).ps.term)
    (hplog : r₁.p.log = (V n).ps.log)
    (hlead : r.leaders = S.leaders)
    (hrll : r.ledLog.get (uint.Z r₁.p.term) = .ok (logOf r₁.p.log)) {it : QItem} {P : List Msg} :
    LeaderPartD (memQ S r n.val it i) n (memView (V n) r₁ rd P) := by
  intro _
  have hv := hs.2.2.2.2 n
  obtain ⟨l1, -, -, -, l5⟩ := hv.2.2.2.2.2.2.2.2.1 hvl
  have hu : (V n).undo ≠ none → (V n).made = false :=
    hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ha hbat
  have hqn' : (stripU n S).queue[n.val]! = [] := hx.hq0
  have hv' := nodeOk_liftC (R := R.syncOff) hqn'
    (nodeOkD_syncOff ha hbat hm hpar0 hx.hdn hu (nodeOkD_stripU hbat hv))
  have hnB1 : NetOk R.syncOff (liftC (stripU n S)) net :=
    netOkD_toB1L ha hs.1.2.2.2.2.2.1 (netOkD_stripU n hs.2.2.1)
  obtain ⟨-, -, lp3, lp4, -⟩ := hv'.leader hvl
  have hMO : MatchOk (R := R.syncOff) (liftC (stripU n S)) n r₁.p :=
    (quiet_reachP (S := liftC (stripU n S)) hx.hc hnB1 hx.d1 (fun q hq hne => (hv'.qs q hq).qmsg hne)
      hx.hr (hpl.trans hvl.symm) hpt hplog).2.2.1 hpl ⟨lp3, lp4⟩
  refine ⟨?_, ?_, fun j k hk hkt => ?_, fun j hj => ?_, ?_⟩
  · show r.leaders.contains { server := nameOf (nodeId n), term := uint.Z r₁.p.term } = true
    rw [hlead, hpt]; exact l1
  · show r.ledLog.get (uint.Z r₁.p.term) = .ok (logOf r₁.full)
    rw [hx.hfl]; exact hrll
  · change uint.Z k ≤ uint.Z (matchOf r₁.p (nodeId j)) at hk
    change plogTermAt r₁.p.base r₁.p.log k = some r₁.p.term at hkt
    exact stripU_ackX (n := n) (S := S) (hMO.1 j k hk hkt)
  · exact (hMO.2 j hj).imp_right (stripU_ackX (n := n) (S := S))
  · intro _
    show ((memQ S r n.val it i).confirmed[n.val]!).term = uint.Z r₁.p.term ∧
      ((V n).dur.log.length : Int) ≤ ((memQ S r n.val it i).confirmed[n.val]!).index
    rw [hpt]
    exact l5 (.inl (by rw [hx.hdn]; rfl))

/-! ## `InMemory` and `MemOk` per kind -/

set_option maxHeartbeats 4000000 in
/-- **A leader's commit at its `mem`** (`ReadyKind.cmt`): `InMemory` of its report (`cmt_mem`), the
leaders and leader logs kept, `chain` and `termLen` raised to the commit (`commit_fieldsM`), and
`MemOk`. -/
theorem memOk_cmt (hs : AntSimD R dec S V net xnet) (hx : LdCtx R.syncOff dec V net xnet G n r₁ rd S)
    (hvl : (V n).ps.role = .leader) (hpl : r₁.p.role = .leader) (hpt : r₁.p.term = (V n).ps.term)
    (hpv : r₁.p.vote = (V n).ps.vote) (hplog : r₁.p.log = (V n).ps.log) (hents : rd.ents = [])
    (hlt : uint.Z (V n).ps.commit < uint.Z r₁.p.commit)
    (hcm : CmtOk (CfgM.simple R.voters0 ∅) r₁.p r₁.p.commit) (hns : NoSelf (nodeId n) r₁.p) :
    ∃ r : MemResult, S.inMemory n.val (evReady (nodeId n) (V n).byE (roleOf .leader) r₁.p.term
        r₁.p.vote r₁.p.commit []) = .ok r ∧ r.ok = true ∧ MemOk R dec S V G n r (uint.Z r₁.p.commit) ∧
      r.leaders = S.leaders ∧ r.ledLog.get (uint.Z r₁.p.term) = .ok (logOf r₁.p.log) ∧
      uint.Z r₁.p.commit ≤ r.chain.length ∧
      r.chain.take (uint.Z r₁.p.commit).toNat = (logOf r₁.p.log).take (uint.Z r₁.p.commit).toNat ∧
      (∃ q ∈ r.termLen, q.1 ≤ uint.Z r₁.p.term ∧ uint.Z r₁.p.commit ≤ q.2) := by
  obtain ⟨-, hk, -, -, hll, hm'⟩ := cmt_mem hx hvl hpl hpt hpv hplog hents hlt hcm hns
  have hb := hx.hb
  have hv := hs.2.2.2.2 n
  obtain ⟨l1, -⟩ := hv.2.2.2.2.2.2.2.2.1 hvl
  have hcL0 : uint.Z r₁.p.commit ≤ r₁.p.log.length := by
    have := nat_commit_le hx.hrf; rw [hx.hfl] at this; exact this
  have hcG : r₁.p.log.take (uint.nat r₁.p.commit) = G.committed.take (uint.nat r₁.p.commit) := by
    rw [← hx.hfl]; exact hx.hrf.2.2.1
  have hcmi : S.commitIndex[n.val]! < uint.Z r₁.p.commit := by rw [hx.d4]; exact hlt
  have himax : imax (tlOld S.termLen (uint.Z r₁.p.term)) (uint.Z r₁.p.commit) = uint.Z r₁.p.commit := by
    unfold imax; split <;> omega
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := commit_fieldsM (n := n) (T := r₁.p.term) hb.2.1 hx.hgo1 hcL0
    hcG hx.hrf.2.1 hx.hrf.2.2.2.1 hcmi
  simp only [hcmi, true_and, himax] at f1 f2 f3 f4 f5 f6 f7
  have hT : S.currentTerm[n.val]! = uint.Z r₁.p.term := by rw [hx.d1, hpt]
  have hrole : S.role[n.val]! = leader := by rw [hx.d5, hvl]; rfl
  have hc0 : 0 < uint.Z r₁.p.commit := by have := uint_Z_nonneg (V n).ps.commit; omega
  refine ⟨_, hm', rfl, ?_, rfl, hll, f2.1, f2.2, f4.resolve_left (by omega)⟩
  exact {
    hrole := rfl
    hviol := rfl
    hmem := ⟨rfl, rfl⟩
    lsub := fun l hl => hl
    lnew := fun l hl hn => absurd hl hn
    lself := by rw [hT, hpt]; exact List.contains_iff_mem.mp l1
    hll := .inl rfl
    llk := fun _ _ _ => rfl
    lconf := hs.2.1.1.ledConfOk
    hchain := f1
    chainG := f6
    tlLen := f3
    tlDom := f5
    tlG := f7
    tlSort := with_sorted _ _ hb.tlSorted
    tlMono := fun T' => by
      show tlOld S.termLen T' ≤ tlOld (S.termLen.with (uint.Z r₁.p.term) (uint.Z r₁.p.commit)) T'
      rw [tlOld_with]
      by_cases h : T' = uint.Z r₁.p.term
      · rw [if_pos h, h]; omega
      · rw [if_neg h]; exact Int.le_refl _
    tlNew := fun T' h => by
      change tlOld S.termLen T' < tlOld (S.termLen.with (uint.Z r₁.p.term) (uint.Z r₁.p.commit)) T' at h
      rw [tlOld_with] at h
      have hT' : T' = uint.Z r₁.p.term := by
        by_cases e : T' = uint.Z r₁.p.term
        · exact e
        · rw [if_neg e] at h; omega
      refine ⟨by rw [hT', hT], fun k hkn hkl hkt => hkn (hx.hlu k hkl ?_)⟩
      rw [hkt, hT', hpt]; exact l1
    tlSelf := by
      show (_ → _ ≤ tlOld (S.termLen.with (uint.Z r₁.p.term) (uint.Z r₁.p.commit)) _) ∧
        tlOld (S.termLen.with (uint.Z r₁.p.term) (uint.Z r₁.p.commit)) _ ≤ _
      rw [hT, tlOld_with, if_pos rfl]
      exact ⟨fun _ => Int.le_refl _, Int.le_refl _⟩
    cge := fun c0 h => by
      rw [memCommit_nil hx.hq0] at h; cases h; exact Int.le_of_lt hcmi
    wasNF := by rw [hrole]; decide }

set_option maxHeartbeats 4000000 in
/-- **A leader's proposal at its `mem`** (`ReadyKind.prop`): `InMemory` of its report (`prop_mem`),
the term's leader log raft's new one, the tally kept, and `MemOk`. -/
theorem memOk_prop (hs : AntSimD R dec S V net xnet) (hx : LdCtx R.syncOff dec V net xnet G n r₁ rd S)
    (hnorm : ∀ x ∈ rd.ents, x.Type' = W32 0)
    (es : List EntryM) (hby : (V n).byE = go!"propose") (hvl : (V n).ps.role = .leader) (hne : es ≠ [])
    (hents : rd.ents = es.mapIdx (stamp (V n).ps.term (plastIndex (V n).ps)))
    (hplog : r₁.p.log = (V n).ps.log ++ rd.ents) (hpl : r₁.p.role = .leader)
    (hpt : r₁.p.term = (V n).ps.term) (hpv : r₁.p.vote = (V n).ps.vote)
    (hpc : r₁.p.commit = (V n).ps.commit) :
    ∃ r : MemResult, S.inMemory n.val (evReady (nodeId n) (V n).byE (roleOf .leader) r₁.p.term
        r₁.p.vote r₁.p.commit rd.ents) = .ok r ∧ r.ok = true ∧ MemOk R dec S V G n r (uint.Z r₁.p.commit) ∧
      r.ledLog.get (uint.Z r₁.p.term) = .ok (logOf r₁.p.log) ∧ r₁.p.matched = (V n).ps.matched := by
  obtain ⟨e, es', hE, hmt, hll, -, hm'⟩ := prop_mem hx es hby hvl hne hents hplog hpl hpt hpv hpc
  have hb := hx.hb
  have hv := hs.2.2.2.2 n
  obtain ⟨l1, -⟩ := hv.2.2.2.2.2.2.2.2.1 hvl
  have hT : S.currentTerm[n.val]! = uint.Z r₁.p.term := by rw [hx.d1, hpt]
  have hrole : S.role[n.val]! = leader := by rw [hx.d5, hvl]; rfl
  have hcmi : S.commitIndex[n.val]! = uint.Z r₁.p.commit := by rw [hx.d4, hpc]
  have hLeq : logOf (V n).ps.log ++ logOf (e :: es') = logOf r₁.p.log := by
    rw [hplog, hE]; unfold logOf; rw [List.map_append]
  have hlogG : r₁.p.log ∈ G.logs := by rw [← hx.hfl]; exact hx.hrf.1
  obtain ⟨-, l0, hcamp, hl0p⟩ := hx.hrf.2.2.2.2.1 hpl
  rw [hx.hfl] at hl0p
  have hTL := hb.termLenOkM.lead_nil hx.hq0 hrole
  rw [hcmi] at hTL
  have hnorm' : ∀ x ∈ e :: es', x.Type' = W32 0 := by rw [← hE]; exact hnorm
  rw [hby, hE]
  refine ⟨_, hm', rfl, ?_, TermFn.get_with_self _ _ _, hmt⟩
  exact {
    hrole := rfl
    hviol := rfl
    hmem := ⟨rfl, rfl⟩
    lsub := fun l hl => hl
    lnew := fun l hl hn => absurd hl hn
    lself := by rw [hT, hpt]; exact List.contains_iff_mem.mp l1
    hll := .inr ⟨logOf r₁.p.log, by rw [hT], fun l hl' => by
        rw [hT, hll] at hl'; cases hl'; rw [← hLeq]; exact List.prefix_append _ _,
      r₁.p.log, hlogG, rfl, r₁.p.term, l0, hT.symm, hcamp, hl0p⟩
    llk := fun k hk hvk => by
      show (S.ledLog.with (uint.Z r₁.p.term) (logOf r₁.p.log)).get _ = _
      refine rr_get_with_ne _ _ fun e => hk (hx.hlu k ?_ ?_)
      · rw [(hs.2.2.2.2 k).2.1.1, hvk]; rfl
      · rw [leader_ct hs hvk, e, hpt]; exact l1
    lconf := fun T' h => by
      change (S.ledLog.with (uint.Z r₁.p.term) (logOf r₁.p.log)).has T' = true at h
      by_cases eT : T' = uint.Z r₁.p.term
      · subst eT
        obtain ⟨l, a, cs, h1, h2, h3, h4, h5⟩ := hs.2.1.1.ledConfOk _ (TermFn.has_of_get hll)
        rw [hll] at h1
        have e1 : logOf (V n).ps.log = logOf l := Except.ok.inj h1
        refine ⟨l ++ (e :: es'), a, cs, ?_, h2, cfgFold_take_append_normal h3 hnorm', h4,
          fun hcc x hx' => (List.mem_append.mp hx').elim (h5 hcc x) (hnorm' x)⟩
        show (S.ledLog.with (uint.Z r₁.p.term) (logOf r₁.p.log)).get (uint.Z r₁.p.term) = _
        rw [TermFn.get_with_self]
        have e2 : logOf (l ++ (e :: es')) = logOf l ++ logOf (e :: es') := by
          unfold logOf; rw [List.map_append]
        rw [e2, ← e1, hLeq]
      · rcases has_with_cases h with h' | h'
        · exact absurd h' eT
        · obtain ⟨l, a, cs, h1, h2, h3, h4, h5⟩ := hs.2.1.1.ledConfOk T' h'
          refine ⟨l, a, cs, ?_, h2, h3, h4, h5⟩
          show (S.ledLog.with (uint.Z r₁.p.term) (logOf r₁.p.log)).get T' = _
          rw [rr_get_with_ne _ _ eT]; exact h1
    hchain := List.prefix_refl _
    chainG := hx.hgo1.2.2.2.2.1
    tlLen := hb.2.1
    tlDom := fun q hq => ⟨q, hq, rfl, Int.le_refl _⟩
    tlG := hx.hgo1.2.2.2.2.2.1
    tlSort := hb.tlSorted
    tlMono := fun _ => Int.le_refl _
    tlNew := fun _ h => absurd h (Int.lt_irrefl _)
    tlSelf := hTL
    cge := fun c0 h => by
      rw [memCommit_nil hx.hq0] at h; cases h; exact Int.le_of_eq hcmi
    wasNF := by rw [hrole]; decide }

set_option maxHeartbeats 8000000 in
/-- **A candidate's win at its `mem`** (`ReadyKind.win`): `InMemory` of its report (`win_mem`), the
term's leader log raft's, and `MemOk`; with what the win's leader part reads. -/
theorem memOk_win (hs : AntSimD R dec S V net xnet) (hx : LdCtx R.syncOff dec V net xnet G n r₁ rd S)
    (hnorm : EntsNormal r₁.full)
    (src : w64) (rej : Bool) (mt : GMap w64 w64) (hvc : (V n).ps.role = .candidate)
    (hsrc : (∃ m, RecvAt (nodeId n) net (V n) m ∧ m.ty = .voteResp ∧ m.term = (V n).ps.term ∧
        m.src = src ∧ m.reject = rej) ∨ (src = nodeId n ∧ rej = false ∧ ∃ q ∈ (V n).qs, q.ty = .voteResp))
    (hq : JQuorum (CfgM.simple R.voters0 ∅) (granted (recordVote (V n).ps.votes src (!rej))))
    (hlm : LeaderMatchOk (nodeId n) (V n).ps mt)
    (hL : LeadC (CfgM.simple R.voters0 ∅) (nodeId n)
      (pwinState (nodeId n) { (V n).ps with votes := recordVote (V n).ps.votes src (!rej) } mt) r₁.p)
    (hents : rd.ents = [pleaderEntry (V n).ps]) (hpc : r₁.p.commit = (V n).ps.commit) :
    ∃ r : MemResult, S.inMemory n.val (evReady (nodeId n) (V n).byE (roleOf .leader) r₁.p.term
        r₁.p.vote r₁.p.commit rd.ents) = .ok r ∧ r.ok = true ∧ MemOk R dec S V G n r (uint.Z r₁.p.commit) ∧
      r.ledLog.get (uint.Z r₁.p.term) = .ok (logOf r₁.p.log) ∧
      r₁.p.log = (V n).ps.log ++ [pleaderEntry (V n).ps] ∧
      (∀ j : Fin R.N, j ≠ n → matchOf r₁.p (nodeId j) = W64 0) ∧
      S.currentTerm[n.val]! = uint.Z r₁.p.term ∧ 0 < uint.Z r₁.p.term ∧ r₁.p.term = (V n).ps.term := by
  obtain ⟨hpl, hpt', -, hplog', hmt, hT, hnl, htl0, hcT, -, d11, hTpos, hm'⟩ :=
    win_mem hx src rej mt hvc hsrc hq hlm hL hents hpc
  have hb := hx.hb
  have hGl := hx.hrf.2.2.2.2.1 hpl
  obtain ⟨l0, hcamp, hl0p⟩ := hGl.2
  rw [hx.hfl] at hl0p
  have hlogG : r₁.p.log ∈ G.logs := by rw [← hx.hfl]; exact hx.hrf.1
  have hcmi : S.commitIndex[n.val]! = uint.Z r₁.p.commit := by rw [hx.d4, hpc]
  have hcfgI : S.config[n.val]! = R.cfg.initConf := by
    rw [hx.hconf, ← confView_c0]; unfold confView; rw [hx.hcf]; rfl
  have hldm : ({ server := nameOf (nodeId n), term := uint.Z r₁.p.term } : LeaderRec) ∈
      lset.add S.leaders ({ server := nameOf (nodeId n), term := uint.Z r₁.p.term } : LeaderRec) :=
    mem_lset_add.mpr (.inr rfl)
  rw [hents]
  refine ⟨_, hm', rfl, ?_, TermFn.get_with_self _ _ _, hplog', hmt, hT, hTpos, hpt'⟩
  exact {
    hrole := rfl
    hviol := rfl
    hmem := ⟨rfl, rfl⟩
    lsub := fun l hl' => mem_lset_add.mpr (.inl hl')
    lnew := fun l hl' hn => by
      rcases mem_lset_add.mp hl' with h | h
      · exact absurd h hn
      · refine ⟨h.trans ?_, r₁.p.term, hGl.1, hT.symm⟩
        congr 1
        exact hT.symm
    lself := by rw [hT]; exact hldm
    hll := .inr ⟨logOf r₁.p.log, by rw [hT], fun l hl' => by
        rw [hT] at hl'; exact absurd (TermFn.has_of_get hl') (by rw [hnl]; decide),
      r₁.p.log, hlogG, rfl, r₁.p.term, l0, hT.symm, hcamp, hl0p⟩
    llk := fun k _ hvk => by
      show (S.ledLog.with (uint.Z r₁.p.term) (logOf r₁.p.log)).get _ = _
      refine rr_get_with_ne _ _ fun e => ?_
      obtain ⟨-, l2, -⟩ := (hs.2.2.2.2 k).2.2.2.2.2.2.2.2.1 hvk
      have h2 := TermFn.has_of_get l2
      rw [e, hnl] at h2; cases h2
    lconf := fun T' h => by
      change (S.ledLog.with (uint.Z r₁.p.term) (logOf r₁.p.log)).has T' = true at h
      by_cases e : T' = uint.Z r₁.p.term
      · subst e
        refine ⟨r₁.p.log, 0, R.c0, TermFn.get_with_self _ _ _, ?_, rfl, ?_, fun _ => ?_⟩
        · show (S.ledAt.with (uint.Z r₁.p.term) (S.confAt[n.val]!)).get (uint.Z r₁.p.term) = _
          rw [TermFn.get_with_self, d11] <;> rfl
        · show (S.ledConf.with (uint.Z r₁.p.term) (S.config[n.val]!)).get (uint.Z r₁.p.term) = _
          rw [TermFn.get_with_self, hcfgI, confView_c0]
        · rw [← hx.hfl]; exact hnorm
      · rcases has_with_cases h with h' | h'
        · exact absurd h' e
        · obtain ⟨l, a, cs, h1, h2, h3, h4, h5⟩ := hs.2.1.1.ledConfOk T' h'
          refine ⟨l, a, cs, ?_, ?_, h3, ?_, h5⟩
          · show (S.ledLog.with (uint.Z r₁.p.term) (logOf r₁.p.log)).get T' = _
            rw [rr_get_with_ne _ _ e]; exact h1
          · show (S.ledAt.with (uint.Z r₁.p.term) (S.confAt[n.val]!)).get T' = _
            rw [rr_get_with_ne _ _ e]; exact h2
          · show (S.ledConf.with (uint.Z r₁.p.term) (S.config[n.val]!)).get T' = _
            rw [rr_get_with_ne _ _ e]; exact h4
    hchain := List.prefix_refl _
    chainG := hx.hgo1.2.2.2.2.1
    tlLen := hb.2.1
    tlDom := fun q hq => ⟨q, hq, rfl, Int.le_refl _⟩
    tlG := hx.hgo1.2.2.2.2.2.1
    tlSort := hb.tlSorted
    tlMono := fun _ => Int.le_refl _
    tlNew := fun _ h => absurd h (Int.lt_irrefl _)
    tlSelf := by
      show (_ → _ ≤ tlOld S.termLen _) ∧ tlOld S.termLen _ ≤ _
      rw [hT, htl0, hx.d3]
      refine ⟨fun h => ?_, uint_Z_nonneg _⟩
      by_cases h0 : uint.Z r₁.p.commit = 0
      · omega
      · have := hcT (by have := uint_Z_nonneg r₁.p.commit; omega); omega
    cge := fun c0 h => by
      rw [memCommit_nil hx.hq0] at h; cases h; exact Int.le_of_eq hcmi
    wasNF := by rw [hx.d5, hvc]; decide }

end memLead

end AntSim
end EtcdGrove
end Perennial
