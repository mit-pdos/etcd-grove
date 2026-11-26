/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: a leader's proposal `Ready` (#33 S4, `antSim_ready`)

The `prop` kind (`ReadyKind.prop`: `ProposeEnd`'s entries stamped at the leader's term appended at
its log's end, its commit unchanged): `InMemory`'s store (`inMemory_lprop`) and `OnDisk`'s
(`onDisk_lstore`) evaluated, the side conditions `ReadyOk`. The leader's `Match` values are
`ProposeEnd`'s unchanged (`prop_matched`), so `LeaderPart`'s ack facts at the old log carry over;
an index among the new entries is covered by the store's own ack fact (the node) or by the ack at
another voter's `Match` (which then reaches past the old log).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Ready

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open AntCheck go_etcd_io.raft.v3 GMap

section prop
variable [GooseExts]

/-! ## Helpers -/

theorem plog_append_le {l ents : List EntryM} {k : w64} (hk : uint.Z k ≤ l.length) :
    plogTermAt base0 (l ++ ents) k = plogTermAt base0 l k := by
  have hk0 : 0 ≤ uint.Z k := by word
  by_cases h0 : uint.Z k = 0
  · have hb : uint.Z (base0 : go_etcd_io.raft.v3.entryID).index' = 0 := rfl
    unfold plogTermAt; rw [hb, if_neg (by omega), if_pos h0, if_neg (by omega), if_pos h0]
  · have := plog_take_append (l := l) (ents := ents) (j := l.length) (Nat.le_refl _) (k := k) (by omega)
    rw [List.take_length] at this
    rw [this, if_pos hk]

theorem has_with_cases {α : Type} {f : TermFn α} {t t' : Int} {v : α} (h : (f.with t v).has t' = true) :
    t' = t ∨ f.has t' = true := by
  by_cases e : t' = t
  · exact .inl e
  · right
    obtain ⟨x, hx⟩ := rr_get_of_has h
    rw [rr_get_with_ne _ _ e] at hx
    exact TermFn.has_of_get hx

theorem logIdx_len_lt {l : List EntryM} (hl : LogIdx l) (hne : l ≠ []) : (l.length : Int) < 2 ^ 64 := by
  have hlt : l.length - 1 < l.length := by
    have := List.length_pos_iff.mpr hne; omega
  have h := hl (l.length - 1) l[l.length - 1] (List.getElem?_eq_getElem hlt)
  have : uint.Z l[l.length - 1].Index' < 2 ^ 64 := by word
  omega

/-- A proposal's state keeps the `Match` values (`ProposeEnd`: `pappend` and `psendMsgs`). -/
theorem prop_matched {kk : NodeK} {cf : CfgM} {id : w64} {net : List Msg} {v : NodeView} {ps₁ : PState}
    {ents : List EntryM}
    (hr : ReachO kk cf id net v ps₁) (hby : v.byE = go!"propose") (hvl : v.ps.role = .leader)
    (hne : ents ≠ []) (hplog : ps₁.log = v.ps.log ++ ents)
    (hqs : ∀ q ∈ v.qs, SelfMsg id v.ps.term q) (hX : v.ps.outbox = []) :
    ps₁.matched = v.ps.matched := by
  have hlne : ps₁.log ≠ v.ps.log := by
    intro h; rw [h] at hplog
    have := congrArg List.length hplog
    rw [List.length_append] at this
    exact hne (List.length_eq_zero_iff.mp (by omega))
  cases hr with
  | stay _ => exact absurd rfl hlne
  | recv m _ _ hbe =>
    have h' : (go!"propose" : Str) ≠ go!"recv" := by decide
    rw [hby] at hbe; exact absurd hbe h'
  | tick _ _ hbe =>
    have h' : (go!"propose" : Str) ≠ go!"tick" := by decide
    have h'' : (go!"propose" : Str) ≠ go!"campaign" := by decide
    rcases hbe with hbe | hbe <;> rw [hby] at hbe
    · exact absurd hbe h'
    · exact absurd hbe h''
  | propose d _ _ _ hs =>
    unfold ProposeEnd at hs
    rw [if_pos hvl] at hs
    rcases hs with rfl | ⟨es, ms, -, -, rfl⟩
    · exact absurd rfl hlne
    · rfl
  | advance _ _ _ _ ha =>
    have hP : AdvP cf id v.ps True ps₁ :=
      advP_run hX ha hqs (fun _ _ _ => trivial) (fun _ _ hc => absurd (hc.symm.trans hvl) (by decide))
        (.inl (.inl rfl))
    rcases hP with (heq | ⟨hc, -⟩) | ⟨-, hL, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩
    · rw [heq] at hlne; exact absurd rfl hlne
    · rw [hvl] at hc; cases hc
    · exact absurd hL.2.2.2.2.1 hlne
    · rw [hvl] at hc; cases hc
    · rw [hvl] at hc; cases hc

/-- No conf-change entry among normal entries. -/
theorem confCount_normal {es : List EntryM} (h : ∀ e ∈ es, e.Type' = W32 0) : confCount es = 0 := by
  unfold confCount
  rw [List.countP_eq_zero]
  intro e he
  have h0 := h e he
  simp only [decide_eq_true_eq, IsConfEnt, h0]
  have e0 : uint.Z (W32 0) = 0 := rfl
  have e1 : uint.Z (W32 1) = 1 := rfl
  have e2 : uint.Z (W32 2) = 2 := rfl
  rintro (h | h)
  · have h' : uint.Z (W32 0) = uint.Z (W32 1) := by rw [h]
    rw [e0, e1] at h'; omega
  · have h' : uint.Z (W32 0) = uint.Z (W32 2) := by rw [h]
    rw [e0, e2] at h'; omega

/-- The configuration fold of a prefix is unchanged by normal entries appended to the log. -/
theorem cfgFold_take_append_normal {dec : CCDec} {c0 cs : CCState} {l es : List EntryM} {a : Nat}
    (hf : cfgFold dec c0 (l.take a) = some cs) (hes : ∀ e ∈ es, e.Type' = W32 0) :
    cfgFold dec c0 ((l ++ es).take a) = some cs := by
  by_cases h : a ≤ l.length
  · rw [List.take_append_of_le_length h]; exact hf
  · rw [List.take_of_length_le (by omega)] at hf
    rw [List.take_append, List.take_of_length_le (by omega), cfgFold_append, hf, Option.bind_some]
    exact cfgFoldFrom_zero _ _ _ _
      (confCount_normal (fun e he => hes e (List.mem_of_mem_take he)))

section ready
variable {R : RunCfg} {dec : CCDec} {S : State} {V : Fin R.N → NodeView} {net : List Msg}
  {xnet : List XMsg} {evs : List Event} {G : RaftFacts} {n : Fin R.N} {r₁ : RState} {rd : ReadyD}
  {S1 : State}

set_option maxHeartbeats 4000000 in
/-- **`antSim_ready` for a leader's proposal** (`ReadyKind.prop`). -/
theorem ready_prop (hx : RdCtx R dec S V net xnet evs G n r₁ rd S1)
    (es : List EntryM) (hby : (V n).byE = go!"propose") (hvl : (V n).ps.role = .leader) (hne : es ≠ [])
    (hents : rd.ents = es.mapIdx (stamp (V n).ps.term (plastIndex (V n).ps)))
    (hplog : r₁.p.log = (V n).ps.log ++ rd.ents) (hpl : r₁.p.role = .leader)
    (hpt : r₁.p.term = (V n).ps.term) (hpv : r₁.p.vote = (V n).ps.vote)
    (hpc : r₁.p.commit = (V n).ps.commit) :
    ReadyGoal R dec V net xnet evs G n r₁ rd := by
  have hb := hx.hs1.2.1
  have hgo1 := hx.hgo1
  have hv := hx.hs1.2.2.2.2 n
  have ha := hx.ha
  have hc : S1.cfg = R.cfg := hx.hc
  have hrl : S1.role.length = R.N := hx.hs1.1.2.2.2.2.2.2.1
  have hn3 := hx.hn3
  have hrf := hx.hrf
  have hfl := hx.hfl
  have hlogG : r₁.p.log ∈ G.logs := by rw [← hfl]; exact hrf.1
  have hfullL : logOf (V n).r.full = logOf (V n).ps.log := by
    rw [← hx.d3, hv.disk.2.2.1, hx.hdk n]; rfl
  obtain ⟨lp1, lp2, lp3, lp4, -⟩ := hv.leader hvl
  rw [hfullL] at lp2
  rw [hx.d8] at lp3
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hbase, hidx, -⟩ := id hx.hro
  have hqsS := hx.hqs
  have d7 := hx.d7
  -- the entries
  have hEne : rd.ents ≠ [] := by
    rw [hents]; intro h; exact hne (List.mapIdx_eq_nil_iff.mp h)
  obtain ⟨e, es', hE⟩ : ∃ e es', rd.ents = e :: es' := by
    cases h : rd.ents with
    | nil => exact absurd h hEne
    | cons e es' => exact ⟨e, es', rfl⟩
  have hmt : r₁.p.matched = (V n).ps.matched := prop_matched hx.hr hby hvl hEne hplog hqsS d7
  have hT : S1.currentTerm[n.val]! = uint.Z r₁.p.term := by rw [hx.d1, hpt]
  have hlogn : S1.log[n.val]! = logOf (V n).ps.log := hx.d3
  have hrole : S1.role[n.val]! = leader := by rw [hx.d5, hvl]; rfl
  have hll : S1.ledLog.get (uint.Z r₁.p.term) = .ok (logOf (V n).ps.log) := by rw [hpt]; exact lp2
  have hLeq : logOf (V n).ps.log ++ logOf (e :: es') = logOf r₁.p.log := by
    rw [hplog, hE]; unfold logOf; rw [List.map_append]
  have hfirst0 : uint.Z e.Index' = ((V n).ps.log.length : Int) + 1 := by
    have h := hidx (V n).ps.log.length e (by rw [hplog, hE, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl)
    exact h
  have hfirst : uint.Z e.Index' = ((logOf (V n).ps.log).length : Int) + 1 := by rw [logOf_length]; exact hfirst0
  have hterms : ∀ x ∈ e :: es', uint.Z x.Term' = uint.Z r₁.p.term := by
    intro x hx'
    rw [← hE, hents] at hx'
    obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.mp hx'
    rw [hpt]; rfl
  have hcL0 : uint.Z r₁.p.commit ≤ r₁.p.log.length := by have := nat_commit_le hrf; rw [hfl] at this; exact this
  -- the old commit is within the old log
  have hcmL : uint.Z r₁.p.commit ≤ (V n).ps.log.length := by
    obtain ⟨h1, h2⟩ := hb.2.2.1 n
    have hlen := congrArg List.length h2
    rw [hlogn] at hlen
    simp only [List.length_take, logOf_length] at hlen
    rw [hpc, ← hx.d4]; omega
  have hcmi : S1.commitIndex[n.val]! = uint.Z r₁.p.commit := by rw [hx.d4, hpc]
  have htermc : termAt (logOf r₁.p.log) (uint.Z r₁.p.commit) =
      termAt (logOf (V n).ps.log) (uint.Z r₁.p.commit) := by
    rw [← hLeq]; exact rr_termAt_append _ _ _ (by rw [logOf_length]; exact hcmL)
  have hTL := (hb.termLenOk.2 n hrole)
  rw [hlogn, hcmi, hT] at hTL
  have hcm : (decide (uint.Z r₁.p.commit > tlOld S1.termLen (uint.Z r₁.p.term)) &&
      (termAt (logOf (V n).ps.log ++ logOf (e :: es')) (uint.Z r₁.p.commit) == uint.Z r₁.p.term)) = false := by
    rw [hLeq, htermc]
    by_cases h : termAt (logOf (V n).ps.log) (uint.Z r₁.p.commit) = uint.Z r₁.p.term
    · have := hTL.1 h
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; left; omega
    · simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]; right; exact h
  have hcnZ : ((uint.nat r₁.p.commit : Nat) : Int) = uint.Z r₁.p.commit := by word
  have hrec : uint.Z r₁.p.commit = 0 ∨ recordedIn S1.chain S1.termLen (logOf (V n).ps.log ++ logOf (e :: es'))
      (uint.Z r₁.p.commit) (uint.Z r₁.p.term) = .ok true := by
    rcases commit_recorded (c := uint.nat r₁.p.commit) hb hlogn (by rw [hcnZ, hcmi]; exact Int.le_refl _)
      with h0 | ⟨h1, h2, ⟨x, hx1, hx2, hx3⟩, h4⟩
    · left; omega
    · right
      rw [hLeq, ← hcnZ]
      refine recordedIn_true (by rw [logOf_length]; omega) h2 ⟨x, hx1, by rw [hT] at hx2; exact hx2, hx3⟩ ?_
      rw [h4, ← hLeq, List.take_append_of_le_length (by rw [logOf_length]; exact h1)]
  have hdb : DrainBy go!"propose" := hby ▸ reach_byE hx.hr hx.hro hx.hrep
  have hm' := inMemory_lprop n hc go!"propose" hdb r₁.p.term r₁.p.vote r₁.p.commit e es'
    (logOf (V n).ps.log) hrole hT hll hfirst hterms (by rw [hLeq, logOf_length]; exact hcL0) hcm hrec
  rw [hLeq] at hm'
  -- `OnDisk`
  have hL1eq : (S1.log[n.val]!).take (uint.Z e.Index' - 1).toNat ++ logOf (e :: es') = logOf r₁.p.log := by
    rw [hlogn, hfirst, List.take_of_length_le (by omega), hLeq]
  have hcG : r₁.p.log.take (uint.nat r₁.p.commit) = G.committed.take (uint.nat r₁.p.commit) := by
    rw [← hfl]; exact hrf.2.2.1
  have hcch : uint.Z r₁.p.commit ≤ S1.chain.length := by rw [← hcmi]; exact (hb.2.2.1 n).1
  obtain ⟨eqb, heqb⟩ := entriesEqual_logOf r₁.p.log (V n).ps.log
  have hsend : sendableIn S1.leaders (S1.ledLog.with (uint.Z r₁.p.term) (logOf r₁.p.log)) S1.chain S1.termLen
      (AppendFact.mk (nameOf (nodeId n)) (nameOf (nodeId n)) (uint.Z r₁.p.term)
        (uint.Z e.Index' - 1) (termAt (logOf r₁.p.log) (uint.Z e.Index' - 1)) (logOf (e :: es')) 0) = .ok true := by
    have h := sendable_leader (S := { S1 with ledLog := S1.ledLog.with (uint.Z r₁.p.term) (logOf r₁.p.log) })
      (src := nameOf (nodeId n)) (dst := nameOf (nodeId n)) (lg := r₁.p.log) (T := uint.Z r₁.p.term)
      (p := (V n).ps.log.length) (pt := termAt (logOf r₁.p.log) ((V n).ps.log.length : Int)) (es := e :: es') (c := 0)
      (by rw [hpt]; exact lp1) (TermFn.get_with_self _ _ _) rfl
      (by rw [hplog]; simp) (by rw [hplog, ← hE]; simp) (.inl rfl)
    have e1 : (((V n).ps.log.length : Nat) : Int) = uint.Z e.Index' - 1 := by omega
    rw [e1] at h; exact h
  obtain ⟨p, hpm, hod⟩ := onDisk_lstore n hc go!"propose" r₁.p.term r₁.p.vote r₁.p.commit e es'
    (if go!"propose" = go!"recv" then S1.pending[n.val]! else []) (S1.role.set n.val leader) S1.leaders
    (S1.ledLog.with (uint.Z r₁.p.term) (logOf r₁.p.log)) S1.chain S1.termLen S1.viol (logOf r₁.p.log) eqb
    hT.symm (by rw [hx.d2, hpv]) (get!_set_self _ hn3) (by rw [hlogn, logOf_length]; exact hfirst0)
    (TermFn.get_with_self _ _ _) hsend hcmi.symm (by rw [hL1eq, hlogn]; exact heqb)
    (by rw [hL1eq]; exact lm_ok hx.hl hlogG hgo1.2.2.1 hx.hs1.1.2.2.2.2.1) hcch
    (by rw [hL1eq]; exact ch_ok hgo1.2.2.2.2.1 hcG hcch)
  have hlast : uint.Z e.Index' - 1 + ((es'.length + 1 : Nat) : Int) = (r₁.p.log.length : Int) := by
    rw [hplog, hE, List.length_append, List.length_cons]; push_cast; omega
  rw [hL1eq, hlast] at hod
  rw [hL1eq] at hpm
  unfold ReadyGoal
  rw [hpl, hE]
  have hcf : (S1.confirmed.set n.val (Confirmed.mk (uint.Z r₁.p.term) (r₁.p.log.length : Int)))[n.val]! =
      Confirmed.mk (uint.Z r₁.p.term) (r₁.p.log.length : Int) :=
    get!_set_self _ (by rw [hx.hs1.1.2.2.2.2.2.2.2.2.2.2.1]; exact n.isLt)
  have hmsub : ∀ f ∈ S1.msgs, f ∈ lset.add S1.msgs (ackFact (nameOf (nodeId n)) (nameOf (nodeId n))
      (uint.Z r₁.p.term) (r₁.p.log.length : Int)) := fun f hf => mem_lset_add.mpr (.inl hf)
  have hackN : ackFact (nameOf (nodeId n)) (nameOf (nodeId n)) (uint.Z r₁.p.term) (r₁.p.log.length : Int) ∈
      lset.add S1.msgs (ackFact (nameOf (nodeId n)) (nameOf (nodeId n)) (uint.Z r₁.p.term)
        (r₁.p.log.length : Int)) := mem_lset_add.mpr (.inr rfl)
  have hnorm : ∀ x ∈ rd.ents, x.Type' = W32 0 := by
    have h := (ha.facts.conf0 hx.hcc).2.1
    intro x hxe
    refine h x ?_
    show x ∈ r₁.full
    rw [hfl, hplog]; exact List.mem_append_right _ hxe
  rw [hby]
  refine hx.finish (ready_of hx.hq0 hm' rfl (queued_ready _ _ _ _ _ _ _ _ _) hod) ?_
  exact {
    hterm := rfl
    tge := Int.le_of_eq hT
    hvote := .inl ⟨hT.symm, by rw [hx.d2]; show _ = nameOf r₁.p.vote; rw [hpv]⟩
    hlog := rfl
    hcommit := rfl
    cge := Int.le_of_eq hcmi
    hrole := by
      rw [get!_set_self _ hn3]; show leader = roleOf r₁.p.role; rw [hpl]; rfl
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
    msub := hmsub
    mnew := fun f hf hn => by
      rcases mem_lset_add.mp hf with h | h
      · exact absurd h hn
      · subst h
        exact .inr ⟨rfl, rfl, ⟨n, rfl⟩, rfl, .inl ⟨rfl, Int.le_refl _⟩⟩
    vsub := fun y hy => hy
    vnew := fun y hy hn => absurd hy hn
    vin := fun h => absurd rfl h
    lsub := fun l hl => hl
    lnew := fun l hl hn => absurd hl hn
    glead := fun _ => (hrf.2.2.2.2.1 hpl).1
    hll := .inr ⟨rfl, get!_set_self _ hn3, hT.symm,
      fun l hl' => by
        rw [hll] at hl'; cases hl'
        rw [← hLeq]; exact List.prefix_append _ _,
      List.contains_iff_mem.mp (by rw [hpt]; exact lp1),
      by
        obtain ⟨-, l0, h1, h2⟩ := hrf.2.2.2.2.1 hpl
        rw [hfl] at h2
        exact ⟨r₁.p.term, l0, rfl, h1, h2⟩⟩
    hchain := List.prefix_refl _
    chainC := ⟨hcch, ch_ok hgo1.2.2.2.2.1 hcG hcch⟩
    tlLen := hb.2.1
    tlC := by
      rcases hb.2.2.2.1 n with h | ⟨q, hq, h1, h2⟩
      · exact .inl (by rw [← hcmi]; exact h)
      · exact .inr ⟨q, hq, by rw [← hT]; exact h1, by rw [← hcmi]; exact h2⟩
    tlDom := fun q hq => ⟨q, hq, rfl, Int.le_refl _⟩
    chainG := hgo1.2.2.2.2.1
    tlG := hgo1.2.2.2.2.2.1
    logG := hlogG
    cmono := .inr ⟨rfl, TermFn.has_with_self _ _ _, fun ht => by
      obtain ⟨o1, -, -⟩ := hb.2.2.2.2.1 n (logOf (V n).ps.log) (by rw [ht]; exact hll)
      rw [hlogn, logOf_length] at o1
      show (S1.confirmed[n.val]!).index ≤ (r₁.p.log.length : Int)
      rw [hplog, List.length_append]; omega⟩
    hconf := fun l hl' => by
      change (S1.ledLog.with (uint.Z r₁.p.term) (logOf r₁.p.log)).get (uint.Z r₁.p.term) = .ok l at hl'
      rw [TermFn.get_with_self] at hl'; cases hl'
      refine ⟨by rw [logOf_length]; exact Int.le_refl _, by rw [logOf_length]; exact Int.le_refl _, rfl⟩
    lpart := fun _ => ⟨by
        show S1.leaders.contains { server := nameOf (nodeId n), term := uint.Z r₁.p.term } = true
        rw [hpt]; exact lp1,
      by
        show (S1.ledLog.with (uint.Z r₁.p.term) (logOf r₁.p.log)).get (uint.Z r₁.p.term) = .ok (logOf r₁.full)
        rw [hfl]; exact TermFn.get_with_self _ _ _,
      fun j k hk hkt => by
        have hk' : uint.Z k ≤ uint.Z (matchOf (V n).ps (nodeId j)) := by
          change uint.Z k ≤ uint.Z ((r₁.p.matched !! nodeId j).getD (W64 0)) at hk
          unfold matchOf; rw [hmt] at hk; exact hk
        have hkt' : plogTermAt base0 r₁.p.log k = some r₁.p.term := by
          change plogTermAt r₁.p.base r₁.p.log k = some r₁.p.term at hkt
          rw [hbase] at hkt; exact hkt
        obtain ⟨hkl, -⟩ := termAt_of_plog hkt'
        by_cases hkL : uint.Z k ≤ (V n).ps.log.length
        · rw [hplog, plog_append_le hkL, hpt] at hkt'
          have := lp3 j k hk' hkt'
          rw [← hpt] at this
          exact AckIn.mono hmsub this
        · by_cases hjn : j = n
          · subst hjn
            exact ⟨_, hackN, rfl, rfl, rfl, rfl, hkl⟩
          · rcases lp4 j hjn with h0 | h1
            · rw [h0] at hk'; have : uint.Z (W64 0) = 0 := rfl; omega
            · have := AckIn.le h1 hk'
              rw [← hpt] at this
              exact AckIn.mono hmsub this,
      fun j hjn => by
        have e1 : matchOf ((V n).afterReady r₁ rd).ps (nodeId j) = matchOf (V n).ps (nodeId j) := by
          unfold matchOf; show (r₁.p.matched !! nodeId j).getD (W64 0) = _; rw [hmt]
        rw [e1]
        rcases lp4 j hjn with h0 | h1
        · exact .inl h0
        · right; rw [← hpt] at h1; exact AckIn.mono hmsub h1,
      by
        show (S1.confirmed.set n.val (Confirmed.mk (uint.Z r₁.p.term) (r₁.p.log.length : Int)))[n.val]!.term =
            uint.Z r₁.p.term ∧ (r₁.full.length : Int) ≤
            (S1.confirmed.set n.val (Confirmed.mk (uint.Z r₁.p.term) (r₁.p.log.length : Int)))[n.val]!.index
        rw [hcf, hfl]; exact ⟨rfl, Int.le_refl _⟩⟩
    cpart := fun h => absurd (h.symm.trans hpl) (by decide)
    hpend := ha.hpend
    hxpend := ha.hxpend
    hqs := fun q hq => by
      obtain ⟨⟨h1, h2, h3, h4, -⟩, hk⟩ := qs_self hx.hro hx.hso q hq
      rcases hk with ⟨hlr, rfl⟩ | ⟨hc', -⟩
      · refine ⟨h1, h2, h4, .inl ⟨h3, .inl ⟨rfl, hlr, ?_⟩⟩⟩
        refine ⟨_, hackN, rfl, rfl, rfl, rfl, ?_⟩
        show uint.Z (plastIndex r₁.p) ≤ (r₁.p.log.length : Int)
        unfold plastIndex plogLastIndexZ
        rw [hbase]
        have hb0 : uint.Z (base0 : go_etcd_io.raft.v3.entryID).index' = 0 := rfl
        rw [hb0]
        have : uint.Z (W64 (0 + (r₁.p.log.length : Int))) = (r₁.p.log.length : Int) := by
          have := logIdx_len_lt hidx (by rw [hplog, hE]; simp)
          rw [Int.zero_add]; word
        omega
      · exact absurd (hc'.symm.trans hpl) (by decide)
    drain := ha.drain
    hlead := ha.hlead
    hvself := hx.hvs1
    rnf := fun _ _ => by rw [hrole]; decide
    tlMono := fun _ => Int.le_refl _
    tlNew := fun _ h => absurd h (Int.lt_irrefl _)
    tlSelf := fun _ => ⟨fun h => by
        rw [htermc] at h; exact hTL.1 h, hTL.2⟩
    lconf := fun T' h => by
      by_cases eT : T' = uint.Z r₁.p.term
      · subst eT
        obtain ⟨l, a, cs, h1, h2, h3, h4, h5⟩ := hb.ledConfOk _ (TermFn.has_of_get hll)
        rw [hll] at h1
        have e1 : logOf (V n).ps.log = logOf l := Except.ok.inj h1
        refine ⟨l ++ rd.ents, a, cs, ?_, h2, cfgFold_take_append_normal h3 hnorm, h4,
          fun hcc e he => (List.mem_append.mp he).elim (h5 hcc e) (hnorm e)⟩
        rw [TermFn.get_with_self]
        have e2 : logOf (l ++ rd.ents) = logOf l ++ logOf rd.ents := by unfold logOf; rw [List.map_append]
        rw [e2, ← e1, hE, hLeq]
      · rcases has_with_cases h with h' | h'
        · exact absurd h' eT
        · obtain ⟨l, a, cs, h1, h2, h3, h4, h5⟩ := hb.ledConfOk T' h'
          exact ⟨l, a, cs, by rw [rr_get_with_ne _ _ eT]; exact h1, h2, h3, h4, h5⟩
    tlSort := hb.tlSorted }

end ready

end prop

end AntSim
end EtcdGrove
end Perennial
