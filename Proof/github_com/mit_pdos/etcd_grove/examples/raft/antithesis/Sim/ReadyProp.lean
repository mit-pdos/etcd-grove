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

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.ReadyCmt

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open AntCheck go_etcd_io.raft.v3 GMap

section prop
variable [GooseExts]
variable {cf : CfgM}

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
theorem prop_matched {id : w64} {net : List Msg} {v : NodeView} {ps₁ : PState} {ents : List EntryM}
    (hr : Reach id net v ps₁) (hby : v.byE = go!"propose") (hvl : v.ps.role = .leader)
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
  | input inp _ _ hbe _ _ hs =>
    cases inp with
    | recv m =>
      have h' : (go!"propose" : Str) ≠ go!"recv" := by decide
      rw [hby] at hbe; exact absurd hbe h'
    | tick =>
      have h' : (go!"propose" : Str) ≠ go!"tick" := by decide
      rw [hby] at hbe; exact absurd hbe h'
    | propose d =>
      have hs' : ProposeEnd cfgM3 id v.ps (propMsg id d) ps₁ := hs
      unfold ProposeEnd at hs'
      rw [if_pos hvl] at hs'
      rcases hs' with rfl | ⟨es, ms, -, -, rfl⟩
      · exact absurd rfl hlne
      · rfl
  | advance _ _ _ _ ha =>
    have hP : AdvP id v.ps True ps₁ :=
      advP_run hX ha hqs (fun _ _ _ => trivial) (.inl (.inl rfl))
    rcases hP with (heq | ⟨hc, -⟩) | ⟨-, hL, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩
    · rw [heq] at hlne; exact absurd rfl hlne
    · rw [hvl] at hc; cases hc
    · exact absurd hL.2.2.2.2.1 hlne
    · rw [hvl] at hc; cases hc
    · rw [hvl] at hc; cases hc

set_option maxHeartbeats 4000000 in
/-- **`antSim_ready` for a leader's proposal** (`ReadyKind.prop`). -/
theorem ready_prop (S : State) (V : Fin 3 → NodeView) (net : List Msg) (evs : List Event)
    (G : RaftFacts) (n : Fin 3) (ps₁ : PState) (rd : ReadyD)
    (hp : Prefix cfg3 evs S) (hs : AntSim S V net) (hl : RaftLaws G) (hgo : GlobalOk S net G)
    (hr : Reach (nodeId n) net (V n) ps₁) (hro : ReadyOutP (nodeId n) (V n) ps₁ rd)
    (hrf : ReadyFacts G (nodeId n) ps₁)
    (es : List EntryM) (hby : (V n).byE = go!"propose") (hvl : (V n).ps.role = .leader) (hne : es ≠ [])
    (hents : rd.ents = es.mapIdx (stamp (V n).ps.term (plastIndex (V n).ps)))
    (hplog : ps₁.log = (V n).ps.log ++ rd.ents)
    (hpl : ps₁.role = .leader) (hpt : ps₁.term = (V n).ps.term) (hpv : ps₁.vote = (V n).ps.vote)
    (hpc : ps₁.commit = (V n).ps.commit) :
    ReadyGoal S V net evs G n ps₁ rd := by
  obtain ⟨S1, hgc, hs1, hgo1⟩ := antSim_gc S V net G hs hl hgo
  have hs1' := hs1
  obtain ⟨hsh, hb, hnet, hno⟩ := hs1'
  have hc : S1.cfg = cfg3 := hsh.1
  have hrl : S1.role.length = 3 := hsh.2.2.2.2.2.2.1
  have hn3 : n.val < S1.role.length := by rw [hrl]; exact n.isLt
  obtain ⟨hd, hLP, -, -, hQ, -, -, hlo, hvsN⟩ := hno n
  obtain ⟨d1, d2, d3, d4, d5, -, d7, -, -, -, -, -, -⟩ := hd
  have hq0 : S1.queue[n.val]! = [] := (hb.2.1 n).1
  obtain ⟨lp1, lp2, lp3, lp4, lp5⟩ := hLP hvl
  obtain ⟨-, -, -, -, -, -, -, -, hpre, hlen, hbase, hidx, -⟩ := id hro
  have hin : ∀ m ∈ net, InMsg m := fun m hm => ⟨(hnet.1 m hm).1, hnet.2.2.1 m hm⟩
  have hqsS : ∀ q ∈ (V n).qs, SelfMsg (nodeId n) (V n).ps.term q := fun q hq => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hQ q hq
    exact ⟨h1, h2, h3, h4, h5.imp (fun h => h.1) (fun h => h.1)⟩
  have hso := selfOut_reach hr d7 hlo.1 hin hqsS
  -- the entries
  have hEne : rd.ents ≠ [] := by
    rw [hents]; intro h; exact hne (List.mapIdx_eq_nil_iff.mp h)
  obtain ⟨e, es', hE⟩ : ∃ e es', rd.ents = e :: es' := by
    cases h : rd.ents with
    | nil => exact absurd h hEne
    | cons e es' => exact ⟨e, es', rfl⟩
  have hmt : ps₁.matched = (V n).ps.matched := prop_matched hr hby hvl hEne hplog hqsS d7
  have hT : S1.currentTerm[n.val]! = uint.Z ps₁.term := by rw [d1, hpt]
  have hlogn : S1.log[n.val]! = logOf (V n).ps.log := d3
  have hrole : S1.role[n.val]! = leader := by rw [d5, hvl]; rfl
  have hll : S1.ledLog.get (uint.Z ps₁.term) = .ok (logOf (V n).ps.log) := by rw [hpt]; exact lp2
  have hlc : S1.ledConf.get (uint.Z ps₁.term) = .ok cfg3.initConf :=
    hb.ledConfOk _ (TermFn.has_of_get hll)
  have hLeq : logOf (V n).ps.log ++ logOf (e :: es') = logOf ps₁.log := by
    rw [hplog, hE]; unfold logOf; rw [List.map_append]
  have hfirst0 : uint.Z e.Index' = ((V n).ps.log.length : Int) + 1 := by
    have h := hidx (V n).ps.log.length e (by rw [hplog, hE, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl)
    exact h
  have hfirst : uint.Z e.Index' = ((logOf (V n).ps.log).length : Int) + 1 := by rw [logOf_length]; exact hfirst0
  have hterms : ∀ x ∈ e :: es', uint.Z x.Term' = uint.Z ps₁.term := by
    intro x hx
    rw [← hE, hents] at hx
    obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.mp hx
    rw [hpt]; rfl
  have hcL0 := nat_commit_le hrf
  -- the old commit is within the old log
  have hcmL : uint.Z ps₁.commit ≤ (V n).ps.log.length := by
    obtain ⟨h1, h2⟩ := hb.2.2.2.2.1 n
    have hlen := congrArg List.length h2
    rw [hlogn] at hlen
    simp only [List.length_take, logOf_length] at hlen
    rw [hpc, ← d4]; omega
  have hcmi : S1.commitIndex[n.val]! = uint.Z ps₁.commit := by rw [d4, hpc]
  have htermc : termAt (logOf ps₁.log) (uint.Z ps₁.commit) = termAt (logOf (V n).ps.log) (uint.Z ps₁.commit) := by
    rw [← hLeq]; exact rr_termAt_append _ _ _ (by rw [logOf_length]; exact hcmL)
  have hTL := (hb.termLenOk.2 n hrole)
  rw [hlogn, hcmi, hT] at hTL
  have hcm : (decide (uint.Z ps₁.commit > tlOld S1.termLen (uint.Z ps₁.term)) &&
      (termAt (logOf (V n).ps.log ++ logOf (e :: es')) (uint.Z ps₁.commit) == uint.Z ps₁.term)) = false := by
    rw [hLeq, htermc]
    by_cases h : termAt (logOf (V n).ps.log) (uint.Z ps₁.commit) = uint.Z ps₁.term
    · have := hTL.1 h
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; left; omega
    · simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]; right; exact h
  have hcnZ : ((uint.nat ps₁.commit : Nat) : Int) = uint.Z ps₁.commit := by word
  have hrec : uint.Z ps₁.commit = 0 ∨ recordedIn S1.chain S1.termLen (logOf (V n).ps.log ++ logOf (e :: es'))
      (uint.Z ps₁.commit) (uint.Z ps₁.term) = .ok true := by
    rcases commit_recorded (c := uint.nat ps₁.commit) hb hlogn (by rw [hcnZ, hcmi]; exact Int.le_refl _)
      with h0 | ⟨h1, h2, ⟨x, hx, hx1, hx2⟩, h4⟩
    · left; omega
    · right
      rw [hLeq, ← hcnZ]
      refine recordedIn_true (by rw [logOf_length]; omega) h2 ⟨x, hx, by rw [hT] at hx1; exact hx1, hx2⟩ ?_
      rw [h4, ← hLeq, List.take_append_of_le_length (by rw [logOf_length]; exact h1)]
  have hm' := inMemory_lprop n hc go!"propose" (.inr (.inr (.inl rfl))) ps₁.term ps₁.vote ps₁.commit e es'
    (logOf (V n).ps.log) hrole hT hll hfirst hterms (by rw [hLeq, logOf_length]; exact hcL0) hcm hrec
  rw [hLeq] at hm'
  -- `OnDisk`
  have hL1eq : (S1.log[n.val]!).take (uint.Z e.Index' - 1).toNat ++ logOf (e :: es') = logOf ps₁.log := by
    rw [hlogn, hfirst, List.take_of_length_le (by omega), hLeq]
  have hcG := hrf.2.2.1
  have hcch : uint.Z ps₁.commit ≤ S1.chain.length := by rw [← hcmi]; exact (hb.2.2.2.2.1 n).1
  obtain ⟨eqb, heqb⟩ := entriesEqual_logOf ps₁.log (V n).ps.log
  have hsend : sendableIn S1.leaders (S1.ledLog.with (uint.Z ps₁.term) (logOf ps₁.log)) S1.chain S1.termLen
      (AppendFact.mk (nameOf (nodeId n)) (nameOf (nodeId n)) (uint.Z ps₁.term)
        (uint.Z e.Index' - 1) (termAt (logOf ps₁.log) (uint.Z e.Index' - 1)) (logOf (e :: es')) 0) = .ok true := by
    have h := sendable_leader (S := { S1 with ledLog := S1.ledLog.with (uint.Z ps₁.term) (logOf ps₁.log) })
      (src := nameOf (nodeId n)) (dst := nameOf (nodeId n)) (lg := ps₁.log) (T := uint.Z ps₁.term)
      (p := (V n).ps.log.length) (pt := termAt (logOf ps₁.log) ((V n).ps.log.length : Int)) (es := e :: es') (c := 0)
      (by rw [hpt]; exact lp1) (TermFn.get_with_self _ _ _) rfl
      (by rw [hplog]; simp) (by rw [hplog, ← hE]; simp) (.inl rfl)
    have e1 : (((V n).ps.log.length : Nat) : Int) = uint.Z e.Index' - 1 := by omega
    rw [e1] at h; exact h
  obtain ⟨p, hpm, hod⟩ := onDisk_lstore n hc go!"propose" ps₁.term ps₁.vote ps₁.commit e es'
    (if go!"propose" = go!"recv" then S1.pending[n.val]! else []) (S1.role.set n.val leader) S1.leaders
    (S1.ledLog.with (uint.Z ps₁.term) (logOf ps₁.log)) S1.chain S1.termLen S1.viol (logOf ps₁.log) eqb
    hT.symm (by rw [d2, hpv]) (get!_set_self _ hn3) (by rw [hlogn, logOf_length]; exact hfirst0)
    (TermFn.get_with_self _ _ _) hsend hcmi.symm (by rw [hL1eq, hlogn]; exact heqb)
    (by rw [hL1eq]; exact lm_ok hl hrf.1 hgo1.2.2.1 hsh.2.2.2.2.1) hcch
    (by rw [hL1eq]; exact ch_ok hgo1.2.2.2.2.1 hcG hcch)
  have hlast : uint.Z e.Index' - 1 + ((es'.length + 1 : Nat) : Int) = (ps₁.log.length : Int) := by
    rw [hplog, hE, List.length_append, List.length_cons]; push_cast; omega
  rw [hL1eq, hlast] at hod
  have hby' : (V n).byE = go!"propose" := hby
  unfold ReadyGoal
  rw [hpl, hE]
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
    rw [hplog, hE]; simp
  have hrd : rd.ents = e :: es' := hE
  rw [hby]
  refine ready_finish hp hgc hs1 hgo1 hl
    (ready_of hq0 hm' rfl (queued_ready _ _ _ _ _ _ _ _ _) hod) ?_
  exact {
    hterm := rfl
    tge := Int.le_of_eq hT
    hvote := .inl ⟨hT.symm, by show S1.vote n.val = nameOf ps₁.vote; rw [d2, hpv]⟩
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
    hviol := hb.1
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
        exact ⟨ps₁.term, l0, rfl, h1, h2⟩⟩
    hchain := List.prefix_refl _
    chainC := ⟨hcch, ch_ok hgo1.2.2.2.2.1 hcG hcch⟩
    tlLen := hb.2.2.2.1
    tlC := by
      rcases hb.2.2.2.2.2.1 n with h | ⟨q, hq, h1, h2⟩
      · exact .inl (by rw [← hcmi]; exact h)
      · exact .inr ⟨q, hq, by rw [← hT]; exact h1, by rw [← hcmi]; exact h2⟩
    tlDom := fun q hq => ⟨q, hq, rfl, Int.le_refl _⟩
    chainG := hgo1.2.2.2.2.1
    tlG := hgo1.2.2.2.2.2.1
    logG := hrf.1
    cmono := .inr ⟨rfl, TermFn.has_with_self _ _ _, fun ht => by
      obtain ⟨o1, -, -⟩ := hb.2.2.2.2.2.2.1 n (logOf (V n).ps.log) (by rw [ht]; exact hll)
      rw [hlogn, logOf_length] at o1
      show (S1.confirmed[n.val]!).index ≤ (ps₁.log.length : Int)
      rw [hplog, List.length_append]; omega⟩
    hconf := fun l hl' => by
      change (S1.ledLog.with (uint.Z ps₁.term) (logOf ps₁.log)).get (uint.Z ps₁.term) = .ok l at hl'
      rw [TermFn.get_with_self] at hl'; cases hl'
      refine ⟨by rw [logOf_length]; exact Int.le_refl _, by rw [logOf_length]; exact Int.le_refl _, rfl⟩
    lpart := fun _ => ⟨by
        show S1.leaders.contains { server := nameOf (nodeId n), term := uint.Z ps₁.term } = true
        rw [hpt]; exact lp1,
      by
        show (S1.ledLog.with (uint.Z ps₁.term) (logOf ps₁.log)).get (uint.Z ps₁.term) = .ok (logOf ps₁.log)
        exact TermFn.get_with_self _ _ _,
      fun j k hk hkt => by
        have hk' : uint.Z k ≤ uint.Z (matchOf (V n).ps (nodeId j)) := by
          change uint.Z k ≤ uint.Z ((ps₁.matched !! nodeId j).getD (W64 0)) at hk
          unfold matchOf; rw [hmt] at hk; exact hk
        have hkt' : plogTermAt base0 ps₁.log k = some ps₁.term := hkt
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
        have e1 : matchOf ((V n).afterReady ps₁ rd).ps (nodeId j) = matchOf (V n).ps (nodeId j) := by
          unfold matchOf; show (ps₁.matched !! nodeId j).getD (W64 0) = _; rw [hmt]
        rw [e1]
        rcases lp4 j hjn with h0 | h1
        · exact .inl h0
        · right; rw [← hpt] at h1; exact AckIn.mono hmsub h1,
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
    hlead := ⟨fun h => absurd hpl h, (reach_leadOk hnet (hno n) hr).2⟩
    hvself := fun _ => by show ps₁.vote = nodeId n; rw [hpv]; exact hvsN (by rw [hvl]; decide)
    rnf := fun _ _ => by rw [hrole]; decide
    tlMono := fun _ => Int.le_refl _
    tlNew := fun _ h => absurd h (Int.lt_irrefl _)
    tlSelf := fun _ => ⟨fun h => by
        rw [htermc] at h; exact hTL.1 h, hTL.2⟩
    lconf := fun T' h => by
      rcases has_with_cases h with rfl | h
      · exact hlc
      · exact hb.ledConfOk T' h
    tlSort := hb.tlSorted }

end prop

end AntSim
end EtcdGrove
end Perennial
