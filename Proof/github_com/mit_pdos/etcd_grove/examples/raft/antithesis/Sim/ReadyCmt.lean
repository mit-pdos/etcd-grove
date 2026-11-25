/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: a leader's commit `Ready` (#33 S4, `antSim_ready`)

The `cmt` kind (`ReadyKind.cmt`: a leader's new commit, on an acknowledgement received or its own
in `Advance`): `InMemory`'s `cmt` (`inMemory_lcommit`) and `OnDisk` (`onDisk_lcommit`) evaluated,
the side conditions `ReadyOk` (`readyOk_lcmt`). Raft's quorum of `Match` values (`CmtOk`) is the
binding's `Acked` quorum (B 252) through `LeaderPart`'s ack facts (`quiet_reach` carries them to
the `Ready`'s state); the leader's configuration is the initial one (C3's `LedConfOk`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Ready

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open AntCheck go_etcd_io.raft.v3 GMap

/-! ## Quorums -/

theorem voters3_mem (x : w64) : x ∈ voters3 ↔ x = nodeId 0 ∨ x = nodeId 1 ∨ x = nodeId 2 := by
  show ((insert (W64 1) () (insert (W64 2) () (insert (W64 3) () (∅ : GSet w64)))) !! x).isSome = true ↔ _
  have e : ∀ (y : w64) (X : GSet w64), ((insert y () X) !! x).isSome = true ↔ x = y ∨ (X !! x).isSome = true :=
    fun y X => elem_of_insert_set x y X
  rw [e, e, e]
  simp only [GMap.lookup_empty, Option.isSome_none, Bool.false_eq_true, or_false]
  rfl

theorem voters3_size : size voters3 = 3 := by
  have := size_eq_length_set voters3 [nodeId 0, nodeId 1, nodeId 2] (by decide)
    (fun x => by rw [voters3_mem]; simp)
  rw [this]; rfl

/-- A quorum of the three voters holds two of them. -/
theorem jq_two {Q : GSet w64} (hq : JQuorum cfgM3 Q) :
    ∃ a b : Fin 3, a ≠ b ∧ nodeId a ∈ Q ∧ nodeId b ∈ Q := by
  refine Classical.byContradiction fun hne => ?_
  have hsub : ∃ x, Q ∩ voters3 ⊆ ({[x]} : GSet w64) := by
    by_cases h : ∃ a : Fin 3, nodeId a ∈ Q
    · obtain ⟨a, ha⟩ := h
      refine ⟨nodeId a, (elem_of_subseteq _ _).mpr fun y hy => ?_⟩
      rw [elem_of_intersection, voters3_mem] at hy
      rw [elem_of_singleton]
      obtain ⟨hyQ, hy⟩ := hy
      obtain ⟨b, rfl⟩ : ∃ b : Fin 3, y = nodeId b := by
        rcases hy with h | h | h
        · exact ⟨0, h⟩
        · exact ⟨1, h⟩
        · exact ⟨2, h⟩
      refine Classical.byContradiction fun hba => ?_
      exact hne ⟨a, b, fun e => hba (by rw [e]), ha, hyQ⟩
    · refine ⟨nodeId 0, (elem_of_subseteq _ _).mpr fun y hy => ?_⟩
      rw [elem_of_intersection, voters3_mem] at hy
      exfalso
      obtain ⟨hyQ, hy⟩ := hy
      rcases hy with rfl | rfl | rfl
      · exact h ⟨0, hyQ⟩
      · exact h ⟨1, hyQ⟩
      · exact h ⟨2, hyQ⟩
  obtain ⟨x, hx⟩ := hsub
  have h1 := subseteq_size hx
  rw [size_singleton] at h1
  rcases hq.1 with h0 | hq1
  · have : size voters3 = 0 := by
      have h0' : cfgM3.incoming = ∅ := h0
      show size cfgM3.incoming = 0
      rw [h0']; exact size_empty
    rw [voters3_size] at this; cases this
  · change size voters3 < 2 * size (Q ∩ voters3) at hq1
    rw [voters3_size] at hq1
    omega

theorem two_of_length {l : List Str} {x y : Str} (hx : x ∈ l) (hy : y ∈ l) (hne : x ≠ y) :
    2 ≤ l.length := by
  have h1 : (l.filter (fun z => z != x)).length < l.length :=
    List.length_filter_lt_length_iff_exists.mpr ⟨x, hx, by simp⟩
  have h2 : y ∈ l.filter (fun z => z != x) := List.mem_filter.mpr ⟨hy, by simpa using Ne.symm hne⟩
  have h3 : 0 < (l.filter (fun z => z != x)).length := List.length_pos_of_mem h2
  omega

/-- **A quorum of the three voters** (raft's `JQuorum cfgM3`) whose members are in `s` makes `s` a
quorum of the initial configuration (`IsQuorum`, R 129). -/
theorem jq_isQuorum {Q : GSet w64} {s : SSet} (hq : JQuorum cfgM3 Q)
    (hs : ∀ j : Fin 3, nodeId j ∈ Q → s.has (nameOf (nodeId j)) = true) :
    isQuorum s cfg3.initConf = true := by
  obtain ⟨a, b, hab, ha, hb⟩ := jq_two hq
  have hin : ∀ j : Fin 3, (namesL 3).contains (nameOf (nodeId j)) = true := server_has
  have hfa : nameOf (nodeId a) ∈ s.filter (fun x => SSet.has (namesL 3) x) :=
    List.mem_filter.mpr ⟨by simpa [SSet.has] using hs a ha, hin a⟩
  have hfb : nameOf (nodeId b) ∈ s.filter (fun x => SSet.has (namesL 3) x) :=
    List.mem_filter.mpr ⟨by simpa [SSet.has] using hs b hb, hin b⟩
  have h2 := two_of_length hfa hfb (fun h => hab (name_inj h))
  have hl3 : (namesL 3).length = 3 := namesL_length
  unfold isQuorum majority interCount Config.initConf
  rw [cfg3_initVoters]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.length_nil, beq_self_eq_true, Bool.true_or,
    and_true, hl3]
  omega


/-- An ack fact from `j` to `n` at `t` with index at least `k` puts `j` in `Acked(n, t, k)`
(R 344-347). -/
theorem acked_of {S : State} (hc : S.cfg = cfg3) {n j : Fin 3} {t k : Int}
    (h : AckIn S (nameOf (nodeId j)) (nameOf (nodeId n)) t k) :
    (S.acked n.val t k).has (nameOf (nodeId j)) = true := by
  obtain ⟨a, ha, h1, h2, h3, h4, h5⟩ := h
  unfold State.acked
  simp only [SSet.has, List.contains_iff_mem]
  rw [server_of hc n]
  have hmem : nameOf (nodeId j) ∈ S.cfg.server := by
    have := server_has j
    rw [hc, cfg3_server]; simpa [SSet.has] using this
  refine mem_foldl_setAdd (P := fun j' => (S.msgs.any (fun a => a.type == go!"ack" && a.src == j' &&
      a.dst == nameOf (nodeId n) && a.term == t && decide (a.index ≥ k))) = true)
    (nameOf (nodeId j)) S.cfg.server [] (.inr ⟨hmem, ?_⟩)
  exact List.any_eq_true.mpr ⟨a, ha, by simp [h1, h2, h3, h4, h5]⟩


/-! ## The leader's term and `termLen` -/

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

section cmt
variable [GooseExts]

/-- **Election safety in the binding**: a leader `k` at its term, and a leader record of `n` at that
term, are the same node (`GlobalOk`'s leaders are raft's, `RaftLaws`' election safety). -/
theorem lead_unique {S : State} {V : Fin 3 → NodeView} {net : List Msg} {G : RaftFacts} {n k : Fin 3}
    (hs : AntSim S V net) (hgo : GlobalOk S net G) (hl : RaftLaws G)
    (hk : S.role[k.val]! = leader)
    (hn : S.leaders.contains { server := nameOf (nodeId n), term := S.currentTerm[k.val]! } = true) :
    k = n := by
  obtain ⟨-, -, -, hno⟩ := hs
  have hvk : (V k).ps.role = .leader :=
    (roleOf_leader_iff _).mp (by rw [← (hno k).1.2.2.2.2.1]; exact hk)
  have hkm := List.contains_iff_mem.mp ((hno k).2.1 hvk).1
  have hnm := List.contains_iff_mem.mp hn
  obtain ⟨a, ta, ha, hsa, hta⟩ := hgo.1 _ hnm
  obtain ⟨b, tb, hb, hsb, htb⟩ := hgo.1 _ hkm
  have hct : S.currentTerm[k.val]! = uint.Z (V k).ps.term := (hno k).1.1
  have hta' : S.currentTerm[k.val]! = uint.Z ta := hta
  have htb' : uint.Z (V k).ps.term = uint.Z tb := htb
  have htt : ta = tb := uint_Z_inj.mp (by omega)
  have hab : a = b := hl.1 _ ha _ hb htt
  have hsa' : nameOf (nodeId n) = nameOf a := hsa
  have hsb' : nameOf (nodeId k) = nameOf b := hsb
  exact name_inj (by rw [hsb', hsa', hab])

set_option maxHeartbeats 4000000 in
/-- **`antSim_ready` for a leader's commit** (`ReadyKind.cmt`). -/
theorem ready_cmt (S : State) (V : Fin 3 → NodeView) (net : List Msg) (evs : List Event)
    (G : RaftFacts) (n : Fin 3) (ps₁ : PState) (rd : ReadyD)
    (hp : Prefix cfg3 evs S) (hs : AntSim S V net) (hl : RaftLaws G) (hgo : GlobalOk S net G)
    (hr : Reach (nodeId n) net (V n) ps₁) (hro : ReadyOutP (nodeId n) (V n) ps₁ rd)
    (hrep : Reported (V n) rd) (hrf : ReadyFacts G (nodeId n) ps₁)
    (hvl : (V n).ps.role = .leader) (hpl : ps₁.role = .leader) (hpt : ps₁.term = (V n).ps.term)
    (hpv : ps₁.vote = (V n).ps.vote) (hplog : ps₁.log = (V n).ps.log) (hents : rd.ents = [])
    (hlt : uint.Z (V n).ps.commit < uint.Z ps₁.commit) (hcm : CmtOk ps₁ ps₁.commit)
    (hns : NoSelf (nodeId n) ps₁) :
    ReadyGoal S V net evs G n ps₁ rd := by
  have hbE := reach_byE hr hro hrep
  obtain ⟨S1, hgc, hs1, hgo1⟩ := antSim_gc S V net G hs hl hgo
  have hs1' := hs1
  obtain ⟨hsh, hb, hnet, hno⟩ := hs1'
  have hc : S1.cfg = cfg3 := hsh.1
  have hrl : S1.role.length = 3 := hsh.2.2.2.2.2.2.1
  have hn3 : n.val < S1.role.length := by rw [hrl]; exact n.isLt
  obtain ⟨hd, hLP, -, -, -, -, -, -, hvsN⟩ := hno n
  obtain ⟨d1, d2, d3, d4, d5, -, -, -, -, -, -, -, -⟩ := hd
  have hq0 : S1.queue[n.val]! = [] := (hb.2.1 n).1
  obtain ⟨lp1, lp2, lp3, lp4, lp5⟩ := hLP hvl
  have hMO : MatchOk S1 n ps₁ :=
    (quiet_reach hc hnet (hno n) hr (hpl.trans hvl.symm) hpt hplog).2.2.1 hpl ⟨lp3, lp4⟩
  obtain ⟨-, -, -, -, -, -, -, -, hpre, hlen, hbase, hidx, -⟩ := id hro
  have hT : S1.currentTerm[n.val]! = uint.Z ps₁.term := by rw [d1, hpt]
  have hlogn : S1.log[n.val]! = logOf ps₁.log := by rw [d3, hplog]
  have hrole : S1.role[n.val]! = leader := by rw [d5, hvl]; rfl
  have hll : S1.ledLog.get (uint.Z ps₁.term) = .ok (logOf ps₁.log) := by rw [hpt, hplog]; exact lp2
  have hlc : S1.ledConf.get (uint.Z ps₁.term) = .ok cfg3.initConf :=
    hb.ledConfOk _ (TermFn.has_of_get hll)
  have hcL0 := nat_commit_le hrf
  have hcL : uint.Z ps₁.commit ≤ (logOf ps₁.log).length := by rw [logOf_length]; exact hcL0
  have hc0 : 0 < uint.Z ps₁.commit := by have := uint_Z_nonneg (V n).ps.commit; omega
  have hcmi : S1.commitIndex[n.val]! < uint.Z ps₁.commit := by rw [d4]; exact hlt
  have hk : tlOld S1.termLen (uint.Z ps₁.term) < uint.Z ps₁.commit := by
    have := (hb.termLenOk.2 n hrole).2; rw [hT] at this; omega
  have hplT : plogTermAt base0 ps₁.log ps₁.commit = some ps₁.term := by rw [← hbase]; exact hcm.2.1
  have hterm : termAt (logOf ps₁.log) (uint.Z ps₁.commit) = uint.Z ps₁.term := (termAt_of_plog hplT).2
  have hq : isQuorum (S1.acked n.val (uint.Z ps₁.term) (uint.Z ps₁.commit)) cfg3.initConf = true :=
    jq_isQuorum hcm.2.2 fun j hj => by
      obtain ⟨y, hy, hle⟩ := mem_ackedBy.mp hj
      have hmo : matchOf ps₁ (nodeId j) = y := by unfold matchOf; rw [hy]; rfl
      exact acked_of hc (hMO.1 j ps₁.commit (by rw [hmo]; exact hle) hplT)
  have hcG := hrf.2.2.1
  have hm' := inMemory_lcommit n hc (V n).byE hbE ps₁.term ps₁.vote ps₁.commit (logOf ps₁.log)
    cfg3.initConf hrole hT hll hlc hcL hc0 hk hterm hq (cs_ok hgo1.2.2.2.2.1 hcG)
    (lc_ok hl hgo1.2.2.2.1 hrf.2.2.2.1 hcG)
  -- the new `chain` and `termLen`
  have himax : imax (tlOld S1.termLen (uint.Z ps₁.term)) (uint.Z ps₁.commit) = uint.Z ps₁.commit := by
    unfold imax; split <;> omega
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := commit_fields (n := n) (T := ps₁.term) hb hgo1 hcL0 hcG
    hrf.2.1 hrf.2.2.2.1 hcmi
  simp only [hcmi, true_and, himax] at f1 f2 f3 f4 f5 f6 f7
  generalize hch : (if (S1.chain.length : Int) < uint.Z ps₁.commit then
    (logOf ps₁.log).take (uint.Z ps₁.commit).toNat else S1.chain) = ch at f1 f2 f3 f4 f5 f6 f7 hm'
  generalize htl : S1.termLen.with (uint.Z ps₁.term) (uint.Z ps₁.commit) = tl at f1 f2 f3 f4 f5 f6 f7 hm'
  have hsend : sendableIn S1.leaders S1.ledLog ch tl (AppendFact.mk (nameOf (nodeId n))
      (nameOf (nodeId n)) (uint.Z ps₁.term) 0 0 [] (uint.Z ps₁.commit)) = .ok true := by
    have h := sendable_leader (S := { S1 with chain := ch, termLen := tl }) (src := nameOf (nodeId n))
      (dst := nameOf (nodeId n)) (lg := ps₁.log) (T := uint.Z ps₁.term) (p := 0) (pt := 0) (es := [])
      (c := uint.nat ps₁.commit) (by rw [hpt]; exact lp1) hll (by unfold termAt; simp) (Nat.zero_le _) rfl
      (.inr ⟨by word, by have := f2.1; word,
        by obtain ⟨q, hq, h1, h2⟩ := f4.resolve_left (by omega); exact ⟨q, hq, h1, by word⟩,
        by have := f2.2; rw [uZ_toNat_nat] at this; exact this⟩)
    have e : ((uint.nat ps₁.commit : Nat) : Int) = uint.Z ps₁.commit := by word
    rw [e] at h; exact h
  obtain ⟨p, hpm, hod⟩ := onDisk_lcommit n hc (V n).byE ps₁.term ps₁.vote ps₁.commit
    (if (V n).byE = go!"recv" then S1.pending[n.val]! else []) (S1.role.set n.val leader) S1.leaders
    S1.ledLog ch tl S1.viol hT.symm (by rw [d2, hpv]) (get!_set_self _ hn3) hsend hcmi
    (by rw [hlogn]; exact hcL) ⟨by rw [lp5.1, hpt], by have := lp5.2; rw [← hplog] at this; omega⟩
    (by rw [hlogn]; exact cs_ok f6 hcG) (by rw [hlogn]; exact lc_ok hl hgo1.2.2.2.1 hrf.2.2.2.1 hcG)
    (by rw [hlogn]; exact ch_ok f6 hcG)
  have hchl : ¬ (S1.commitIndex[n.val]! < uint.Z ps₁.commit ∧ (ch.length : Int) < uint.Z ps₁.commit) :=
    fun h => by have := f2.1; omega
  have htl2 : tl.with (uint.Z ps₁.term) (imax (tlOld tl (uint.Z ps₁.term)) (uint.Z ps₁.commit)) = tl := by
    rw [← htl, tlOld_with, if_pos rfl, with_with]
    unfold imax; simp
  rw [if_neg hchl, htl2] at hod
  unfold ReadyGoal
  rw [hpl, hents]
  have hcf : (S1.confirmed.set n.val (S1.confirmed[n.val]!))[n.val]! = S1.confirmed[n.val]! :=
    get!_set_self _ (by rw [hsh.2.2.2.2.2.2.2.2.2.2.1]; exact n.isLt)
  refine ready_finish hp hgc hs1 hgo1 hl
    (ready_of hq0 hm' rfl (queued_ready _ _ _ _ _ _ _ _ _) hod) ?_
  exact {
    hterm := rfl
    tge := Int.le_of_eq hT
    hvote := .inl ⟨hT.symm, by show S1.vote n.val = nameOf ps₁.vote; rw [d2, hpv]⟩
    hlog := hlogn
    hcommit := rfl
    cge := Int.le_of_lt hcmi
    hrole := by rw [get!_set_self _ hn3]; show leader = roleOf ps₁.role; rw [hpl]; rfl
    rlen := by rw [List.length_set, hrl]
    rother := fun k hk => get!_set_ne _ _ (fun h => hk (Fin.ext h))
    rstay := fun _ _ => get!_set_self _ hn3
    hdel := rfl
    wf := ⟨rfl, hbase, hidx, hpre, hlen⟩
    hmem := ⟨rfl, rfl⟩
    hviol := hb.1
    made := hpm
    msub := fun f hf => hf
    mnew := fun f hf hn => absurd hf hn
    vsub := fun y hy => hy
    vnew := fun y hy hn => absurd hy hn
    vin := fun h => absurd rfl h
    lsub := fun l hl => hl
    lnew := fun l hl hn => absurd hl hn
    glead := fun _ => (hrf.2.2.2.2.1 hpl).1
    hll := .inl rfl
    hchain := f1
    chainC := by rw [hlogn]; exact f2
    tlLen := f3
    tlC := f4
    tlDom := f5
    chainG := f6
    tlG := f7
    logG := hrf.1
    cmono := .inl rfl
    hconf := fun l hl => hb.2.2.2.2.2.2.1 n l hl
    lpart := fun _ => ⟨by
        show S1.leaders.contains { server := nameOf (nodeId n), term := uint.Z ps₁.term } = true
        rw [hpt]; exact lp1,
      by show S1.ledLog.get (uint.Z ps₁.term) = .ok (logOf ps₁.log); exact hll,
      hMO.1, hMO.2,
      by show (S1.confirmed.set n.val (S1.confirmed[n.val]!))[n.val]!.term = uint.Z ps₁.term ∧
          (ps₁.log.length : Int) ≤ (S1.confirmed.set n.val (S1.confirmed[n.val]!))[n.val]!.index
         rw [hcf, lp5.1, hpt, hplog]; exact ⟨rfl, lp5.2⟩⟩
    cpart := fun h => absurd (h.symm.trans hpl) (by decide)
    hpend := pendOk_of_reach hnet (hno n) hr hro
    hqs := fun q hq => by
      have hq' := (hro.2.2.2.2.2.2.1.mem_iff).mp hq
      rw [List.mem_filter] at hq'
      exact (hns q hq'.1 (of_decide_eq_true hq'.2)).elim
    drain := ⟨rfl, rfl⟩
    hlead := ⟨fun h => absurd hpl h, (reach_leadOk hnet (hno n) hr).2⟩
    hvself := fun _ => by show ps₁.vote = nodeId n; rw [hpv]; exact hvsN (by rw [hvl]; decide)
    rnf := fun _ _ => by rw [hrole]; decide
    tlMono := fun T' => by
      rw [← htl, tlOld_with]
      by_cases h : T' = uint.Z ps₁.term
      · rw [if_pos h, h]; omega
      · rw [if_neg h]; exact Int.le_refl _
    tlNew := fun T' h => by
      rw [← htl, tlOld_with] at h
      have hT' : T' = uint.Z ps₁.term := by
        by_cases e : T' = uint.Z ps₁.term
        · exact e
        · rw [if_neg e] at h; omega
      have lp1' : S1.leaders.contains { server := nameOf (nodeId n), term := uint.Z ps₁.term } = true := by
        rw [hpt]; exact lp1
      refine ⟨hT', ⟨_, List.contains_iff_mem.mp lp1', rfl⟩, fun k hkn hkl hkt => ?_⟩
      exact absurd (lead_unique hs1 hgo1 hl hkl (by rw [hkt, hpt]; exact lp1)) hkn
    tlSelf := fun _ => ⟨fun _ => by rw [← htl, tlOld_with, if_pos rfl]; exact Int.le_refl _, by
      rw [← htl, tlOld_with, if_pos rfl]; exact Int.le_refl _⟩
    lconf := fun T' h => hb.ledConfOk T' h
    tlSort := by rw [← htl]; exact with_sorted _ _ hb.tlSorted }

end cmt

end AntSim
end EtcdGrove
end Perennial
