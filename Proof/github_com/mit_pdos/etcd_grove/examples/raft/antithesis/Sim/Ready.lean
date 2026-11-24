/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: `antSim_ready` (#33 S4, the invariant phase)

A reported `Ready` (`notes/antithesis-rawnode-design.md` §3.3, "`antSim_ready`, guard by guard"):
`antSim_gc` to `S1`; the `Ready`'s kind (`ready_kind`); per kind, `InMemory` and `OnDisk` of its
`ready` report evaluated (`ReadyEval`, `ReadyLeader`, `ReadyOD`, `ReadyOD2`) to `readyS`, its side
conditions `ReadyOk` (`ReadyRel.lean`), then `ready_rel` and `Prefix.snoc`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.ReadyRel
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.ReadyKind
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.ReadyLeader
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.ReadySafe
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Quiet
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.GC
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Send

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open AntCheck go_etcd_io.raft.v3

section ready
variable [GooseExts]

/-! ## From `Ready`'s result to the next prefix -/

/-- `Step` of a `ready` report whose `Ready` is `rdS (odS …) r`: `readyS`. -/
theorem ready_step {S : State} {n : Fin 3} (hc : S.cfg = cfg3) {b : Str} {rr : Role} {t v c : w64}
    {es : List EntryM} {t1 : Int} {vo : Option Str} {L1 : List Entry} {c1 : Int} {ro : List Str}
    {cf : Confirmed} {M : List Fact} {Vs : List VoteRec} {ld : List LeaderRec}
    {ll : TermFn (List Entry)} {p : Pre} {ch : List Entry} {tl : TermFn Int} {vi : SSet}
    {r : MemResult}
    (h : S.ready n.val (evReady (nodeId n) b rr t v c es) =
      .ok (some (rdS (odS S n.val t1 vo L1 c1 ro cf M Vs ld ll p ch tl vi) r))) :
    S.step (evReady (nodeId n) b rr t v c es) =
      .ok (some (readyS S n.val t1 vo L1 c1 ro cf M Vs ld ll p ch tl vi r)) := by
  rw [step_evReady n hc, h]; rfl

/-- **The last step of each kind**: `Ready` evaluated at `S1` (after `GC`) to `rdS (odS …) r`, its
side conditions met: the next prefix, the relation and `GlobalOk` at the new state. -/
theorem ready_finish {S S1 : State} {V : Fin 3 → NodeView} {net : List Msg} {evs : List Event}
    {G : RaftFacts} {n : Fin 3} {w : NodeView} {b : Str} {rr : Role} {t v c : w64}
    {es : List EntryM} {t1 : Int} {vo : Option Str} {L1 : List Entry} {c1 : Int} {ro : List Str}
    {cf : Confirmed} {M : List Fact} {Vs : List VoteRec} {ld : List LeaderRec}
    {ll : TermFn (List Entry)} {p : Pre} {ch : List Entry} {tl : TermFn Int} {vi : SSet}
    {r : MemResult}
    (hp : Prefix cfg3 evs S) (hgc : gcLoop (gcFuel S) S = .ok (S1, none))
    (hs1 : AntSim S1 V net) (hgo1 : GlobalOk S1 net G) (hl : RaftLaws G)
    (h : S1.ready n.val (evReady (nodeId n) b rr t v c es) =
      .ok (some (rdS (odS S1 n.val t1 vo L1 c1 ro cf M Vs ld ll p ch tl vi) r)))
    (hok : ReadyOk S1 V net G n w t1 vo L1 c1 ro cf M Vs ld ll p ch tl vi r) :
    ∃ S', Prefix cfg3 (evs ++ [evReady (nodeId n) b rr t v c es]) S' ∧
      AntSim S' (setV V n w) net ∧ GlobalOk S' net G := by
  obtain ⟨h1, h2, h3⟩ := ready_rel hs1 hgo1 hl hok
  exact ⟨_, Prefix.snoc hp hgc (ready_step hs1.1.1 h) h3, h1, h2⟩

/-! ## The drain's `by` -/

theorem reach_byE {id : w64} {net : List Msg} {v : NodeView} {ps₁ : PState} {rd : ReadyD}
    (hr : Reach id net v ps₁) (hro : ReadyOutP id v ps₁ rd) (hrep : Reported v rd) :
    v.byE = go!"recv" ∨ v.byE = go!"tick" ∨ v.byE = go!"propose" ∨ v.byE = go!"boot" := by
  cases hr with
  | stay _ => exact absurd hrep (stay_quiet hro)
  | input inp _ _ hbe _ _ _ =>
    cases inp with
    | recv m => exact .inl hbe
    | tick => exact .inr (.inl hbe)
    | propose d => exact .inr (.inr (.inl hbe))
  | advance _ _ _ hb _ =>
    rcases hb with h | h | h | h
    · exact .inr (.inr (.inr h))
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))

theorem roleOf_leader_iff (r : Role) : roleOf r = leader ↔ r = .leader := by
  cases r <;> decide

/-! ## Kinds that write no entry and move no commit -/

/-- **`ReadyOk` of a `Ready` that changes only the term, the vote or the role** of a non-leader
(`camp`, `grant`, `adopt`, `demote`): `InMemory`'s `memNL`, `OnDisk`'s log, commit, confirmation,
leaders, leader logs, `chain`, `termLen` as they were; the facts `M` and votes `Vs` only the
campaign's vote request and the node's own vote. -/
theorem readyOk_plain {S : State} {V : Fin 3 → NodeView} {net : List Msg} {G : RaftFacts}
    {n : Fin 3} {ps₁ : PState} {rd : ReadyD} {vo : Option Str} {M : List Fact} {Vs : List VoteRec}
    {p : Pre}
    (hs : AntSim S V net) (hgo : GlobalOk S net G) (hrf : ReadyFacts G (nodeId n) ps₁)
    (hr : Reach (nodeId n) net (V n) ps₁) (hro : ReadyOutP (nodeId n) (V n) ps₁ rd)
    (hnl : ps₁.role ≠ .leader) (hlog : ps₁.log = (V n).ps.log) (hcm : ps₁.commit = (V n).ps.commit)
    (htge : uint.Z (V n).ps.term ≤ uint.Z ps₁.term)
    (hvl : (V n).ps.role = .leader → (V n).ps.term ≠ ps₁.term)
    (hvote : match vo with
      | some x => x = nameOf ps₁.vote ∧ 0 < uint.Z ps₁.term
      | none => (ps₁.term = (V n).ps.term ∧ ps₁.vote = (V n).ps.vote) ∨
          (uint.Z (V n).ps.term < uint.Z ps₁.term ∧ ps₁.vote = W64 0))
    (hmsub : ∀ f ∈ S.msgs, f ∈ M) (hmnew : ∀ f ∈ M, f ∉ S.msgs → f.type = go!"vote")
    (hvsub : ∀ y ∈ S.votes, y ∈ Vs)
    (hvnew : ∀ y ∈ Vs, y ∉ S.votes →
      y = { voter := nameOf (nodeId n), term := uint.Z ps₁.term, cand := nameOf ps₁.vote } ∧
        ps₁.vote ≠ W64 0)
    (hvin : vo ≠ none →
      { voter := nameOf (nodeId n), term := uint.Z ps₁.term, cand := nameOf ps₁.vote } ∈ Vs)
    (hmade : p.made = false)
    (hcp : CandPart (readyS S n.val (uint.Z ps₁.term) vo (S.log[n.val]!) (uint.Z ps₁.commit)
      (S.role.set n.val (roleOf ps₁.role)) (S.confirmed[n.val]!) M Vs S.leaders S.ledLog p S.chain
      S.termLen S.viol (memNL S n.val (roleOf ps₁.role))) n ((V n).afterReady ps₁ rd))
    (hqs : ∀ q ∈ rd.qs, QsOk (readyS S n.val (uint.Z ps₁.term) vo (S.log[n.val]!) (uint.Z ps₁.commit)
      (S.role.set n.val (roleOf ps₁.role)) (S.confirmed[n.val]!) M Vs S.leaders S.ledLog p S.chain
      S.termLen S.viol (memNL S n.val (roleOf ps₁.role))) n ((V n).afterReady ps₁ rd) q)
    (hlh : LeadHint (nodeId n) ps₁) (hvsp : ps₁.role ≠ .follower → ps₁.vote = nodeId n) :
    ReadyOk S V net G n ((V n).afterReady ps₁ rd) (uint.Z ps₁.term) vo (S.log[n.val]!)
      (uint.Z ps₁.commit) (S.role.set n.val (roleOf ps₁.role)) (S.confirmed[n.val]!) M Vs
      S.leaders S.ledLog p S.chain S.termLen S.viol (memNL S n.val (roleOf ps₁.role)) := by
  obtain ⟨hsh, hb, hnet, hno⟩ := hs
  obtain ⟨hd, -, -, -, -, -, -, -⟩ := hno n
  obtain ⟨d1, d2, d3, d4, d5, -, -, -, -, -, -, -, -⟩ := hd
  obtain ⟨hb1, -, -, hb4, hb5, hb6, hb7, -⟩ := hb
  have hrl : S.role.length = 3 := hsh.2.2.2.2.2.2.1
  have hn3 : n.val < S.role.length := by rw [hrl]; exact n.isLt
  obtain ⟨-, -, -, -, -, -, -, -, hpre, hlen, hbase, hidx, -⟩ := id hro
  have hcmZ : S.commitIndex[n.val]! = uint.Z ps₁.commit := by rw [d4, hcm]
  exact {
    hterm := rfl
    tge := by rw [d1]; exact htge
    hvote := by
      cases vo with
      | some x => exact hvote
      | none =>
        rcases hvote with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact .inl ⟨by rw [d1, h1], by rw [d2]; show _ = nameOf ps₁.vote; rw [h2]⟩
        · exact .inr ⟨by rw [d1]; exact h1, h2⟩
    hlog := by rw [d3]; show logOf (V n).ps.log = logOf ps₁.log; rw [hlog]
    hcommit := rfl
    cge := Int.le_of_eq hcmZ
    hrole := get!_set_self _ hn3
    rlen := by rw [List.length_set, hrl]
    rother := fun k hk => get!_set_ne _ _ (fun h => hk (Fin.ext h))
    rstay := by
      intro hl ht
      rw [d5, roleOf_leader_iff] at hl
      exact absurd (uint_Z_inj.mp (by rw [← d1, ← ht])).symm (hvl hl)
    hdel := rfl
    wf := ⟨rfl, hbase, hidx, hpre, hlen⟩
    hmem := ⟨rfl, rfl⟩
    hviol := hb1
    made := hmade
    msub := hmsub
    mnew := fun f hf hn => .inl (hmnew f hf hn)
    vsub := hvsub
    vnew := fun y hy hn => ⟨(hvnew y hy hn).1, hrf.2.2.2.2.2 (hvnew y hy hn).2⟩
    vin := hvin
    lsub := fun l hl => hl
    lnew := fun l hl hn => absurd hl hn
    glead := by
      intro h
      rw [get!_set_self _ hn3, roleOf_leader_iff] at h
      exact absurd h hnl
    hll := .inl rfl
    hchain := List.prefix_refl _
    chainC := by
      obtain ⟨e1, e2⟩ := hb5 n
      rw [hcmZ] at e1 e2
      exact ⟨e1, e2⟩
    tlLen := hb4
    tlC := by
      rcases hb6 n with h | ⟨q, hq, h1, h2⟩
      · exact .inl (hcmZ ▸ h)
      · exact .inr ⟨q, hq, by rw [d1] at h1; exact Int.le_trans h1 htge, hcmZ ▸ h2⟩
    tlDom := fun q hq => ⟨q, hq, rfl, Int.le_refl _⟩
    chainG := hgo.2.2.2.2.1
    tlG := hgo.2.2.2.2.2.1
    logG := hrf.1
    cmono := .inl rfl
    hconf := by
      intro l hl
      exact hb7 n l hl
    lpart := fun h => absurd h hnl
    cpart := hcp
    hpend := pendOk_of_reach hnet (hno n) hr hro
    hqs := hqs
    drain := ⟨rfl, rfl⟩
    hlead := hlh
    hvself := hvsp }

/-! ## Facts of the kinds -/

/-- A campaign's tally is empty (`pbecomeCandidate`): the campaign is `TickEnd`'s (an `Advance`
keeps the term, a leader's tick its role). -/
theorem camp_votes {id : w64} {net : List Msg} {v : NodeView} {ps₁ : PState}
    (hr : Reach id net v ps₁) (hX : v.ps.outbox = []) (hqs : ∀ q ∈ v.qs, SelfMsg id v.ps.term q)
    (hbe : v.byE = go!"tick") (ht : ps₁.term = v.ps.term + W64 1) (hc : ps₁.role = .candidate) :
    ps₁.votes = ∅ := by
  cases hr with
  | stay _ => exact absurd ht.symm (w64_succ_ne _)
  | input inp _ _ hbe' _ _ hs =>
    cases inp with
    | recv m => rw [hbe] at hbe'; exact absurd hbe' (by simp [Input.byE])
    | propose d => rw [hbe] at hbe'; exact absurd hbe' (by simp [Input.byE])
    | tick =>
      rcases hs with rfl | ⟨-, -, peers, cl, -, rfl⟩ | ⟨hl, ms, -, rfl⟩
      · exact absurd ht.symm (w64_succ_ne _)
      · rfl
      · rw [psendMsgs_role, hl] at hc; cases hc
  | advance _ _ _ _ ha =>
    have hinv : AdvInv id v.ps.term v.ps.commit ps₁ :=
      adv_run ha hqs (advInv_nil rfl (Int.le_refl _) hX)
    rw [hinv.1] at ht
    exact absurd ht.symm (w64_succ_ne _)

/-- A follower's `Ready` queues no self-addressed message. -/
theorem qs_follower {id : w64} {v : NodeView} {ps : PState} {rd : ReadyD}
    (hro : ReadyOutP id v ps rd) (hso : SelfOut id ps) (hf : ps.role = .follower) :
    ∀ q ∈ rd.qs, False := by
  intro q hq
  rcases (qs_self hro hso q hq).2 with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [hf] at h <;> cases h

/-- `UpToDate` of a vote request against the node's log is raft's `plogUpToDate`. -/
theorem upToDate_of {S : State} {n : Fin 3} {l : List EntryM} {m : Msg}
    (hlog : S.log[n.val]! = logOf l) (hidx : LogIdx l)
    (h : plogUpToDate base0 l (entryID.mk m.logterm m.index) = true) :
    S.upToDate (vfOf m) n.val = true := by
  obtain ⟨hi, hterm⟩ := plogLast_idx hidx
  unfold plogUpToDate at h
  unfold State.upToDate State.lastTerm
  rw [hlog, logOf_length]
  simp only [decide_eq_true_eq] at h
  simp only [vfOf, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq]
  rcases h with h | ⟨h1, h2⟩
  · left; rw [← hterm]; exact decide_eq_true h
  · right; exact ⟨by rw [← hterm]; exact congrArg _ h1, by rw [← hi]; exact decide_eq_true h2⟩

/-- The `ready` report's `m` for a drain caused by a `recv` (`pending[n]`, B 201). -/
theorem pending_of {S : State} {net : List Msg} {n : Fin 3} {v : NodeView} {m : Msg}
    (hv : NodeOk S net n v) (ht : v.told = true) (hca : v.cause = some m) :
    S.pending[n.val]! = [msgOf m (nodeId n)] := by
  obtain ⟨m', h1, h2⟩ := hv.2.2.2.2.2.1 ht
  rw [hca] at h1; cases h1; exact h2

theorem queued_recv (S : State) (n : Fin 3) (r : Role) (t v c : w64) (es : List EntryM) (m : Msg)
    (hp : S.pending[n.val]! = [msgOf m (nodeId n)]) :
    S.queued n.val (evReady (nodeId n) go!"recv" r t v c es) =
      .ok { ev := evReady (nodeId n) go!"recv" r t v c es, m := [msgOf m (nodeId n)] } := by
  rw [queued_ready, if_pos rfl, hp]

theorem queued_other (S : State) (n : Fin 3) (b : Str) (r : Role) (t v c : w64) (es : List EntryM)
    (hb : b ≠ go!"recv") :
    S.queued n.val (evReady (nodeId n) b r t v c es) =
      .ok { ev := evReady (nodeId n) b r t v c es, m := [] } := by
  rw [queued_ready, if_neg hb]

/-! ## A commit's `chain` and `termLen` -/

theorem rd_with_mem {α : Type} {f : TermFn α} {t : Int} {v : α} {q : Int × α} (h : q ∈ f.with t v) :
    q ∈ f ∨ q = (t, v) := by
  induction f with
  | nil => simp [TermFn.with] at h; exact .inr h
  | cons p ps ih =>
    unfold TermFn.with at h
    split at h
    · rcases List.mem_cons.mp h with h | h
      · exact .inr h
      · split at h
        · exact .inl (List.mem_cons_of_mem _ h)
        · exact .inl h
    · rcases List.mem_cons.mp h with h | h
      · exact .inl (h ▸ List.mem_cons_self ..)
      · rcases ih h with h | h
        · exact .inl (List.mem_cons_of_mem _ h)
        · exact .inr h

theorem rd_with_self {α : Type} (f : TermFn α) (t : Int) (v : α) : (t, v) ∈ f.with t v := by
  induction f with
  | nil => simp [TermFn.with]
  | cons p ps ih =>
    unfold TermFn.with
    split
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ ih

theorem rd_with_dom (f : TermFn Int) (t v : Int) (hv : tlOld f t ≤ v) :
    ∀ q ∈ f, ∃ q' ∈ f.with t v, q'.1 = q.1 ∧ q.2 ≤ q'.2 := by
  induction f with
  | nil => intro q hq; cases hq
  | cons p ps ih =>
    intro q hq
    unfold TermFn.with
    split
    · rename_i hle
      by_cases hpt : p.1 = t
      · rw [if_pos hpt]
        rcases List.mem_cons.mp hq with rfl | hq
        · refine ⟨(t, v), List.mem_cons_self .., hpt.symm, ?_⟩
          have : tlOld (q :: ps) t = q.2 := by
            unfold tlOld; simp [hpt]
          rw [this] at hv; exact hv
        · exact ⟨q, List.mem_cons_of_mem _ hq, rfl, Int.le_refl _⟩
      · rw [if_neg hpt]
        exact ⟨q, List.mem_cons_of_mem _ hq, rfl, Int.le_refl _⟩
    · rename_i hlt
      have hpt : p.1 ≠ t := by omega
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨q, List.mem_cons_self .., rfl, Int.le_refl _⟩
      · have hold : tlOld (p :: ps) t = tlOld ps t := by
          unfold tlOld; simp [hpt]
        rw [hold] at hv
        obtain ⟨q', hq', h1, h2⟩ := ih hv q hq
        exact ⟨q', List.mem_cons_of_mem _ hq', h1, h2⟩

theorem tlOld_cases (tl : TermFn Int) (t : Int) :
    tlOld tl t = 0 ∨ ∃ q ∈ tl, q.1 = t ∧ q.2 = tlOld tl t := by
  unfold tlOld
  cases h : tl.find? (fun p => p.1 == t) with
  | none => exact .inl rfl
  | some q =>
    have hm := List.mem_of_find?_eq_some h
    have hq := List.find?_some h
    exact .inr ⟨q, hm, by simpa using hq, rfl⟩

theorem logOf_take_len (l : List EntryM) (k : Nat) : (logOf (l.take k)).length = min k l.length := by
  rw [logOf_length, List.length_take]

/-- **A commit to `cc` at term `T`** (`OnDisk`'s `ch1` and `termLen` when the commit moves, B 422-423):
`chain` extended to the new committed prefix where it is longer, `termLen[T]` raised to it; what
`ReadyOk` needs of them, from `chain` and the new prefix both prefixes of the committed log (C5,
`ReadyFacts`). -/
theorem commit_fields {S : State} {net : List Msg} {G : RaftFacts} {n : Fin 3} {l : List EntryM}
    {cc T : w64} (hb : BindingOk S) (hgo : GlobalOk S net G)
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
  have hb4 := hb.2.2.2.1
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


/-! ## A follower's store or commit on a request -/

/-- **`ReadyOk` of a follower's `Ready` on a request** (`store`, `hb`): the term the request's (kept
or adopted, `FolTerm`), the vote kept or reset; the log `L1`, commit, confirmation `cf`, facts `M`
(the node's ack), `chain` and `termLen` as the kind's `OnDisk` gives them, with their fields. -/
theorem readyOk_fol {S : State} {V : Fin 3 → NodeView} {net : List Msg} {G : RaftFacts}
    {n : Fin 3} {ps₁ : PState} {rd : ReadyD} {m : Msg} {L1 : List Entry} {cf : Confirmed}
    {M : List Fact} {p : Pre} {ch : List Entry} {tl : TermFn Int}
    (hs : AntSim S V net) (hrf : ReadyFacts G (nodeId n) ps₁)
    (hr : Reach (nodeId n) net (V n) ps₁) (hro : ReadyOutP (nodeId n) (V n) ps₁ rd)
    (hpr : ps₁.role = .follower) (hft : FolTerm (V n).ps m ps₁) (hpt : ps₁.term = m.term)
    (hL1 : L1 = logOf ps₁.log) (hcge : uint.Z (V n).ps.commit ≤ uint.Z ps₁.commit)
    (hmsub : ∀ f ∈ S.msgs, f ∈ M)
    (hmnew : ∀ f ∈ M, f ∉ S.msgs → f.type = go!"ack" ∧ f.src = nameOf (nodeId n) ∧
      (∃ j : Fin 3, f.dst = nameOf (nodeId j)) ∧ f.term = uint.Z ps₁.term ∧
      ((cf.term = f.term ∧ f.index ≤ cf.index) ∨ f.index ≤ uint.Z ps₁.commit))
    (hmade : p.made = false)
    (hch : S.chain <+: ch) (hchC : uint.Z ps₁.commit ≤ ch.length ∧
      ch.take (uint.Z ps₁.commit).toNat = L1.take (uint.Z ps₁.commit).toNat)
    (htlL : ∀ q ∈ tl, q.2 ≤ ch.length)
    (htlC : uint.Z ps₁.commit = 0 ∨ ∃ q ∈ tl, q.1 ≤ uint.Z ps₁.term ∧ uint.Z ps₁.commit ≤ q.2)
    (htlD : ∀ q ∈ S.termLen, ∃ q' ∈ tl, q'.1 = q.1 ∧ q.2 ≤ q'.2)
    (hchG : ∃ c' ≤ G.committed.length, ch = logOf (G.committed.take c'))
    (htlG : ∀ q ∈ tl, 0 ≤ q.2 ∧ ∃ x, uint.Z x = q.1 ∧ (x, q.2.toNat) ∈ G.commits)
    (hcm : cf = S.confirmed[n.val]! ∨
      (cf.term = uint.Z ps₁.term ∧ S.ledLog.has (uint.Z ps₁.term) = true ∧
        ((S.confirmed[n.val]!).term = uint.Z ps₁.term → (S.confirmed[n.val]!).index ≤ cf.index)))
    (hconf : ∀ l, S.ledLog.get cf.term = .ok l →
      cf.index ≤ L1.length ∧ cf.index ≤ l.length ∧ L1.take cf.index.toNat = l.take cf.index.toNat)
    (hlh : LeadHint (nodeId n) ps₁) (hso : SelfOut (nodeId n) ps₁) :
    ReadyOk S V net G n ((V n).afterReady ps₁ rd) (uint.Z ps₁.term) none L1
      (uint.Z ps₁.commit) (S.role.set n.val (roleOf ps₁.role)) cf M S.votes
      S.leaders S.ledLog p ch tl S.viol (memNL S n.val (roleOf ps₁.role)) := by
  obtain ⟨hsh, hb, hnet, hno⟩ := hs
  obtain ⟨hd, -, -, -, -, -, -, -⟩ := hno n
  obtain ⟨d1, d2, d3, d4, d5, -, -, -, -, -, -, -, -⟩ := hd
  have hrl : S.role.length = 3 := hsh.2.2.2.2.2.2.1
  have hn3 : n.val < S.role.length := by rw [hrl]; exact n.isLt
  obtain ⟨-, -, -, -, -, -, -, -, hpre, hlen, hbase, hidx, -⟩ := id hro
  have hnl : ps₁.role ≠ .leader := by rw [hpr]; decide
  exact {
    hterm := rfl
    tge := by
      rw [d1]; rcases hft with ⟨h, -⟩ | ⟨h, -, -⟩
      · rw [hpt]; exact Int.le_of_lt h
      · rw [hpt, h]; exact Int.le_refl _
    hvote := by
      rcases hft with ⟨h1, h2⟩ | ⟨h1, -, h2⟩
      · exact .inr ⟨by rw [d1, hpt]; exact h1, h2⟩
      · exact .inl ⟨by rw [d1, hpt, h1], by rw [d2]; show _ = nameOf ps₁.vote; rw [h2]⟩
    hlog := hL1
    hcommit := rfl
    cge := by rw [d4]; exact hcge
    hrole := get!_set_self _ hn3
    rlen := by rw [List.length_set, hrl]
    rother := fun k hk => get!_set_ne _ _ (fun h => hk (Fin.ext h))
    rstay := by
      intro hl ht
      rw [d5, roleOf_leader_iff] at hl
      rcases hft with ⟨h, -⟩ | ⟨-, h, -⟩
      · rw [d1, hpt] at ht; rw [ht] at h; exact absurd h (Int.lt_irrefl _)
      · exact absurd hl h
    hdel := rfl
    wf := ⟨rfl, hbase, hidx, hpre, hlen⟩
    hmem := ⟨rfl, rfl⟩
    hviol := hb.1
    made := hmade
    msub := hmsub
    mnew := fun f hf hn => .inr (hmnew f hf hn)
    vsub := fun y hy => hy
    vnew := fun y hy hn => absurd hy hn
    vin := fun h => absurd rfl h
    lsub := fun l hl => hl
    lnew := fun l hl hn => absurd hl hn
    glead := by
      intro h
      rw [get!_set_self _ hn3, roleOf_leader_iff] at h
      exact absurd h hnl
    hll := .inl rfl
    hchain := hch
    chainC := hchC
    tlLen := htlL
    tlC := htlC
    tlDom := htlD
    chainG := hchG
    tlG := htlG
    logG := hrf.1
    cmono := hcm
    hconf := hconf
    lpart := fun h => absurd h hnl
    cpart := fun h => absurd (h.symm.trans hpr) (by decide)
    hpend := pendOk_of_reach hnet (hno n) hr hro
    hqs := fun q hq => (qs_follower hro hso hpr q hq).elim
    drain := ⟨rfl, rfl⟩
    hlead := hlh
    hvself := fun h => absurd hpr h }

theorem nat_commit_le {G : RaftFacts} {id : w64} {ps : PState} (hrf : ReadyFacts G id ps) :
    uint.Z ps.commit ≤ ps.log.length := by
  have h1 := hrf.2.1
  have h2 := congrArg List.length hrf.2.2.1
  rw [List.length_take, List.length_take] at h2
  have : uint.nat ps.commit ≤ ps.log.length := by omega
  word


/-! ## A request's guards from raft's log facts -/

theorem prev_of_match {S : State} {n : Fin 3} {l : List EntryM} {m : Msg}
    (hlog : S.log[n.val]! = logOf l) (h : PlogMatches base0 l (entryID.mk m.logterm m.index)) :
    (afOf m (nodeId n)).prevLogIndex = 0 ∨ ((afOf m (nodeId n)).prevLogIndex ≤ (S.log[n.val]!).length ∧
      ((S.log[n.val]!)[((afOf m (nodeId n)).prevLogIndex - 1).toNat]!).term =
        (afOf m (nodeId n)).prevLogTerm) := by
  unfold afOf; simp only
  rw [hlog]
  obtain ⟨p1, p2⟩ := termAt_of_plog (show plogTermAt base0 l m.index = some m.logterm from h)
  by_cases h0 : uint.Z m.index = 0
  · exact .inl h0
  · right
    have hm0 : 0 ≤ uint.Z m.index := by word
    rw [logOf_length]
    refine ⟨p1, ?_⟩
    rw [termAt_pos (by omega) (by rw [logOf_length]; exact p1)] at p2
    exact p2

theorem hf_of_match {S : State} {n : Fin 3} {l : List EntryM} {m : Msg}
    (hlog : S.log[n.val]! = logOf l) (hpay : AppPayloadOk m) {k : Nat} {e : EntryM}
    (he : m.entries[k]? = some e) (h : PlogMatches base0 l (entId e)) :
    HFAt S n.val (afOf m (nodeId n)) k := by
  have hidx := hpay.1 k e he
  obtain ⟨p1, p2⟩ := termAt_of_plog (show plogTermAt base0 l e.Index' = some e.Term' from h)
  have hm0 : 0 ≤ uint.Z m.index := by word
  have hw : uint.Z e.Index' = uint.Z m.index + ((k : Int) + 1) := by rw [hidx]; push_cast; rfl
  rw [hw] at p1 p2
  unfold HFAt afOf; simp only
  rw [hlog, logOf_length, logOf_getElem! he, entOf_term]
  refine ⟨p1, ?_⟩
  rw [termAt_pos (by omega) (by rw [logOf_length]; exact p1)] at p2
  exact p2

theorem hasFirst_of_match {S : State} {n : Fin 3} {l : List EntryM} {m : Msg}
    (hlog : S.log[n.val]! = logOf l) (hpay : AppPayloadOk m) (K : Nat) (hK : K ≤ m.entries.length)
    (h : ∀ (k : Nat) (e : EntryM), k < K → m.entries[k]? = some e → PlogMatches base0 l (entId e)) :
    S.hasFirst n.val (afOf m (nodeId n)) (K : Int) = .ok true := by
  have h0 : 0 ≤ (afOf m (nodeId n)).prevLogIndex := by unfold afOf; simp only; word
  rw [hasFirst_eq _ _ _ h0 K (by unfold afOf; simp only; rw [logOf_length]; exact hK)]
  congr 1
  refine decide_eq_true fun q hq => ?_
  have he : m.entries[q]? = some m.entries[q] := List.getElem?_eq_getElem (by omega)
  exact hf_of_match hlog hpay he (h q _ hq he)

theorem prevOk_of_match {S : State} {n : Fin 3} {l : List EntryM} {m : Msg}
    (hlog : S.log[n.val]! = logOf l) (h : PlogMatches base0 l (entryID.mk m.logterm m.index)) :
    S.prevOk n.val (afOf m (nodeId n)) = .ok true := by
  have h0 : 0 ≤ (afOf m (nodeId n)).prevLogIndex := by unfold afOf; simp only; word
  rw [prevOk_eq _ _ _ h0]
  exact congrArg _ (decide_eq_true (prev_of_match hlog h))


/-- Raft's `term(k)` of a follower's log after a store (`plogMaybeAppend`'s cut at `j` and append). -/
theorem plog_take_append {l ents : List EntryM} {j : Nat} (hj : j ≤ l.length) {k : w64}
    (hk1 : 1 ≤ uint.Z k) :
    plogTermAt base0 (l.take j ++ ents) k =
      if uint.Z k ≤ j then plogTermAt base0 l k
      else (fun e : EntryM => e.Term') <$> ents[(uint.Z k - j - 1).toNat]? := by
  have hb : uint.Z (base0 : go_etcd_io.raft.v3.entryID).index' = 0 := rfl
  unfold plogTermAt
  rw [hb, if_neg (by omega), if_neg (by omega)]
  split
  · rename_i hkj
    rw [if_neg (by omega), if_neg (by omega), List.getElem?_append_left (by rw [List.length_take]; omega),
      List.getElem?_take_of_lt (by omega)]
  · rename_i hkj
    rw [List.getElem?_append_right (by rw [List.length_take]; omega), List.length_take,
      Nat.min_eq_left hj]
    congr 2; omega


/-! ## `readyS`'s fields -/

section fields
variable (S : State) (n : Nat) (t1 : Int) (vo : Option Str) (L1 : List Entry) (c : Int)
  (ro : List Str) (cf : Confirmed) (M : List Fact) (Vs : List VoteRec) (ld : List LeaderRec)
  (ll : TermFn (List Entry)) (p : Pre) (ch : List Entry) (tl : TermFn Int) (vi : SSet) (r : MemResult)
theorem rS_ct : (readyS S n t1 vo L1 c ro cf M Vs ld ll p ch tl vi r).currentTerm = S.currentTerm.set n t1 := rfl
theorem rS_msgs : (readyS S n t1 vo L1 c ro cf M Vs ld ll p ch tl vi r).msgs = M := rfl
theorem rS_votes : (readyS S n t1 vo L1 c ro cf M Vs ld ll p ch tl vi r).votes = Vs := rfl
theorem rS_log : (readyS S n t1 vo L1 c ro cf M Vs ld ll p ch tl vi r).log = S.log.set n L1 := rfl
theorem rS_cfg : (readyS S n t1 vo L1 c ro cf M Vs ld ll p ch tl vi r).cfg = S.cfg := rfl
end fields

/-- What `antSim_ready` concludes, the `Ready`'s fields read off its state (`ReadyOutP`). -/
def ReadyGoal (S : State) (V : Fin 3 → NodeView) (net : List Msg) (evs : List Event) (G : RaftFacts)
    (n : Fin 3) (ps₁ : PState) (rd : ReadyD) : Prop :=
  ∃ S', Prefix cfg3 (evs ++ [evReady (nodeId n) (V n).byE ps₁.role ps₁.term ps₁.vote ps₁.commit rd.ents]) S' ∧
    AntSim S' (setV V n ((V n).afterReady ps₁ rd)) net ∧ GlobalOk S' net G

set_option maxHeartbeats 2000000 in
/-- **`antSim_ready`**, with the cases not proved here as premises. -/
theorem ready_main (S : State) (V : Fin 3 → NodeView) (net : List Msg) (evs : List Event)
    (G : RaftFacts) (n : Fin 3) (ps₁ : PState) (rd : ReadyD)
    (hp : Prefix cfg3 evs S) (hs : AntSim S V net) (hl : RaftLaws G) (hgo : GlobalOk S net G)
    (hr : Reach (nodeId n) net (V n) ps₁) (hro : ReadyOutP (nodeId n) (V n) ps₁ rd)
    (hrep : Reported (V n) rd) (htold : (V n).byE = go!"recv" → (V n).told = true)
    (hrf : ReadyFacts G (nodeId n) ps₁) (htb : uint.Z (V n).ps.term + 1 < 2 ^ 64)
    -- the cases not proved yet, as premises
    (hstoreB : ∀ m : Msg, RecvAt (nodeId n) net (V n) m → m.ty = .app → FolTerm (V n).ps m ps₁ →
      ps₁.term = m.term → ps₁.role = .follower → uint.Z (V n).ps.commit ≤ uint.Z m.index →
      PlogMatches base0 (V n).ps.log (entryID.mk m.logterm m.index) →
      (∃ (d : Nat) (e : EntryM), m.entries[d]? = some e ∧ rd.ents = m.entries.drop d ∧
        ¬ PlogMatches base0 (V n).ps.log (entId e) ∧
        (∀ (k : Nat) (e' : EntryM), k < d → m.entries[k]? = some e' →
          PlogMatches base0 (V n).ps.log (entId e')) ∧
        uint.Z e.Index' = uint.Z m.index + (d : Int) + 1 ∧
        uint.Z e.Index' ≤ ((V n).ps.log.length : Int) + 1 ∧
        ps₁.log = (V n).ps.log.take (uint.nat e.Index' - 1) ++ rd.ents) →
      (ps₁.commit = (V n).ps.commit ∨ (uint.Z (V n).ps.commit < uint.Z ps₁.commit ∧
        uint.Z ps₁.commit ≤ uint.Z m.commit ∧
        uint.Z ps₁.commit ≤ uint.Z m.index + (m.entries.length : Int))) →
      ReadyGoal S V net evs G n ps₁ rd)
    (hwin : ∀ (src : w64) (rej : Bool) (mt : GMap w64 w64), (V n).ps.role = .candidate →
      ((∃ m, RecvAt (nodeId n) net (V n) m ∧ m.ty = .voteResp ∧ m.term = (V n).ps.term ∧ m.src = src ∧
          m.reject = rej) ∨
        (src = nodeId n ∧ rej = false ∧ ∃ q ∈ (V n).qs, q.ty = .voteResp)) →
      JQuorum cfgM3 (granted (recordVote (V n).ps.votes src (!rej))) →
      LeaderMatchOk (nodeId n) (V n).ps mt →
      LeadC (nodeId n) (pwinState (nodeId n) { (V n).ps with votes := recordVote (V n).ps.votes src (!rej) } mt)
        ps₁ →
      rd.ents = [pleaderEntry (V n).ps] → ReadyGoal S V net evs G n ps₁ rd)
    (hprop : ∀ es : List EntryM, (V n).byE = go!"propose" → (V n).ps.role = .leader → es ≠ [] →
      rd.ents = es.mapIdx (stamp (V n).ps.term (plastIndex (V n).ps)) → ps₁.log = (V n).ps.log ++ rd.ents →
      ps₁.role = .leader → ps₁.term = (V n).ps.term → ps₁.vote = (V n).ps.vote →
      ps₁.commit = (V n).ps.commit → ReadyGoal S V net evs G n ps₁ rd)
    (hcmt : (V n).ps.role = .leader → ps₁.role = .leader → ps₁.term = (V n).ps.term →
      ps₁.vote = (V n).ps.vote → ps₁.log = (V n).ps.log → rd.ents = [] →
      uint.Z (V n).ps.commit < uint.Z ps₁.commit → CmtOk ps₁ ps₁.commit →
      ReadyGoal S V net evs G n ps₁ rd) :
    ∃ S', Prefix cfg3
        (evs ++ [evReady (nodeId n) (V n).byE rd.role rd.term rd.vote rd.commit rd.ents]) S' ∧
      AntSim S' (setV V n ((V n).afterReady ps₁ rd)) net ∧ GlobalOk S' net G := by
  obtain ⟨S1, hgc, hs1, hgo1⟩ := antSim_gc S V net G hs hl hgo
  have hs1' := hs1
  obtain ⟨hsh, hb, hnet, hno⟩ := hs1'
  have hc : S1.cfg = cfg3 := hsh.1
  have hrl : S1.role.length = 3 := hsh.2.2.2.2.2.2.1
  have hn3 : n.val < S1.role.length := by rw [hrl]; exact n.isLt
  have hct3 : n.val < S1.currentTerm.length := by rw [hsh.2.1]; exact n.isLt
  have hlg3 : n.val < S1.log.length := by rw [hsh.2.2.2.2.1]; exact n.isLt
  obtain ⟨hd, -, -, -, hQ, -, hca, hlo, hvs⟩ := hno n
  obtain ⟨d1, d2, d3, d4, d5, -, d7, d8, d9, d10, -, -, -⟩ := hd
  have hq0 : S1.queue[n.val]! = [] := (hb.2.1 n).1
  have hin : ∀ m ∈ net, InMsg m := fun m hm => ⟨(hnet.1 m hm).1, hnet.2.2 m hm⟩
  have hqs : ∀ q ∈ (V n).qs, SelfMsg (nodeId n) (V n).ps.term q := fun q hq => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hQ q hq
    exact ⟨h1, h2, h3, h4, h5.imp (fun h => h.1) (fun h => h.1)⟩
  have hso := selfOut_reach hr d7 hlo hin hqs
  have hlh := reach_leadOk hnet (hno n) hr
  have hbyE := reach_byE hr hro hrep
  have hk := ready_kind hr hro hrep d8 (nodeId_ne_zero n) hvs hin hqs
  have hvs1 := voteSelf_kind hk hvs
  obtain ⟨hR, hT, hVt, hC, -⟩ := id hro
  rw [hR, hT, hVt, hC]
  -- the sender of a received message: another node, at a term it has
  have hsender : ∀ m, RecvAt (nodeId n) net (V n) m → ∃ i : Fin 3, i ≠ n ∧ m.src = nodeId i ∧
      uint.Z m.term ≤ S1.currentTerm[i.val]! := by
    intro m hm
    obtain ⟨-, ⟨i, hi, hti⟩, -⟩ := hnet.1 m hm.2.2.1
    refine ⟨i, fun h => ?_, hi, hti⟩
    subst h
    exact (hnet.2.2 m hm.2.2.1).2.1 (by rw [hi, hm.2.2.2.1])
  cases hk with
  | demote hvc hpr hpt hpv hpl hpc hen =>
    rw [hen]
    have hnl : ps₁.role ≠ .leader := by rw [hpr]; decide
    have hm := inMemory_nl_eq n hc (V n).byE hbyE ps₁.role hnl ps₁.term ps₁.vote ps₁.commit [] d10
    obtain ⟨p, hpm, hod⟩ := onDisk_same n hc (V n).byE ps₁.role ps₁.term ps₁.vote ps₁.commit
      (if (V n).byE = go!"recv" then S1.pending[n.val]! else []) (S1.role.set n.val (roleOf ps₁.role))
      S1.leaders S1.ledLog S1.chain S1.termLen S1.viol hnl (by rw [hpt, d1]) (by rw [hpv, d2])
      (by rw [hpc, d4]) (get!_set_self _ hn3)
    refine ready_finish hp hgc hs1 hgo1 hl (ready_of hq0 hm rfl (queued_ready ..) hod) ?_
    exact readyOk_plain hs1 hgo1 hrf hr hro hnl hpl hpc (by rw [hpt]; exact Int.le_refl _)
      (fun h => by rw [hvc] at h; cases h) (.inl ⟨hpt, hpv⟩) (fun f hf => hf)
      (fun f hf hn => absurd hf hn) (fun y hy => hy) (fun y hy hn => absurd hy hn)
      (fun h => absurd rfl h) hpm (fun h => absurd (h.symm.trans hpr) (by decide))
      (fun q hq => (qs_follower hro hso hpr q hq).elim) hlh hvs1
  | camp hbe hnl0 hpt hpv hpr hpl hpc hen =>
    rw [hen, hbe, hpv]
    have htz : uint.Z ps₁.term = uint.Z (V n).ps.term + 1 := by
      rw [hpt]; have := htb; word
    have hnl : ps₁.role ≠ .leader := by rw [hpr]; decide
    have hvot := camp_votes hr d7 hqs hbe hpt hpr
    have hm := inMemory_nl_eq n hc go!"tick" (by decide) ps₁.role hnl ps₁.term (nodeId n) ps₁.commit [] d10
    rw [hpr] at hm
    obtain ⟨p, hpm, hod⟩ := onDisk_camp n hc ps₁.term ps₁.commit (S1.role.set n.val (roleOf .candidate))
      S1.leaders S1.ledLog S1.chain S1.termLen S1.viol (by rw [htz, d1]) (by rw [hpc, d4])
      (get!_set_self _ hn3)
    rw [hpr]
    have hok := readyOk_plain (vo := some (nameOf (nodeId n)))
      (M := lset.add S1.msgs (S1.voteRequest n.val (uint.Z ps₁.term)))
      (Vs := lset.add S1.votes { voter := nameOf (nodeId n), term := uint.Z ps₁.term, cand := nameOf (nodeId n) })
      hs1 hgo1 hrf hr hro hnl hpl hpc (by rw [htz]; omega) (fun h => absurd h hnl0)
      ⟨by rw [hpv], by rw [htz]; have := (V n).ps.term; word⟩
      (fun f hf => mem_lset_add.mpr (.inl hf))
      (fun f hf hn => by
        rcases mem_lset_add.mp hf with h | h
        · exact absurd h hn
        · rw [h]; rfl)
      (fun y hy => mem_lset_add.mpr (.inl hy))
      (fun y hy hn => by
        rcases mem_lset_add.mp hy with h | h
        · exact absurd h hn
        · rw [hpv]; exact ⟨h, nodeId_ne_zero n⟩)
      (fun _ => by rw [hpv]; exact mem_lset_add.mpr (.inr rfl)) hpm
      (fun _ => by
        refine ⟨fun j hj => ?_, ?_⟩
        · change ps₁.votes !! nodeId j = some true at hj
          rw [hvot, GMap.lookup_empty] at hj; cases hj
        · rw [rS_ct, get!_set_self _ hct3, rS_msgs]
          refine mem_lset_add.mpr (.inr ?_)
          unfold State.voteRequest State.lastTerm
          rw [rS_cfg, rS_log, get!_set_self _ hlg3])
      (fun q hq => by
        obtain ⟨⟨h1, h2, h3, h4, -⟩, hk⟩ := qs_self hro hso q hq
        rcases hk with ⟨h, -⟩ | ⟨-, rfl⟩
        · rw [hpr] at h; cases h
        · refine ⟨h1, h2, h3, h4, .inr ⟨rfl, ?_⟩⟩
          rw [rS_votes]; exact mem_lset_add.mpr (.inr rfl))
      hlh hvs1
    rw [hpr] at hok
    exact ready_finish hp hgc hs1 hgo1 hl
      (ready_of hq0 hm rfl (queued_other _ _ _ _ _ _ _ _ (by decide)) hod) hok
  | adopt m hm hlt hpt hpv hpr hpl hpc hen =>
    rw [hen, hm.1, hpv]
    have hnl : ps₁.role ≠ .leader := by rw [hpr]; decide
    have hpend := pending_of (hno n) (htold hm.1) hm.2.1
    obtain ⟨i, hin', hsi, hti⟩ := hsender m hm
    have hm' := inMemory_nl_eq n hc go!"recv" (by decide) ps₁.role hnl ps₁.term (W64 0) ps₁.commit [] d10
    rw [hpr] at hm'
    obtain ⟨p, hpm, hod⟩ := onDisk_adopt n hc ps₁.term ps₁.commit m (S1.role.set n.val (roleOf .follower))
      S1.leaders S1.ledLog S1.chain S1.termLen S1.viol hpt.symm (by rw [d1, hpt]; exact hlt)
      ⟨i, hin', by rw [hpt]; exact hti⟩ (by rw [hpc, d4]) (get!_set_self _ hn3)
    rw [hpr]
    have hok := readyOk_plain (vo := none) (M := S1.msgs) (Vs := S1.votes)
      hs1 hgo1 hrf hr hro hnl hpl hpc (by rw [hpt]; exact Int.le_of_lt hlt)
      (fun _ h => by rw [h, hpt] at hlt; exact absurd hlt (Int.lt_irrefl _))
      (.inr ⟨by rw [hpt]; exact hlt, hpv⟩) (fun f hf => hf)
      (fun f hf hn => absurd hf hn) (fun y hy => hy) (fun y hy hn => absurd hy hn)
      (fun h => absurd rfl h) hpm (fun h => absurd (h.symm.trans hpr) (by decide))
      (fun q hq => (qs_follower hro hso hpr q hq).elim) hlh hvs1
    rw [hpr] at hok
    exact ready_finish hp hgc hs1 hgo1 hl
      (ready_of hq0 hm' rfl (queued_recv _ _ _ _ _ _ _ _ hpend) hod) hok
  | grant m hm hty hTT hutd hpt hpv hpr hpl hpc hen =>
    rw [hen, hm.1, hpv]
    have hnl : ps₁.role ≠ .leader := by rw [hpr]; decide
    have hpend := pending_of (hno n) (htold hm.1) hm.2.1
    obtain ⟨i, hin', hsi, hti⟩ := hsender m hm
    have hle : S1.currentTerm[n.val]! ≤ uint.Z m.term := by
      rw [d1]; rcases hTT with h | ⟨h, -⟩
      · exact Int.le_of_lt h
      · rw [h]; exact Int.le_refl _
    have hvf : S1.msgs.contains (vfOf m) = true := by
      obtain ⟨-, -, j, hj, hjj⟩ := hnet.1 m hm.2.2.1
      have hjn : j = n := nodeId_inj (hj.symm.trans hm.2.2.2.1)
      subst hjn
      obtain ⟨f, hf, hfm⟩ := (hjj hle).2.1 hty
      rw [mo_voteFact] at hf; cases hf
      exact List.contains_iff_mem.mpr hfm
    have hm' := inMemory_nl_eq n hc go!"recv" (by decide) ps₁.role hnl ps₁.term m.src ps₁.commit [] d10
    rw [hpr] at hm'
    obtain ⟨p, hpm, hod⟩ := onDisk_grant n hc ps₁.term ps₁.commit m (S1.role.set n.val (roleOf .follower))
      S1.leaders S1.ledLog S1.chain S1.termLen S1.viol hty hpt.symm
      (by rw [hsi]; exact nameOf_ne_nil i)
      (by
        rcases hTT with h | ⟨h1, h2, -⟩
        · exact .inr ⟨by rw [d1, hpt]; exact h, i, hin', by rw [hpt]; exact hti⟩
        · refine .inl ⟨by rw [d1, hpt, h1], ?_⟩
          rw [d2, h2]; rfl)
      (by rw [hpc, d4]) (get!_set_self _ hn3) hvf (upToDate_of d3 d9 (d8 ▸ hutd))
    rw [hpr]
    have hok := readyOk_plain (vo := some (nameOf m.src)) (M := S1.msgs)
      (Vs := lset.add S1.votes { voter := nameOf (nodeId n), term := uint.Z ps₁.term, cand := nameOf m.src })
      hs1 hgo1 hrf hr hro hnl hpl hpc (by rw [hpt, ← d1]; exact hle)
      (fun hl0 h => by
        rcases hTT with h' | ⟨-, h2, -⟩
        · rw [h, hpt] at h'; exact absurd h' (Int.lt_irrefl _)
        · have := hvs (by rw [hl0]; decide); rw [h2] at this
          exact nodeId_ne_zero n this.symm)
      ⟨by rw [hpv], by
        rw [hpt]; have h0 := hm.2.2.2.2
        have : uint.Z m.term ≠ 0 := fun h => h0 (by word)
        have := m.term; word⟩
      (fun f hf => hf) (fun f hf hn => absurd hf hn)
      (fun y hy => mem_lset_add.mpr (.inl hy))
      (fun y hy hn => by
        rcases mem_lset_add.mp hy with h | h
        · exact absurd h hn
        · rw [hpv]; exact ⟨h, by rw [hsi]; exact nodeId_ne_zero i⟩)
      (fun _ => by rw [hpv]; exact mem_lset_add.mpr (.inr rfl)) hpm
      (fun h => absurd (h.symm.trans hpr) (by decide))
      (fun q hq => (qs_follower hro hso hpr q hq).elim) hlh hvs1
    rw [hpr] at hok
    exact ready_finish hp hgc hs1 hgo1 hl
      (ready_of hq0 hm' rfl (queued_recv _ _ _ _ _ _ _ _ hpend) hod) hok
  | hb m hm hty hft hpt hpr hpl hlt hpc hen =>
    rw [hen, hm.1]
    have hnl : ps₁.role ≠ .leader := by rw [hpr]; decide
    have hpend := pending_of (hno n) (htold hm.1) hm.2.1
    obtain ⟨i, hin', hsi, hti⟩ := hsender m hm
    have hle : S1.currentTerm[n.val]! ≤ uint.Z m.term := by
      rw [d1]; rcases hft with ⟨h, -⟩ | ⟨h, -, -⟩
      · exact Int.le_of_lt h
      · rw [h]; exact Int.le_refl _
    have hsd : S1.sendable (afOf m (nodeId n)) = .ok true := by
      obtain ⟨-, -, j, hj, hjj⟩ := hnet.1 m hm.2.2.1
      have hjn : j = n := nodeId_inj (hj.symm.trans hm.2.2.2.1)
      subst hjn
      have := (hjj hle).1 (.inr hty)
      rw [hj, mo_appendFact, eok_bind] at this; exact this
    have hlogn : S1.log[n.val]! = logOf ps₁.log := by rw [d3, hpl]
    have hcL := nat_commit_le hrf
    have hold : S1.commitIndex[n.val]! < uint.Z ps₁.commit := by rw [d4]; exact hlt
    have hcbc : (S1.confirmed[n.val]!).term = uint.Z ps₁.term ∧
        uint.Z ps₁.commit ≤ (S1.confirmed[n.val]!).index := by
      rcases hnet.2.1 m hm.2.2.1 hty n hm.2.2.2.1 hle with ⟨h1, h2⟩ | h
      · rw [hpt, hpc]; exact ⟨h1, h2⟩
      · rw [← hpc] at h; omega
    have hv : (nameOf ps₁.vote != (if uint.Z ps₁.term != S1.currentTerm[n.val]! then [] else S1.vote n.val))
        = false := by
      rcases hft with ⟨h1, h2⟩ | ⟨h1, -, h2⟩
      · have e : (uint.Z ps₁.term != S1.currentTerm[n.val]!) = true := by
          rw [bne_iff_ne, d1, hpt]; omega
        rw [e, if_pos rfl, h2, nameOf_zero]; rfl
      · have e : (uint.Z ps₁.term != S1.currentTerm[n.val]!) = false := by
          rw [d1, hpt, h1]; exact bne_self_eq_false _
        rw [e, if_neg (by simp), d2, h2]; exact bne_self_eq_false _
    have hm' := inMemory_nl_eq n hc go!"recv" (by decide) ps₁.role hnl ps₁.term ps₁.vote ps₁.commit [] d10
    rw [hpr] at hm'
    have hcG := hrf.2.2.1
    obtain ⟨p, hpm, hod⟩ := onDisk_fhb n hc ps₁.term ps₁.vote ps₁.commit m
      (S1.role.set n.val (roleOf .follower)) S1.leaders S1.ledLog S1.chain S1.termLen S1.viol hty hpt.symm
      (by rw [hpt]; exact hle) ⟨i, hin', by rw [hpt]; exact hti⟩ hv (get!_set_self _ hn3) hsd hold
      (by rw [hlogn, logOf_length]; exact hcL) (by rw [hpc]; exact Int.le_refl _) hcbc
      (by rw [hlogn]; exact cs_ok hgo1.2.2.2.2.1 hcG)
      (by rw [hlogn]; exact lc_ok hl hgo1.2.2.2.1 hrf.2.2.2.1 hcG)
      (by rw [hlogn]; exact ch_ok hgo1.2.2.2.2.1 hcG)
    rw [hlogn] at hod
    rw [hpr]
    obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := commit_fields (n := n) (T := ps₁.term) hb hgo1 hcL hcG hrf.2.1
      hrf.2.2.2.1 hold
    have hok := readyOk_fol (M := S1.msgs) (cf := S1.confirmed[n.val]!) (rd := rd) hs1 hrf hr hro hpr hft hpt
      rfl (Int.le_of_lt hlt) (fun f hf => hf) (fun f hf hn => absurd hf hn) hpm f1 f2 f3 f4 f5 f6 f7
      (.inl rfl) (fun l hl => by rw [← hlogn]; exact hb.2.2.2.2.2.2.1 n l hl) hlh hso
    rw [hpr] at hok
    exact ready_finish hp hgc hs1 hgo1 hl
      (ready_of hq0 hm' rfl (queued_recv _ _ _ _ _ _ _ _ hpend) hod) hok
  | store m hm hty hft hpt hpr hpc0 hprv hsl hcmv hchg =>
    rw [hm.1]
    have hnl : ps₁.role ≠ .leader := by rw [hpr]; decide
    have hpend := pending_of (hno n) (htold hm.1) hm.2.1
    obtain ⟨i, hin', hsi, hti⟩ := hsender m hm
    have hpay : AppPayloadOk m := (hnet.2.2 m hm.2.2.1).1 hty
    have hle : S1.currentTerm[n.val]! ≤ uint.Z m.term := by
      rw [d1]; rcases hft with ⟨h, -⟩ | ⟨h, -, -⟩
      · exact Int.le_of_lt h
      · rw [h]; exact Int.le_refl _
    have hsd : S1.sendable (afOf m (nodeId n)) = .ok true := by
      obtain ⟨-, -, j, hj, hjj⟩ := hnet.1 m hm.2.2.1
      have hjn : j = n := nodeId_inj (hj.symm.trans hm.2.2.2.1)
      subst hjn
      have := (hjj hle).1 (.inl hty)
      rw [hj, mo_appendFact, eok_bind] at this; exact this
    have hcL := nat_commit_le hrf
    have hv : (nameOf ps₁.vote != (if uint.Z ps₁.term != S1.currentTerm[n.val]! then [] else S1.vote n.val))
        = false := by
      rcases hft with ⟨h1, h2⟩ | ⟨h1, -, h2⟩
      · have e : (uint.Z ps₁.term != S1.currentTerm[n.val]!) = true := by
          rw [bne_iff_ne, d1, hpt]; omega
        rw [e, if_pos rfl, h2, nameOf_zero]; rfl
      · have e : (uint.Z ps₁.term != S1.currentTerm[n.val]!) = false := by
          rw [d1, hpt, h1]; exact bne_self_eq_false _
        rw [e, if_neg (by simp), d2, h2]; exact bne_self_eq_false _
    have hm' := inMemory_nl_eq n hc go!"recv" (by decide) ps₁.role hnl ps₁.term ps₁.vote ps₁.commit
      rd.ents d10
    rw [hpr] at hm'
    have hcG := hrf.2.2.1
    have hlogv : S1.log[n.val]! = logOf (V n).ps.log := d3
    have hprev := prevOk_of_match hlogv hprv
    obtain ⟨l, hll, -⟩ := sendable_inv hsd
    rcases hsl with ⟨hen, hpl, hall⟩ | ⟨d, e, hed, hen, hncf, hbef, hidx, hile, hpl⟩
    · -- nothing stored: the commit moves
      rw [hen]
      have hlogn : S1.log[n.val]! = logOf ps₁.log := by rw [d3, hpl]
      obtain ⟨hlt, hcc, hcl⟩ : uint.Z (V n).ps.commit < uint.Z ps₁.commit ∧
          uint.Z ps₁.commit ≤ uint.Z m.commit ∧
          uint.Z ps₁.commit ≤ uint.Z m.index + (m.entries.length : Int) := by
        rcases hcmv with h | h
        · rcases hchg with h' | h'
          · exact absurd hpl h'
          · exact absurd h h'
        · exact h
      have hold : S1.commitIndex[n.val]! < uint.Z ps₁.commit := by rw [d4]; exact hlt
      have hfirst := hasFirst_of_match hlogv hpay m.entries.length (Nat.le_refl _)
        (fun k e _ he => hall k e he)
      obtain ⟨p, hpm, hod⟩ := onDisk_fcommit n hc ps₁.term ps₁.vote ps₁.commit m
        (S1.role.set n.val (roleOf .follower)) S1.leaders S1.ledLog S1.chain S1.termLen S1.viol hty
        hpt.symm (by rw [hpt]; exact hle) ⟨i, hin', by rw [hpt]; exact hti⟩ hv (get!_set_self _ hn3) hsd
        hold (by rw [hlogn, logOf_length]; exact hcL) hcc hcl hprev hfirst
        (by rw [hlogn]; exact cs_ok hgo1.2.2.2.2.1 hcG)
        (by rw [hlogn]; exact lc_ok hl hgo1.2.2.2.1 hrf.2.2.2.1 hcG)
        (by rw [hlogn]; exact ch_ok hgo1.2.2.2.2.1 hcG)
      rw [hlogn] at hod
      rw [hpr]
      obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := commit_fields (n := n) (T := ps₁.term) hb hgo1 hcL hcG
        hrf.2.1 hrf.2.2.2.1 hold
      have hcfe : Confirmed.mk (uint.Z ps₁.term) (fConfIdx S1 n.val false (uint.Z ps₁.term)
          (uint.Z m.index + m.entries.length)) =
          ackConf S1.confirmed[n.val]! (uint.Z m.term) (recvLast m) := by
        rw [hpt]; unfold recvLast; rw [logOf_length]; rfl
      have hge := ackConf_ge S1.confirmed[n.val]! (uint.Z m.term) (recvLast m)
      have hrl : recvLast m = uint.Z m.index + m.entries.length := by unfold recvLast; rw [logOf_length]
      have hg : AckGuard S1 n.val m (nodeId n) :=
        ⟨prev_of_match hlogv hprv, fun k hk => by
          rw [logOf_length] at hk
          have he : m.entries[k]? = some m.entries[k] := List.getElem?_eq_getElem hk
          exact hf_of_match hlogv hpay he (hall k _ he)⟩
      have hok := readyOk_fol (rd := rd) (L1 := logOf ps₁.log)
        (cf := Confirmed.mk (uint.Z ps₁.term) (fConfIdx S1 n.val false (uint.Z ps₁.term)
          (uint.Z m.index + m.entries.length)))
        (M := lset.add S1.msgs (ackFact (nameOf (nodeId n)) (nameOf m.src) (uint.Z ps₁.term)
          (uint.Z m.index + m.entries.length)))
        hs1 hrf hr hro hpr hft hpt rfl (Int.le_of_lt hlt) (fun f hf => mem_lset_add.mpr (.inl hf))
        (fun f hf hn => by
          rcases mem_lset_add.mp hf with h | h
          · exact absurd h hn
          · subst h
            refine ⟨rfl, rfl, ⟨i, by show nameOf m.src = _; rw [hsi]⟩, rfl, .inl ⟨rfl, ?_⟩⟩
            exact fConfIdx_ge S1 n.val false (uint.Z ps₁.term) _)
        hpm f1 f2 f3 f4 f5 f6 f7
        (by
          rw [hcfe]; right
          exact ⟨by rw [hpt]; rfl, by rw [hpt]; exact TermFn.has_of_get hll, by rw [hpt]; exact hge.2⟩)
        (by
          intro l' hll'
          rw [hcfe] at hll' ⊢
          rw [ackConf_term] at hll'
          rw [← hlogn]
          have hpos : 1 ≤ recvLast m := by
            rw [hrl]; have : 0 ≤ uint.Z (V n).ps.commit := by word
            omega
          obtain ⟨m1, m2, m3⟩ := ack_match hl hgo1 hll' hsd hpos hg
          by_cases ht : (S1.confirmed[n.val]!).term = uint.Z m.term
          · obtain ⟨o1, o2, o3⟩ := hb.2.2.2.2.2.2.1 n l' (by rw [ht]; exact hll')
            have e : (ackConf S1.confirmed[n.val]! (uint.Z m.term) (recvLast m)).index =
                imax (S1.confirmed[n.val]!).index (recvLast m) := by
              unfold ackConf; simp only [ht, beq_self_eq_true, ite_true]
            rw [e]; unfold imax
            split
            · exact ⟨o1, o2, o3⟩
            · exact ⟨m1, m2, m3⟩
          · have e : (ackConf S1.confirmed[n.val]! (uint.Z m.term) (recvLast m)).index = recvLast m := by
              have hb' : ((S1.confirmed[n.val]!).term == uint.Z m.term) = false := by simpa using ht
              unfold ackConf; simp only [hb', Bool.false_eq_true, ite_false]
            rw [e]; exact ⟨m1, m2, m3⟩)
        hlh hso
      rw [hpr] at hok
      exact ready_finish hp hgc hs1 hgo1 hl
        (ready_of hq0 hm' rfl (queued_recv _ _ _ _ _ _ _ _ hpend) hod) hok
    · have := hstoreB m hm hty hft hpt hpr hpc0 hprv ⟨d, e, hed, hen, hncf, hbef, hidx, hile, hpl⟩ hcmv
      unfold ReadyGoal at this; rw [hm.1] at this; exact this
  | win src rej mt h1 h2 h3 h4 h5 h6 => exact hwin src rej mt h1 h2 h3 h4 h5 h6
  | prop es h1 h2 h3 h4 h5 h6 h7 h8 h9 => exact hprop es h1 h2 h3 h4 h5 h6 h7 h8 h9
  | cmt h1 h2 h3 h4 h5 h6 h7 h8 => exact hcmt h1 h2 h3 h4 h5 h6 h7 h8

theorem plog_pos {l : List EntryM} {k : w64} (hk1 : 1 ≤ uint.Z k) :
    plogTermAt base0 l k = (fun e : EntryM => e.Term') <$> l[(uint.Z k - 1).toNat]? := by
  have hb : uint.Z (base0 : go_etcd_io.raft.v3.entryID).index' = 0 := rfl
  unfold plogTermAt
  rw [hb, if_neg (by omega), if_neg (by omega)]
  congr 2

set_option maxHeartbeats 2000000 in
/-- **A follower's store** (`store` with entries from the first conflict): `onDisk_fstore`. -/
theorem ready_storeB (S : State) (V : Fin 3 → NodeView) (net : List Msg) (evs : List Event)
    (G : RaftFacts) (n : Fin 3) (ps₁ : PState) (rd : ReadyD)
    (hp : Prefix cfg3 evs S) (hs : AntSim S V net) (hl : RaftLaws G) (hgo : GlobalOk S net G)
    (hr : Reach (nodeId n) net (V n) ps₁) (hro : ReadyOutP (nodeId n) (V n) ps₁ rd)
    (htold : (V n).byE = go!"recv" → (V n).told = true)
    (hrf : ReadyFacts G (nodeId n) ps₁) (m : Msg) (hm : RecvAt (nodeId n) net (V n) m) (hty : m.ty = .app)
    (hft : FolTerm (V n).ps m ps₁) (hpt : ps₁.term = m.term) (hpr : ps₁.role = .follower)
    (hpc0 : uint.Z (V n).ps.commit ≤ uint.Z m.index)
    (hprv : PlogMatches base0 (V n).ps.log (entryID.mk m.logterm m.index))
    (hsl : ∃ (d : Nat) (e : EntryM), m.entries[d]? = some e ∧ rd.ents = m.entries.drop d ∧
        ¬ PlogMatches base0 (V n).ps.log (entId e) ∧
        (∀ (k : Nat) (e' : EntryM), k < d → m.entries[k]? = some e' →
          PlogMatches base0 (V n).ps.log (entId e')) ∧
        uint.Z e.Index' = uint.Z m.index + (d : Int) + 1 ∧
        uint.Z e.Index' ≤ ((V n).ps.log.length : Int) + 1 ∧
        ps₁.log = (V n).ps.log.take (uint.nat e.Index' - 1) ++ rd.ents)
    (hcmv : ps₁.commit = (V n).ps.commit ∨ (uint.Z (V n).ps.commit < uint.Z ps₁.commit ∧
        uint.Z ps₁.commit ≤ uint.Z m.commit ∧
        uint.Z ps₁.commit ≤ uint.Z m.index + (m.entries.length : Int))) :
    ReadyGoal S V net evs G n ps₁ rd := by
  obtain ⟨d, e, hed, hen, hncf, hbef, hidx, hile, hpl⟩ := hsl
  obtain ⟨S1, hgc, hs1, hgo1⟩ := antSim_gc S V net G hs hl hgo
  have hs1' := hs1
  obtain ⟨hsh, hb, hnet, hno⟩ := hs1'
  have hc : S1.cfg = cfg3 := hsh.1
  have hrl : S1.role.length = 3 := hsh.2.2.2.2.2.2.1
  have hn3 : n.val < S1.role.length := by rw [hrl]; exact n.isLt
  have hlg3 : n.val < S1.log.length := by rw [hsh.2.2.2.2.1]; exact n.isLt
  obtain ⟨hd, -, -, -, hQ, -, hca, hlo, hvsN⟩ := hno n
  obtain ⟨d1, d2, d3, d4, d5, -, d7, d8, d9, d10, -, -, -⟩ := hd
  have hq0 : S1.queue[n.val]! = [] := (hb.2.1 n).1
  have hin : ∀ m ∈ net, InMsg m := fun m hm => ⟨(hnet.1 m hm).1, hnet.2.2 m hm⟩
  have hqs : ∀ q ∈ (V n).qs, SelfMsg (nodeId n) (V n).ps.term q := fun q hq => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hQ q hq
    exact ⟨h1, h2, h3, h4, h5.imp (fun h => h.1) (fun h => h.1)⟩
  have hso := selfOut_reach hr d7 hlo hin hqs
  have hlh := reach_leadOk hnet (hno n) hr
  unfold ReadyGoal
  rw [hm.1]
  have hnl : ps₁.role ≠ .leader := by rw [hpr]; decide
  have hpend := pending_of (hno n) (htold hm.1) hm.2.1
  obtain ⟨i, hin', hsi, hti⟩ : ∃ i : Fin 3, i ≠ n ∧ m.src = nodeId i ∧
      uint.Z m.term ≤ S1.currentTerm[i.val]! := by
    obtain ⟨-, ⟨i, hi, hti⟩, -⟩ := hnet.1 m hm.2.2.1
    refine ⟨i, fun h => ?_, hi, hti⟩
    subst h
    exact (hnet.2.2 m hm.2.2.1).2.1 (by rw [hi, hm.2.2.2.1])
  have hpay : AppPayloadOk m := (hnet.2.2 m hm.2.2.1).1 hty
  have hle : S1.currentTerm[n.val]! ≤ uint.Z m.term := by
    rw [d1]; rcases hft with ⟨h, -⟩ | ⟨h, -, -⟩
    · exact Int.le_of_lt h
    · rw [h]; exact Int.le_refl _
  have hsd : S1.sendable (afOf m (nodeId n)) = .ok true := by
    obtain ⟨-, -, j, hj, hjj⟩ := hnet.1 m hm.2.2.1
    have hjn : j = n := nodeId_inj (hj.symm.trans hm.2.2.2.1)
    subst hjn
    have := (hjj hle).1 (.inl hty)
    rw [hj, mo_appendFact, eok_bind] at this; exact this
  have hcL := nat_commit_le hrf
  have hv : (nameOf ps₁.vote != (if uint.Z ps₁.term != S1.currentTerm[n.val]! then [] else S1.vote n.val))
      = false := by
    rcases hft with ⟨h1, h2⟩ | ⟨h1, -, h2⟩
    · have e : (uint.Z ps₁.term != S1.currentTerm[n.val]!) = true := by
        rw [bne_iff_ne, d1, hpt]; omega
      rw [e, if_pos rfl, h2, nameOf_zero]; rfl
    · have e : (uint.Z ps₁.term != S1.currentTerm[n.val]!) = false := by
        rw [d1, hpt, h1]; exact bne_self_eq_false _
      rw [e, if_neg (by simp), d2, h2]; exact bne_self_eq_false _
  have hcG := hrf.2.2.1
  have hlogv : S1.log[n.val]! = logOf (V n).ps.log := d3
  have hprev := prevOk_of_match hlogv hprv
  obtain ⟨l, hll, -⟩ := sendable_inv hsd
  -- the stored entries
  have hdl : d < m.entries.length := (List.getElem?_eq_some_iff.mp hed).1
  have hents : rd.ents = e :: m.entries.drop (d + 1) := by rw [hen]; exact list_drop_S _ _ _ hed
  have hm0 : 0 ≤ uint.Z m.index := by word
  have hjv : uint.nat e.Index' - 1 ≤ (V n).ps.log.length := by have := hile; word
  have hjz : ((uint.nat e.Index' - 1 : Nat) : Int) = uint.Z e.Index' - 1 := by
    have : 1 ≤ uint.Z e.Index' := by omega
    word
  have hL1eq : (S1.log[n.val]!).take (uint.Z e.Index' - 1).toNat ++ logOf (e :: m.entries.drop (d + 1)) =
      logOf ps₁.log := by
    rw [hpl, hents, hlogv, logOf_take, logOf, logOf, logOf, List.map_append]
    congr 3; omega
  have hm' := inMemory_nl_eq n hc go!"recv" (by decide) ps₁.role hnl ps₁.term ps₁.vote ps₁.commit
    rd.ents d10
  rw [hpr, hents] at hm'
  obtain ⟨eqb, heqb⟩ := entriesEqual_logOf ps₁.log (V n).ps.log
  have hold0 : S1.commitIndex[n.val]! ≤ uint.Z ps₁.commit := by
    rw [d4]; rcases hcmv with h | h
    · rw [h]; exact Int.le_refl _
    · exact Int.le_of_lt h.1
  obtain ⟨p, hpm, hod⟩ := onDisk_fstore n hc ps₁.term ps₁.vote ps₁.commit m e (m.entries.drop (d + 1))
    (S1.role.set n.val (roleOf .follower)) S1.leaders S1.ledLog S1.chain S1.termLen S1.viol eqb hty
    hpt.symm (by rw [hpt]; exact hle) ⟨i, hin', by rw [hpt]; exact hti⟩ hv (get!_set_self _ hn3) hsd hprev
    (by omega) (by omega)
    (by
      have : uint.Z e.Index' - uint.Z m.index - 1 = (d : Int) := by omega
      rw [this]; exact hasFirst_of_match hlogv hpay d (Nat.le_of_lt hdl) hbef)
    (by
      have : (uint.Z e.Index' - uint.Z m.index - 1).toNat = d := by omega
      rw [this]; exact (list_drop_S _ _ _ hed).symm)
    (by
      intro hfl hteq
      apply hncf
      show plogTermAt base0 (V n).ps.log e.Index' = some e.Term'
      rw [hlogv, logOf_length] at hfl
      rw [plog_pos (by omega)]
      have hlt : (uint.Z e.Index' - 1).toNat < (V n).ps.log.length := by omega
      rw [List.getElem?_eq_getElem hlt]
      rw [hlogv, logOf_getElem! (List.getElem?_eq_getElem hlt), entOf_term] at hteq
      simp only [Option.map_eq_map, Option.map_some]
      exact congrArg some (uint_Z_inj.mp hteq))
    (by rw [hlogv, logOf_length]; intro h; omega) hold0
    (by rw [hL1eq, logOf_length]; exact hcL)
    (fun h => by
      rcases hcmv with h' | h'
      · rw [h', ← d4] at h; exact absurd h (Int.lt_irrefl _)
      · exact h'.2.1)
    (by
      rcases hcmv with h' | h'
      · rw [h']; have : (m.entries.length : Int) ≥ 0 := by omega
        omega
      · exact h'.2.2)
    (by rw [hL1eq, hlogv]; exact heqb)
    (by rw [hL1eq]; exact lm_ok hl hrf.1 hgo1.2.2.1 hsh.2.2.2.2.1)
    (by rw [hL1eq]; exact cs_ok hgo1.2.2.2.2.1 hcG)
    (by rw [hL1eq]; exact lc_ok hl hgo1.2.2.2.1 hrf.2.2.2.1 hcG)
    (by rw [hL1eq]; exact ch_ok hgo1.2.2.2.2.1 hcG)
    (fun h => by rw [h]; exact (hb.2.2.2.2.1 n).1)
  rw [hL1eq] at hod
  -- the acknowledgement's guard at the log after the write
  have hb0 : uint.Z (base0 : go_etcd_io.raft.v3.entryID).index' = 0 := rfl
  have hpm1 : PlogMatches base0 ps₁.log (entryID.mk m.logterm m.index) := by
    show plogTermAt base0 ps₁.log m.index = some m.logterm
    have h' : plogTermAt base0 (V n).ps.log m.index = some m.logterm := hprv
    by_cases hi0 : uint.Z m.index = 0
    · unfold plogTermAt at h' ⊢
      rw [hb0, if_neg (by omega), if_pos hi0] at h' ⊢; exact h'
    · rw [hpl, plog_take_append hjv (by omega), if_pos (by omega)]; exact h'
  have hpmk : ∀ (k : Nat) (x : EntryM), m.entries[k]? = some x → PlogMatches base0 ps₁.log (entId x) := by
    intro k x hx
    have hxi := hpay.1 k x hx
    simp only at hxi; push_cast at hxi
    show plogTermAt base0 ps₁.log x.Index' = some x.Term'
    rw [hpl, plog_take_append hjv (by omega)]
    by_cases hkd : k < d
    · rw [if_pos (by omega)]; exact hbef k x hkd hx
    · rw [if_neg (by omega), hen, List.getElem?_drop]
      have : d + (uint.Z x.Index' - ↑(uint.nat e.Index' - 1) - 1).toNat = k := by omega
      rw [this, hx]; rfl
  let S' : State := { S1 with log := S1.log.set n.val (logOf ps₁.log) }
  have hlog' : S'.log[n.val]! = logOf ps₁.log := get!_set_self _ hlg3
  have hgo' : GlobalOk S' net G := by
    obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := hgo1
    refine ⟨g1, g2, fun k => ?_, g4, g5, g6, g7⟩
    by_cases hk : k = n
    · subst hk; exact ⟨ps₁.log, hrf.1, hlog'⟩
    · show ∃ l ∈ G.logs, (S1.log.set n.val (logOf ps₁.log))[k.val]! = logOf l
      rw [get!_set_ne _ _ (fun h => hk (Fin.ext h))]; exact g3 k
  have hg : AckGuard S' n.val m (nodeId n) :=
    ⟨prev_of_match hlog' hpm1, fun k hk => by
      rw [logOf_length] at hk
      have he : m.entries[k]? = some m.entries[k] := List.getElem?_eq_getElem hk
      exact hf_of_match hlog' hpay he (hpmk k _ he)⟩
  have hrl : recvLast m = uint.Z m.index + m.entries.length := by unfold recvLast; rw [logOf_length]
  have hpos : 1 ≤ recvLast m := by rw [hrl]; omega
  obtain ⟨m1, m2, m3⟩ := ack_match hl hgo' hll hsd hpos hg
  rw [hlog', hrl] at m1 m3; rw [hrl] at m2
  -- the confirmation does not move down at its term
  have hcmono : (S1.confirmed[n.val]!).term = uint.Z ps₁.term →
      (S1.confirmed[n.val]!).index ≤ uint.Z m.index + m.entries.length := by
    intro ht
    rw [hpt] at ht
    obtain ⟨o1, o2, o3⟩ := hb.2.2.2.2.2.2.1 n l (by rw [ht]; exact hll)
    refine Int.not_lt.mp fun hlt => hncf ?_
    rw [hlogv, logOf_length] at o1
    have hj : (uint.Z e.Index' - 1).toNat = uint.nat e.Index' - 1 := by omega
    have h1 := congrArg (·[(uint.Z e.Index' - 1).toNat]?) o3
    have h2 := congrArg (·[(uint.Z e.Index' - 1).toNat]?) m3
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_take_of_lt (by omega)] at h1
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_take_of_lt (by omega)] at h2
    rw [← h2, hlogv] at h1
    have h3 : (logOf ps₁.log)[(uint.Z e.Index' - 1).toNat]? = some (entOf e) := by
      rw [hpl, hents, hj, logOf, List.map_append, List.getElem?_append_right (by simp; omega)]
      simp only [List.length_map, List.length_take]
      rw [Nat.min_eq_left hjv, Nat.sub_self]; rfl
    rw [h3] at h1
    unfold logOf at h1
    rw [List.getElem?_map] at h1
    show plogTermAt base0 (V n).ps.log e.Index' = some e.Term'
    rw [plog_pos (by omega)]
    cases hx : (V n).ps.log[(uint.Z e.Index' - 1).toNat]? with
    | none => rw [hx] at h1; cases h1
    | some x =>
      rw [hx] at h1
      have hxe : entOf x = entOf e := Option.some.inj h1
      have := congrArg Entry.term hxe
      rw [entOf_term, entOf_term] at this
      simp only [Option.map_eq_map, Option.map_some]
      exact congrArg some (uint_Z_inj.mp this)
  have hhas : S1.ledLog.has (uint.Z ps₁.term) = true := by rw [hpt]; exact TermFn.has_of_get hll
  have hconf : ∀ l', S1.ledLog.get (Confirmed.mk (uint.Z ps₁.term) (uint.Z m.index + m.entries.length)).term
      = .ok l' → (uint.Z m.index + m.entries.length : Int) ≤ (logOf ps₁.log).length ∧
      (uint.Z m.index + m.entries.length : Int) ≤ l'.length ∧
      (logOf ps₁.log).take (uint.Z m.index + (m.entries.length : Int)).toNat =
        l'.take (uint.Z m.index + (m.entries.length : Int)).toNat := by
    intro l' hl'
    change S1.ledLog.get (uint.Z ps₁.term) = .ok l' at hl'
    have hll' : S1.ledLog.get (uint.Z m.term) = .ok l := hll
    rw [hpt, hll'] at hl'; cases hl'
    exact ⟨m1, m2, m3⟩
  rw [hpr, hents]
  by_cases hlt : S1.commitIndex[n.val]! < uint.Z ps₁.commit
  · rw [if_pos hlt, if_pos hlt] at hod
    obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := commit_fields (n := n) (T := ps₁.term) hb hgo1 hcL hcG
      hrf.2.1 hrf.2.2.2.1 hlt
    have hok := readyOk_fol (rd := rd) (L1 := logOf ps₁.log)
      (cf := Confirmed.mk (uint.Z ps₁.term) (uint.Z m.index + m.entries.length))
      (M := lset.add S1.msgs (ackFact (nameOf (nodeId n)) (nameOf m.src) (uint.Z ps₁.term)
        (uint.Z m.index + m.entries.length)))
      hs1 hrf hr hro hpr hft hpt rfl (by rw [← d4]; exact Int.le_of_lt hlt)
      (fun f hf => mem_lset_add.mpr (.inl hf))
      (fun f hf hn => by
        rcases mem_lset_add.mp hf with h | h
        · exact absurd h hn
        · subst h
          exact ⟨rfl, rfl, ⟨i, by show nameOf m.src = _; rw [hsi]⟩, rfl, .inl ⟨rfl, Int.le_refl _⟩⟩)
      hpm f1 f2 f3 f4 f5 f6 f7 (.inr ⟨rfl, hhas, hcmono⟩) hconf hlh hso
    rw [hpr] at hok
    exact ready_finish hp hgc hs1 hgo1 hl
      (ready_of hq0 hm' rfl (queued_recv _ _ _ _ _ _ _ _ hpend) hod) hok
  · rw [if_neg hlt, if_neg (fun h => hlt h.1), if_neg hlt] at hod
    have hceq : uint.Z ps₁.commit = S1.commitIndex[n.val]! := by omega
    have hok := readyOk_fol (rd := rd) (L1 := logOf ps₁.log)
      (cf := Confirmed.mk (uint.Z ps₁.term) (uint.Z m.index + m.entries.length))
      (M := S1.msgs) (ch := S1.chain) (tl := S1.termLen)
      hs1 hrf hr hro hpr hft hpt rfl (by rw [← d4]; exact hold0)
      (fun f hf => hf) (fun f hf hn => absurd hf hn) hpm (List.prefix_refl _)
      ⟨by rw [hceq]; exact (hb.2.2.2.2.1 n).1,
        ch_ok hgo1.2.2.2.2.1 hcG (by rw [hceq]; exact (hb.2.2.2.2.1 n).1)⟩
      hb.2.2.2.1
      (by
        rcases hb.2.2.2.2.2.1 n with h | ⟨q, hq, h1, h2⟩
        · exact .inl (hceq ▸ h)
        · refine .inr ⟨q, hq, ?_, hceq ▸ h2⟩
          have := hle; rw [← hpt] at this; omega)
      (fun q hq => ⟨q, hq, rfl, Int.le_refl _⟩) hgo1.2.2.2.2.1 hgo1.2.2.2.2.2.1
      (.inr ⟨rfl, hhas, hcmono⟩) hconf hlh hso
    rw [hpr] at hok
    exact ready_finish hp hgc hs1 hgo1 hl
      (ready_of hq0 hm' rfl (queued_recv _ _ _ _ _ _ _ _ hpend) hod) hok

/-- **`antSim_ready` for every kind but a leader's** (`win`, `prop`, `cmt` as premises). -/
theorem ready_nonleader (S : State) (V : Fin 3 → NodeView) (net : List Msg) (evs : List Event)
    (G : RaftFacts) (n : Fin 3) (ps₁ : PState) (rd : ReadyD)
    (hp : Prefix cfg3 evs S) (hs : AntSim S V net) (hl : RaftLaws G) (hgo : GlobalOk S net G)
    (hr : Reach (nodeId n) net (V n) ps₁) (hro : ReadyOutP (nodeId n) (V n) ps₁ rd)
    (hrep : Reported (V n) rd) (htold : (V n).byE = go!"recv" → (V n).told = true)
    (hrf : ReadyFacts G (nodeId n) ps₁) (htb : uint.Z (V n).ps.term + 1 < 2 ^ 64)
    (hwin : ∀ (src : w64) (rej : Bool) (mt : GMap w64 w64), (V n).ps.role = .candidate →
      ((∃ m, RecvAt (nodeId n) net (V n) m ∧ m.ty = .voteResp ∧ m.term = (V n).ps.term ∧ m.src = src ∧
          m.reject = rej) ∨
        (src = nodeId n ∧ rej = false ∧ ∃ q ∈ (V n).qs, q.ty = .voteResp)) →
      JQuorum cfgM3 (granted (recordVote (V n).ps.votes src (!rej))) →
      LeaderMatchOk (nodeId n) (V n).ps mt →
      LeadC (nodeId n) (pwinState (nodeId n) { (V n).ps with votes := recordVote (V n).ps.votes src (!rej) } mt)
        ps₁ →
      rd.ents = [pleaderEntry (V n).ps] → ReadyGoal S V net evs G n ps₁ rd)
    (hprop : ∀ es : List EntryM, (V n).byE = go!"propose" → (V n).ps.role = .leader → es ≠ [] →
      rd.ents = es.mapIdx (stamp (V n).ps.term (plastIndex (V n).ps)) → ps₁.log = (V n).ps.log ++ rd.ents →
      ps₁.role = .leader → ps₁.term = (V n).ps.term → ps₁.vote = (V n).ps.vote →
      ps₁.commit = (V n).ps.commit → ReadyGoal S V net evs G n ps₁ rd)
    (hcmt : (V n).ps.role = .leader → ps₁.role = .leader → ps₁.term = (V n).ps.term →
      ps₁.vote = (V n).ps.vote → ps₁.log = (V n).ps.log → rd.ents = [] →
      uint.Z (V n).ps.commit < uint.Z ps₁.commit → CmtOk ps₁ ps₁.commit →
      ReadyGoal S V net evs G n ps₁ rd) :
    ∃ S', Prefix cfg3
        (evs ++ [evReady (nodeId n) (V n).byE rd.role rd.term rd.vote rd.commit rd.ents]) S' ∧
      AntSim S' (setV V n ((V n).afterReady ps₁ rd)) net ∧ GlobalOk S' net G :=
  ready_main S V net evs G n ps₁ rd hp hs hl hgo hr hro hrep htold hrf htb
    (fun m hm hty hft hpt hpr hpc0 hprv hsl hcmv =>
      ready_storeB S V net evs G n ps₁ rd hp hs hl hgo hr hro htold hrf m hm hty hft hpt hpr hpc0 hprv hsl hcmv)
    hwin hprop hcmt

end ready

end AntSim
end EtcdGrove
end Perennial
