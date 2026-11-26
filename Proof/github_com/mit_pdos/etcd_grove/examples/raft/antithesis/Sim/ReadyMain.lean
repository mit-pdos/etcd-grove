/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: `antSim_ready`'s follower and candidate kinds (#33 S4; parity B1)

From `RdCtx` (`Ready.lean`): per `ReadyKind` but a leader's, `InMemory` and `OnDisk` of the `ready`
report evaluated (`ReadyEval`, `ReadyOD`, `ReadyOD2`) and `ReadyOk` (`readyOk_plain` for the kinds that
write no entry and move no commit, `readyOk_fol` for a follower's store or commit), then
`RdCtx.finish` (`ready_main`, with a store from a conflict `ready_storeB`); the leader kinds (`win`,
`prop`, `cmt`) are `ready_nonleader`'s premises, discharged in `ReadyAll.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Ready

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open AntCheck go_etcd_io.raft.v3

theorem precand_ne_leader : (go!"precandidate" : Str) ≠ leader := by decide

theorem precand_ne_follower : (go!"precandidate" : Str) ≠ follower := by decide

section main
variable [GooseExts]
variable {R : RunCfg} {dec : CCDec} {xnet : List XMsg}

/-- A message of the S4 types keeps no term (`PreTermKeep`: a pre-vote message). -/
theorem InMsg.notPre {m : Msg} (h : InMsg m) : ¬ PreTermKeep m := by
  rintro (h' | ⟨h', -⟩) <;> rcases h.1 with h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h1] at h' <;> cases h'

/-- The binding's leader role is raft's (a pre-candidate is reported as `precandidate`). -/
theorem roleS_leader {v : NodeView} (h : roleS v = leader) : v.ps.role = .leader := by
  unfold roleS roleStr at h
  split at h
  · exact absurd h precand_ne_leader
  · exact (roleOf_leader_iff _).mp h

/-! ## A follower's commit on a leader's message -/

/-- **A follower's commit on a leader's message** (an append or heartbeat sent to node `n`, whose
term `n` has not passed): its term is led, and its commit is within every leader's of its term
(election safety, C4's `LeadCommitMsgOk`). -/
theorem fol_led {S : State} {V : Fin R.N → NodeView} {net : List Msg} {G : RaftFacts} {n : Fin R.N}
    {m : Msg} (hs : AntSim R dec S V net xnet) (hgo : GlobalOk R S net G) (hl : RaftLaws G)
    (hdk : ∀ k : Fin R.N, (V k).dur = durOf (V k).r) (hm : m ∈ net)
    (hty : m.ty = .app ∨ m.ty = .heartbeat) (hdst : m.dst = nodeId n)
    (hle : S.currentTerm[n.val]! ≤ uint.Z m.term) :
    (∃ l ∈ S.leaders, l.term = uint.Z m.term) ∧
    ∀ k : Fin R.N, S.role[k.val]! = leader → S.currentTerm[k.val]! = uint.Z m.term →
      uint.Z m.commit ≤ S.commitIndex[k.val]! := by
  obtain ⟨-, -, hn, -, hno⟩ := hs
  obtain ⟨-, -, j, hj, hjk⟩ := hn.1 m hm
  have hjn : j = n := nodeId_inj (hj.symm.trans hdst)
  subst hjn
  have hsd := (hjk hle).1 hty
  rw [toAppendFact_msgOf, eok_bind] at hsd
  have hlm := List.contains_iff_mem.mp (sendable_led hsd)
  refine ⟨⟨_, hlm, rfl⟩, fun k hk hkt => ?_⟩
  have hvk : (V k).ps.role = .leader := (roleOf_leader_iff _).mp (by rw [← (hno k).mem.1]; exact hk)
  have hkm := List.contains_iff_mem.mp ((hno k).leader hvk).1
  have hct : S.currentTerm[k.val]! = uint.Z (V k).ps.term := by rw [(hno k).disk.1, hdk k]; rfl
  have hik : m.src = nodeId k := nameOf_inj (hgo.leader_server hl hlm hkm (by
    show uint.Z m.term = uint.Z (V k).ps.term; rw [← hct, hkt]))
  exact hn.2.2.2.1 m hm hty k hik (by rw [hk]; decide) hkt

/-- `termLen` after a follower's commit `cc` on a leader's message at term `T` (`OnDisk`'s `adv`):
it only grows, at `T`, which is led, within every leader's commit at `T`. -/
theorem fol_tl {S : State} {V : Fin R.N → NodeView} {net : List Msg} {G : RaftFacts} {n : Fin R.N}
    {m : Msg} {T cc : w64} (hs : AntSim R dec S V net xnet) (hgo : GlobalOk R S net G) (hl : RaftLaws G)
    (hdk : ∀ k : Fin R.N, (V k).dur = durOf (V k).r) (hm : m ∈ net)
    (hty : m.ty = .app ∨ m.ty = .heartbeat) (hdst : m.dst = nodeId n)
    (hle : S.currentTerm[n.val]! ≤ uint.Z m.term) (hT : T = m.term) (hcc : uint.Z cc ≤ uint.Z m.commit) :
    (∀ T', tlOld S.termLen T' ≤ tlOld (S.termLen.with (uint.Z T) (imax (tlOld S.termLen (uint.Z T)) (uint.Z cc))) T') ∧
    (∀ T', tlOld S.termLen T' <
        tlOld (S.termLen.with (uint.Z T) (imax (tlOld S.termLen (uint.Z T)) (uint.Z cc))) T' →
      T' = uint.Z T ∧ (∃ l ∈ S.leaders, l.term = uint.Z T) ∧
      ∀ k : Fin R.N, k ≠ n → S.role[k.val]! = leader → S.currentTerm[k.val]! = uint.Z T →
        tlOld (S.termLen.with (uint.Z T) (imax (tlOld S.termLen (uint.Z T)) (uint.Z cc))) (uint.Z T) ≤
          S.commitIndex[k.val]!) := by
  subst hT
  obtain ⟨hld, hk⟩ := fol_led hs hgo hl hdk hm hty hdst hle
  have hb17 := hs.2.1.termLenOk
  refine ⟨fun T' => ?_, fun T' hlt => ?_⟩
  · rw [tlOld_with]; unfold imax
    by_cases h1 : T' = uint.Z m.term
    · rw [if_pos h1]; subst h1; split <;> omega
    · rw [if_neg h1]; exact Int.le_refl _
  · rw [tlOld_with] at hlt
    have hT' : T' = uint.Z m.term := by
      by_cases h : T' = uint.Z m.term
      · exact h
      · rw [if_neg h] at hlt; omega
    subst hT'
    refine ⟨rfl, hld, fun k _ hkl hkt => ?_⟩
    have h1 := hk k hkl hkt
    have h2 := (hb17.2 k hkl).2
    rw [hkt] at h2
    rw [tlOld_with, if_pos rfl]; unfold imax; split <;> omega

/-! ## Small facts of the kinds -/

/-- A follower's `Ready` queues no self-addressed message. -/
theorem qs_follower {id : w64} {N : Nat} {v : NodeView} {ps : PState} {rd : ReadyD}
    (hro : ReadyOutO N id v ps rd) (hso : SelfOut id ps) (hf : ps.role = .follower) :
    ∀ q ∈ rd.qs, False := by
  intro q hq
  rcases (qs_self hro hso q hq).2 with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [hf] at h <;> cases h

/-- `UpToDate` of a vote request against the node's log is raft's `plogUpToDate`. -/
theorem upToDate_of {S : State} {n : Nat} {l : List EntryM} {m : Msg}
    (hlog : S.log[n]! = logOf l) (hidx : LogIdx l)
    (h : plogUpToDate base0 l (entryID.mk m.logterm m.index) = true) :
    S.upToDate (vfOf m) n = true := by
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
theorem pending_of {S : State} {net : List Msg} {n : Fin R.N} {v : NodeView} {m : Msg}
    (hv : NodeOk R dec S net n v) (ht : v.told = true) (hca : v.cause = some m) :
    S.pending[n.val]! = [msgOf m (nodeId n)] := by
  rcases hv.told ht with ⟨m', h1, h2⟩ | ⟨x, hx, -⟩
  · rw [hca] at h1; cases h1; exact h2
  · rw [(hv.xcause x hx).2] at hca; cases hca

theorem queued_recv (S : State) (n : Nat) (id : w64) (r : Role) (t v c : w64) (es : List EntryM) (m : Msg)
    (hp : S.pending[n]! = [msgOf m id]) :
    S.queued n (evReady id go!"recv" (roleOf r) t v c es) =
      .ok { ev := evReady id go!"recv" (roleOf r) t v c es, m := [msgOf m id] } := by
  rw [queued_ready, if_pos rfl, hp]

theorem queued_other (S : State) (n : Nat) (id : w64) (b : Str) (r : Role) (t v c : w64) (es : List EntryM)
    (hb : b ≠ go!"recv") :
    S.queued n (evReady id b (roleOf r) t v c es) =
      .ok { ev := evReady id b (roleOf r) t v c es, m := [] } := by
  rw [queued_ready, if_neg hb]

/-! ## Kinds that write no entry and move no commit -/

section ctx
variable {S : State} {V : Fin R.N → NodeView} {net : List Msg} {evs : List Event} {G : RaftFacts}
  {n : Fin R.N} {r₁ : RState} {rd : ReadyD} {S1 : State}

theorem RdCtx.rlen (hx : RdCtx R dec S V net xnet evs G n r₁ rd S1) : S1.role.length = R.N :=
  hx.hs1.1.2.2.2.2.2.2.1

/-- The new view's binding role: raft's (no pre-candidate below `mskB1a`). -/
theorem RdCtx.roleS_w (hx : RdCtx R dec S V net xnet evs G n r₁ rd S1) :
    roleS ((V n).afterReady r₁ rd) = roleOf r₁.p.role := by
  show roleStr rd.pre r₁.p.role = _; rw [hx.hpf]; rfl

theorem RdCtx.logG (hx : RdCtx R dec S V net xnet evs G n r₁ rd S1) : r₁.p.log ∈ G.logs := by
  rw [← hx.hfl]; exact hx.hrf.1

/-- **`ReadyOk` of a `Ready` that changes only the term, the vote or the role** of a non-leader
(`camp`, `grant`, `adopt`, `demote`): `InMemory`'s `memNL`, `OnDisk`'s log, commit, confirmation,
leaders, leader logs, `chain`, `termLen` as they were; the facts `M` and votes `Vs` only the
campaign's vote request and the node's own vote. -/
theorem readyOk_plain (hx : RdCtx R dec S V net xnet evs G n r₁ rd S1)
    {vo : Option Str} {M : List Fact} {Vs : List VoteRec} {p : Pre}
    (hnl : r₁.p.role ≠ .leader) (hlog : r₁.p.log = (V n).ps.log) (hcm : r₁.p.commit = (V n).ps.commit)
    (htge : uint.Z (V n).ps.term ≤ uint.Z r₁.p.term)
    (hvl : (V n).ps.role = .leader → (V n).ps.term ≠ r₁.p.term)
    (hvote : match vo with
      | some x => x = nameOf r₁.p.vote ∧ S1.bootTerm < uint.Z r₁.p.term
      | none => (r₁.p.term = (V n).ps.term ∧ r₁.p.vote = (V n).ps.vote) ∨
          (uint.Z (V n).ps.term < uint.Z r₁.p.term ∧ r₁.p.vote = W64 0))
    (hmsub : ∀ f ∈ S1.msgs, f ∈ M)
    (hmnew : ∀ f ∈ M, f ∉ S1.msgs → f.type = go!"vote" ∧ S1.bootTerm < f.term)
    (hvsub : ∀ y ∈ S1.votes, y ∈ Vs)
    (hvnew : ∀ y ∈ Vs, y ∉ S1.votes →
      y = { voter := nameOf (nodeId n), term := uint.Z r₁.p.term, cand := nameOf r₁.p.vote } ∧
        r₁.p.vote ≠ W64 0)
    (hvin : vo ≠ none →
      { voter := nameOf (nodeId n), term := uint.Z r₁.p.term, cand := nameOf r₁.p.vote } ∈ Vs)
    (hpm : PreOk S1 n.val (S1.log[n.val]!) p)
    (hcp : CandPart (readyS S1 n.val (uint.Z r₁.p.term) vo (S1.log[n.val]!) (uint.Z r₁.p.commit)
      (S1.role.set n.val (roleOf r₁.p.role)) (S1.confirmed[n.val]!) M Vs S1.leaders S1.ledLog p S1.chain
      S1.termLen S1.viol (memNL S1 n.val (roleOf r₁.p.role))) n ((V n).afterReady r₁ rd))
    (hqs : ∀ q ∈ rd.qs, QsOk R (readyS S1 n.val (uint.Z r₁.p.term) vo (S1.log[n.val]!) (uint.Z r₁.p.commit)
      (S1.role.set n.val (roleOf r₁.p.role)) (S1.confirmed[n.val]!) M Vs S1.leaders S1.ledLog p S1.chain
      S1.termLen S1.viol (memNL S1 n.val (roleOf r₁.p.role))) n ((V n).afterReady r₁ rd) q)
    (hrnf : r₁.p.role ≠ .follower → r₁.p.term = (V n).ps.term → (V n).ps.role ≠ .follower) :
    ReadyOk R dec S1 V net G n ((V n).afterReady r₁ rd) (uint.Z r₁.p.term) vo (S1.log[n.val]!)
      (uint.Z r₁.p.commit) (S1.role.set n.val (roleOf r₁.p.role)) (S1.confirmed[n.val]!) M Vs
      S1.leaders S1.ledLog p S1.chain S1.termLen S1.viol (memNL S1 n.val (roleOf r₁.p.role)) := by
  have hb := hx.hs1.2.1
  have hgo := hx.hgo1
  have ha := hx.ha
  have hrl : S1.role.length = R.N := hx.rlen
  have hn3 := hx.hn3
  have hcmZ : S1.commitIndex[n.val]! = uint.Z r₁.p.commit := by rw [hx.d4, hcm]
  exact {
    hterm := rfl
    tge := by rw [hx.d1]; exact htge
    hvote := by
      cases vo with
      | some x => exact hvote
      | none =>
        rcases hvote with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact .inl ⟨by rw [hx.d1, h1], by rw [hx.d2]; show _ = nameOf r₁.p.vote; rw [h2]⟩
        · exact .inr ⟨by rw [hx.d1]; exact h1, h2⟩
    hlog := by rw [hx.d3]; show logOf (V n).ps.log = logOf r₁.p.log; rw [hlog]
    hcommit := rfl
    cge := Int.le_of_eq hcmZ
    hrole := by rw [get!_set_self _ hn3]; rfl
    rlen := by rw [List.length_set, hrl]
    rother := fun k hk => get!_set_ne _ _ (fun h => hk (Fin.ext h))
    rstay := by
      intro hl ht
      rw [hx.d5, roleOf_leader_iff] at hl
      exact absurd (uint_Z_inj.mp (by rw [← hx.d1, ← ht])).symm (hvl hl)
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
    mnew := fun f hf hn => .inl (hmnew f hf hn)
    vsub := hvsub
    vnew := fun y hy hn => ⟨(hvnew y hy hn).1, hx.hrf.2.2.2.2.2 (hvnew y hy hn).2⟩
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
      obtain ⟨e1, e2⟩ := hb.2.2.1 n
      rw [hcmZ] at e1 e2
      exact ⟨e1, e2⟩
    tlLen := hb.2.1
    tlC := by
      rcases hb.2.2.2.1 n with h | ⟨q, hq, h1, h2⟩
      · exact .inl (hcmZ ▸ h)
      · exact .inr ⟨q, hq, by rw [hx.d1] at h1; exact Int.le_trans h1 htge, hcmZ ▸ h2⟩
    tlDom := fun q hq => ⟨q, hq, rfl, Int.le_refl _⟩
    chainG := hgo.2.2.2.2.1
    tlG := hgo.2.2.2.2.2.1
    logG := hx.logG
    cmono := .inl rfl
    hconf := fun l hl => hb.2.2.2.2.1 n l hl
    lpart := fun h => absurd h hnl
    cpart := hcp
    hpend := ha.hpend
    hxpend := ha.hxpend
    hqs := hqs
    drain := ha.drain
    hlead := ha.hlead
    hvself := hx.hvs1
    rnf := by
      intro hf ht
      rw [get!_set_self _ hn3] at hf
      rw [hx.d5]; intro h'
      have hpf : r₁.p.role ≠ .follower := fun e => hf (by rw [e]; rfl)
      have hvt : r₁.p.term = (V n).ps.term := uint_Z_inj.mp (by rw [ht, hx.d1])
      exact hrnf hpf hvt ((roleOf_follower_iff _).mp h')
    tlMono := fun _ => Int.le_refl _
    tlNew := fun _ h => absurd h (Int.lt_irrefl _)
    tlSelf := fun h => absurd ((roleOf_leader_iff _).mp ((get!_set_self _ hn3).symm.trans h)) hnl
    lconf := hb.ledConfOk
    tlSort := hb.tlSorted }

/-! ## A follower's store or commit on a request -/

/-- **`ReadyOk` of a follower's `Ready` on a request** (`store`, `hb`): the term the request's (kept
or adopted, `FolTerm`), the vote kept or reset; the log `L1`, commit, confirmation `cf`, facts `M`
(the node's ack), `chain` and `termLen` as the kind's `OnDisk` gives them, with their fields. -/
theorem readyOk_fol (hx : RdCtx R dec S V net xnet evs G n r₁ rd S1)
    {m : Msg} {L1 : List Entry} {cf : Confirmed}
    {M : List Fact} {p : Pre} {ch : List Entry} {tl : TermFn Int}
    (hpr : r₁.p.role = .follower) (hft : FolTerm (V n).ps m r₁.p) (hpt : r₁.p.term = m.term)
    (hL1 : L1 = logOf r₁.p.log) (hcge : uint.Z (V n).ps.commit ≤ uint.Z r₁.p.commit)
    (hmsub : ∀ f ∈ S1.msgs, f ∈ M)
    (hmnew : ∀ f ∈ M, f ∉ S1.msgs → f.type = go!"ack" ∧ f.src = nameOf (nodeId n) ∧
      (∃ j : Fin R.N, f.dst = nameOf (nodeId j)) ∧ f.term = uint.Z r₁.p.term ∧
      ((cf.term = f.term ∧ f.index ≤ cf.index) ∨ f.index ≤ uint.Z r₁.p.commit))
    (hpm : PreOk S1 n.val L1 p)
    (hch : S1.chain <+: ch) (hchC : uint.Z r₁.p.commit ≤ ch.length ∧
      ch.take (uint.Z r₁.p.commit).toNat = L1.take (uint.Z r₁.p.commit).toNat)
    (htlL : ∀ q ∈ tl, q.2 ≤ ch.length)
    (htlC : uint.Z r₁.p.commit = 0 ∨ ∃ q ∈ tl, q.1 ≤ uint.Z r₁.p.term ∧ uint.Z r₁.p.commit ≤ q.2)
    (htlD : ∀ q ∈ S1.termLen, ∃ q' ∈ tl, q'.1 = q.1 ∧ q.2 ≤ q'.2)
    (hchG : ∃ c' ≤ G.committed.length, ch = logOf (G.committed.take c'))
    (htlG : ∀ q ∈ tl, 0 ≤ q.2 ∧ ∃ x, uint.Z x = q.1 ∧ (x, q.2.toNat) ∈ G.commits)
    (hcm : cf = S1.confirmed[n.val]! ∨
      (cf.term = uint.Z r₁.p.term ∧ S1.ledLog.has (uint.Z r₁.p.term) = true ∧
        ((S1.confirmed[n.val]!).term = uint.Z r₁.p.term → (S1.confirmed[n.val]!).index ≤ cf.index)))
    (hconf : ∀ l, S1.ledLog.get cf.term = .ok l →
      cf.index ≤ L1.length ∧ cf.index ≤ l.length ∧ L1.take cf.index.toNat = l.take cf.index.toNat)
    (htlM : ∀ T, tlOld S1.termLen T ≤ tlOld tl T)
    (htlN : ∀ T, tlOld S1.termLen T < tlOld tl T → T = uint.Z r₁.p.term ∧
      (∃ l ∈ S1.leaders, l.term = uint.Z r₁.p.term) ∧
      ∀ k : Fin R.N, k ≠ n → S1.role[k.val]! = leader → S1.currentTerm[k.val]! = uint.Z r₁.p.term →
        tlOld tl (uint.Z r₁.p.term) ≤ S1.commitIndex[k.val]!)
    (htlS : tl.Pairwise (fun a b => a.1 < b.1)) :
    ReadyOk R dec S1 V net G n ((V n).afterReady r₁ rd) (uint.Z r₁.p.term) none L1
      (uint.Z r₁.p.commit) (S1.role.set n.val (roleOf r₁.p.role)) cf M S1.votes
      S1.leaders S1.ledLog p ch tl S1.viol (memNL S1 n.val (roleOf r₁.p.role)) := by
  have hb := hx.hs1.2.1
  have ha := hx.ha
  have hrl : S1.role.length = R.N := hx.rlen
  have hn3 := hx.hn3
  have hnl : r₁.p.role ≠ .leader := by rw [hpr]; decide
  exact {
    hterm := rfl
    tge := by
      rw [hx.d1]; rcases hft with ⟨h, -⟩ | ⟨h, -, -⟩
      · rw [hpt]; exact Int.le_of_lt h
      · rw [hpt, h]; exact Int.le_refl _
    hvote := by
      rcases hft with ⟨h1, h2⟩ | ⟨h1, -, h2⟩
      · exact .inr ⟨by rw [hx.d1, hpt]; exact h1, h2⟩
      · exact .inl ⟨by rw [hx.d1, hpt, h1], by rw [hx.d2]; show _ = nameOf r₁.p.vote; rw [h2]⟩
    hlog := hL1
    hcommit := rfl
    cge := by rw [hx.d4]; exact hcge
    hrole := by rw [get!_set_self _ hn3]; rfl
    rlen := by rw [List.length_set, hrl]
    rother := fun k hk => get!_set_ne _ _ (fun h => hk (Fin.ext h))
    rstay := by
      intro hl ht
      rw [hx.d5, roleOf_leader_iff] at hl
      rcases hft with ⟨h, -⟩ | ⟨-, h, -⟩
      · rw [hx.d1, hpt] at ht; rw [ht] at h; exact absurd h (Int.lt_irrefl _)
      · exact absurd hl h
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
    logG := hx.logG
    cmono := hcm
    hconf := hconf
    lpart := fun h => absurd h hnl
    cpart := fun h => absurd (h.symm.trans hpr) (by decide)
    hpend := ha.hpend
    hxpend := ha.hxpend
    hqs := fun q hq => (qs_follower hx.hro hx.hso hpr q hq).elim
    drain := ha.drain
    hlead := ha.hlead
    hvself := fun h => absurd hpr h
    rnf := fun hf _ => absurd (by rw [get!_set_self _ hn3, hpr]; rfl) hf
    tlMono := htlM
    tlNew := htlN
    tlSelf := fun h => absurd ((roleOf_leader_iff _).mp ((get!_set_self _ hn3).symm.trans h)) hnl
    lconf := hb.ledConfOk
    tlSort := htlS }

end ctx

/-! ## A request's guards from raft's log facts -/

theorem prev_of_match {S : State} {n : Fin R.N} {l : List EntryM} {m : Msg}
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

theorem hf_of_match {S : State} {n : Fin R.N} {l : List EntryM} {m : Msg}
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

theorem hasFirst_of_match {S : State} {n : Fin R.N} {l : List EntryM} {m : Msg}
    (hlog : S.log[n.val]! = logOf l) (hpay : AppPayloadOk m) (K : Nat) (hK : K ≤ m.entries.length)
    (h : ∀ (k : Nat) (e : EntryM), k < K → m.entries[k]? = some e → PlogMatches base0 l (entId e)) :
    S.hasFirst n.val (afOf m (nodeId n)) (K : Int) = .ok true := by
  have h0 : 0 ≤ (afOf m (nodeId n)).prevLogIndex := by unfold afOf; simp only; word
  rw [hasFirst_eq _ _ _ h0 K (by unfold afOf; simp only; rw [logOf_length]; exact hK)]
  congr 1
  refine decide_eq_true fun q hq => ?_
  have he : m.entries[q]? = some m.entries[q] := List.getElem?_eq_getElem (by omega)
  exact hf_of_match hlog hpay he (h q _ hq he)

theorem prevOk_of_match {S : State} {n : Fin R.N} {l : List EntryM} {m : Msg}
    (hlog : S.log[n.val]! = logOf l) (h : PlogMatches base0 l (entryID.mk m.logterm m.index)) :
    S.prevOk n.val (afOf m (nodeId n)) = .ok true := by
  have h0 : 0 ≤ (afOf m (nodeId n)).prevLogIndex := by unfold afOf; simp only; word
  rw [prevOk_eq _ _ _ h0]
  exact congrArg _ (decide_eq_true (prev_of_match hlog h))

/-! ## The kinds of a non-leader's `Ready` -/

set_option maxHeartbeats 2000000 in
/-- **`antSim_ready` from the context**, a store from a conflict and the leader kinds as premises. -/
theorem ready_main {S : State} {V : Fin R.N → NodeView} {net : List Msg} {evs : List Event}
    {G : RaftFacts} {n : Fin R.N} {r₁ : RState} {rd : ReadyD} {S1 : State}
    (hx : RdCtx R dec S V net xnet evs G n r₁ rd S1)
    (hstoreB : ∀ m : Msg, RecvAt (nodeId n) net (V n) m → m.ty = .app → FolTerm (V n).ps m r₁.p →
      r₁.p.term = m.term → r₁.p.role = .follower → uint.Z (V n).ps.commit ≤ uint.Z m.index →
      PlogMatches base0 (V n).ps.log (entryID.mk m.logterm m.index) →
      (∃ (d : Nat) (e : EntryM), m.entries[d]? = some e ∧ rd.ents = m.entries.drop d ∧
        ¬ PlogMatches base0 (V n).ps.log (entId e) ∧
        (∀ (k : Nat) (e' : EntryM), k < d → m.entries[k]? = some e' →
          PlogMatches base0 (V n).ps.log (entId e')) ∧
        uint.Z e.Index' = uint.Z m.index + (d : Int) + 1 ∧
        uint.Z e.Index' ≤ ((V n).ps.log.length : Int) + 1 ∧
        r₁.p.log = (V n).ps.log.take (uint.nat e.Index' - 1) ++ rd.ents) →
      (r₁.p.commit = (V n).ps.commit ∨ (uint.Z (V n).ps.commit < uint.Z r₁.p.commit ∧
        uint.Z r₁.p.commit ≤ uint.Z m.commit ∧
        uint.Z r₁.p.commit ≤ uint.Z m.index + (m.entries.length : Int))) →
      ReadyGoal R dec V net xnet evs G n r₁ rd)
    (hwin : ∀ (src : w64) (rej : Bool) (mt : GMap w64 w64), (V n).ps.role = .candidate →
      ((∃ m, RecvAt (nodeId n) net (V n) m ∧ m.ty = .voteResp ∧ m.term = (V n).ps.term ∧ m.src = src ∧
          m.reject = rej) ∨
        (src = nodeId n ∧ rej = false ∧ ∃ q ∈ (V n).qs, q.ty = .voteResp)) →
      JQuorum (CfgM.simple R.voters0 ∅) (granted (recordVote (V n).ps.votes src (!rej))) →
      LeaderMatchOk (nodeId n) (V n).ps mt →
      LeadC (CfgM.simple R.voters0 ∅) (nodeId n)
        (pwinState (nodeId n) { (V n).ps with votes := recordVote (V n).ps.votes src (!rej) } mt) r₁.p →
      rd.ents = [pleaderEntry (V n).ps] → r₁.p.commit = (V n).ps.commit →
      ReadyGoal R dec V net xnet evs G n r₁ rd)
    (hprop : ∀ es : List EntryM, (V n).byE = go!"propose" → (V n).ps.role = .leader → es ≠ [] →
      rd.ents = es.mapIdx (stamp (V n).ps.term (plastIndex (V n).ps)) → r₁.p.log = (V n).ps.log ++ rd.ents →
      r₁.p.role = .leader → r₁.p.term = (V n).ps.term → r₁.p.vote = (V n).ps.vote →
      r₁.p.commit = (V n).ps.commit → ReadyGoal R dec V net xnet evs G n r₁ rd)
    (hcmt : (V n).ps.role = .leader → r₁.p.role = .leader → r₁.p.term = (V n).ps.term →
      r₁.p.vote = (V n).ps.vote → r₁.p.log = (V n).ps.log → rd.ents = [] →
      uint.Z (V n).ps.commit < uint.Z r₁.p.commit → CmtOk (CfgM.simple R.voters0 ∅) r₁.p r₁.p.commit →
      NoSelf (nodeId n) r₁.p → ReadyGoal R dec V net xnet evs G n r₁ rd) :
    ReadyGoal R dec V net xnet evs G n r₁ rd := by
  have hs1 := hx.hs1
  have hgo1 := hx.hgo1
  have hl := hx.hl
  have hb := hs1.2.1
  have hnet := hs1.2.2.1
  have hno := hs1.2.2.2.2
  have hc := hx.hc
  have hn3 := hx.hn3
  have hct3 := hx.hct3
  have hlg3 := hx.hlg3
  have d1 := hx.d1
  have d2 := hx.d2
  have d3 := hx.d3
  have d4 := hx.d4
  have d7 := hx.d7
  have d8 := hx.d8
  have d9 := hx.d9
  have hq0 := hx.hq0
  have hqs := hx.hqs
  have hso := hx.hso
  have hvs := hx.hvs
  have hrf := hx.hrf
  have hr := hx.hr
  have hro := hx.hro
  have htold := hx.htold
  have htb := hx.htb
  have hbyE := reach_byE hr hro hx.hrep
  -- the sender of a received message: another node, at a term it has
  have hsender : ∀ m, RecvAt (nodeId n) net (V n) m → ∃ i : Fin R.N, i ≠ n ∧ m.src = nodeId i ∧
      uint.Z m.term ≤ S1.currentTerm[i.val]! := by
    intro m hm
    obtain ⟨-, ⟨i, hi, hti⟩, -⟩ := hnet.1 m hm.2.2.1
    refine ⟨i, fun h => ?_, hi, hti.resolve_left (hx.hin m hm.2.2.1).notPre⟩
    subst h
    exact (hnet.2.2.1 m hm.2.2.1).2.1 (by rw [hi, hm.2.2.2.1])
  unfold ReadyGoal
  cases hx.hk with
  | demote hvc hpr hpt hpv hpl hpc hen =>
    rw [hen, hpr]
    have hm := inMemory_nl_eq n hc (V n).byE hbyE .follower (by decide) r₁.p.term r₁.p.vote r₁.p.commit []
      (fun h => by cases h)
    obtain ⟨p, hpm, hod⟩ := onDisk_same n hc (V n).byE .follower r₁.p.term r₁.p.vote r₁.p.commit
      (if (V n).byE = go!"recv" then S1.pending[n.val]! else []) (S1.role.set n.val (roleOf .follower))
      S1.leaders S1.ledLog S1.chain S1.termLen S1.viol (by decide) (by rw [hpt, d1]) (by rw [hpv, d2])
      (by rw [hpc, d4]) (get!_set_self _ hn3)
    have hok := readyOk_plain hx (vo := none) (M := S1.msgs) (Vs := S1.votes) (p := p)
      (by rw [hpr]; decide) hpl hpc (by rw [hpt]; exact Int.le_refl _)
      (fun h => by rw [hvc] at h; cases h) (.inl ⟨hpt, hpv⟩) (fun f hf => hf)
      (fun f hf hn => absurd hf hn) (fun y hy => hy) (fun y hy hn => absurd hy hn)
      (fun h => absurd rfl h) hpm (fun h => absurd (h.symm.trans hpr) (by decide))
      (fun q hq => (qs_follower hro hso hpr q hq).elim) (fun h _ => absurd hpr h)
    rw [hpr] at hok
    exact hx.finish (ready_of hq0 hm rfl (queued_ready ..) hod) hok
  | camp hbe hnl0 hpt hpv hpr hpl hpc hen =>
    rw [hen, hpv, hpr]
    have htz : uint.Z r₁.p.term = uint.Z (V n).ps.term + 1 := by
      rw [hpt]; have := htb; word
    have hbtl : S1.bootTerm < uint.Z r₁.p.term := by
      have h0 := hb.bootTermOk.1 n; rw [d1] at h0; omega
    obtain ⟨hvot, hvo0⟩ := camp_votes hr d7 hqs hbe hpt hpr
    have hvo : nodeId n ∈ R.voters0 := by
      unfold CfgM.voters CfgM.simple at hvo0
      rcases (GMap.elem_of_union _ _ _).mp hvo0 with h | h
      · exact h
      · exact absurd h (GMap.not_elem_of_empty _)
    have hm := inMemory_nl_eq n hc (V n).byE hbyE .candidate (by decide) r₁.p.term (nodeId n)
      r₁.p.commit [] (fun _ => by rw [hx.hconf]; exact cin_has_voter n hvo hx.hcf)
    obtain ⟨p, hpm, hod⟩ := onDisk_camp n hc (V n).byE r₁.p.term r₁.p.commit (S1.role.set n.val (roleOf .candidate))
      S1.leaders S1.ledLog S1.chain S1.termLen S1.viol (by rw [htz, d1]) (by rw [hpc, d4])
      (get!_set_self _ hn3)
    have hok := readyOk_plain hx (vo := some (nameOf (nodeId n)))
      (M := lset.add S1.msgs (S1.voteRequest n.val (uint.Z r₁.p.term)))
      (Vs := lset.add S1.votes { voter := nameOf (nodeId n), term := uint.Z r₁.p.term, cand := nameOf (nodeId n) })
      (p := p) (by rw [hpr]; decide) hpl hpc (by rw [htz]; omega) (fun h => absurd h hnl0)
      ⟨by rw [hpv], hbtl⟩
      (fun f hf => mem_lset_add.mpr (.inl hf))
      (fun f hf hn => by
        rcases mem_lset_add.mp hf with h | h
        · exact absurd h hn
        · rw [h]; exact ⟨rfl, hbtl⟩)
      (fun y hy => mem_lset_add.mpr (.inl hy))
      (fun y hy hn => by
        rcases mem_lset_add.mp hy with h | h
        · exact absurd h hn
        · rw [hpv]; exact ⟨h, nodeId_ne_zero n⟩)
      (fun _ => by rw [hpv]; exact mem_lset_add.mpr (.inr rfl)) hpm
      (fun _ => by
        refine ⟨fun j hj => ?_, ?_⟩
        · change r₁.p.votes !! nodeId j = some true at hj
          rw [hvot, GMap.lookup_empty] at hj; cases hj
        · rw [rS_ct, get!_set_self _ hct3, rS_msgs]
          refine mem_lset_add.mpr (.inr ?_)
          unfold State.voteRequest State.lastTerm
          rw [rS_cfg, rS_log, get!_set_self _ hlg3])
      (fun q hq => by
        obtain ⟨⟨h1, h2, h3, h4, -⟩, hk⟩ := qs_self hro hso q hq
        rcases hk with ⟨h, -⟩ | ⟨-, rfl⟩
        · rw [hpr] at h; cases h
        · refine ⟨h1, h2, h4, .inl ⟨h3, .inr ⟨rfl, ?_⟩⟩⟩
          rw [rS_votes]; exact mem_lset_add.mpr (.inr rfl))
      (fun h ht => by rw [ht] at htz; omega)
    rw [hpr] at hok
    exact hx.finish (ready_of hq0 hm rfl (queued_other _ _ _ _ _ _ _ _ _
      (by rcases hbe with h | h <;> rw [h] <;> decide)) hod) hok
  | adopt m hm hlt hpt hpv hpr hpl hpc hen =>
    rw [hen, hm.1, hpv, hpr]
    have hpend := pending_of (hno n) (htold hm.1) hm.2.1
    obtain ⟨i, hin', hsi, hti⟩ := hsender m hm
    have hm' := inMemory_nl_eq n hc go!"recv" (hm.1 ▸ hbyE) .follower (by decide) r₁.p.term (W64 0)
      r₁.p.commit [] (fun h => by cases h)
    obtain ⟨p, hpm, hod⟩ := onDisk_adopt n hc r₁.p.term r₁.p.commit m (S1.role.set n.val (roleOf .follower))
      S1.leaders S1.ledLog S1.chain S1.termLen S1.viol hpt.symm (by rw [d1, hpt]; exact hlt)
      ⟨i, hin', by rw [hpt]; exact hti⟩ (by rw [hpc, d4]) (get!_set_self _ hn3)
    have hok := readyOk_plain hx (vo := none) (M := S1.msgs) (Vs := S1.votes) (p := p)
      (by rw [hpr]; decide) hpl hpc (by rw [hpt]; exact Int.le_of_lt hlt)
      (fun _ h => by rw [h, hpt] at hlt; exact absurd hlt (Int.lt_irrefl _))
      (.inr ⟨by rw [hpt]; exact hlt, hpv⟩) (fun f hf => hf)
      (fun f hf hn => absurd hf hn) (fun y hy => hy) (fun y hy hn => absurd hy hn)
      (fun h => absurd rfl h) hpm (fun h => absurd (h.symm.trans hpr) (by decide))
      (fun q hq => (qs_follower hro hso hpr q hq).elim) (fun h _ => absurd hpr h)
    rw [hpr] at hok
    exact hx.finish (ready_of hq0 hm' rfl (queued_recv _ _ _ _ _ _ _ _ _ hpend) hod) hok
  | grant m hm hty hTT hutd hpt hpv hpr hpl hpc hen =>
    rw [hen, hm.1, hpv, hpr]
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
    have hm' := inMemory_nl_eq n hc go!"recv" (hm.1 ▸ hbyE) .follower (by decide) r₁.p.term m.src
      r₁.p.commit [] (fun h => by cases h)
    obtain ⟨p, hpm, hod⟩ := onDisk_grant n hc r₁.p.term r₁.p.commit m (S1.role.set n.val (roleOf .follower))
      S1.leaders S1.ledLog S1.chain S1.termLen S1.viol hty hpt.symm
      (by rw [hsi]; exact nameOf_ne_nil i)
      (by
        rcases hTT with h | ⟨h1, h2, -⟩
        · exact .inr ⟨by rw [d1, hpt]; exact h, i, hin', by rw [hpt]; exact hti⟩
        · refine .inl ⟨by rw [d1, hpt, h1], ?_⟩
          rw [d2, h2]; rfl)
      (by rw [hpc, d4]) (get!_set_self _ hn3) hvf (upToDate_of d3 d9 (d8 ▸ hutd))
    have hok := readyOk_plain hx (vo := some (nameOf m.src)) (M := S1.msgs)
      (Vs := lset.add S1.votes { voter := nameOf (nodeId n), term := uint.Z r₁.p.term, cand := nameOf m.src })
      (p := p) (by rw [hpr]; decide) hpl hpc (by rw [hpt, ← d1]; exact hle)
      (fun hl0 h => by
        rcases hTT with h' | ⟨-, h2, -⟩
        · rw [h, hpt] at h'; exact absurd h' (Int.lt_irrefl _)
        · have := hvs (by rw [hl0]; decide); rw [h2] at this
          exact nodeId_ne_zero n this.symm)
      ⟨by rw [hpv], by rw [hpt]; exact hb.bootTermOk.2 _ (List.contains_iff_mem.mp hvf) rfl⟩
      (fun f hf => hf) (fun f hf hn => absurd hf hn)
      (fun y hy => mem_lset_add.mpr (.inl hy))
      (fun y hy hn => by
        rcases mem_lset_add.mp hy with h | h
        · exact absurd h hn
        · rw [hpv]; exact ⟨h, by rw [hsi]; exact nodeId_ne_zero i⟩)
      (fun _ => by rw [hpv]; exact mem_lset_add.mpr (.inr rfl)) hpm
      (fun h => absurd (h.symm.trans hpr) (by decide))
      (fun q hq => (qs_follower hro hso hpr q hq).elim) (fun h _ => absurd hpr h)
    rw [hpr] at hok
    exact hx.finish (ready_of hq0 hm' rfl (queued_recv _ _ _ _ _ _ _ _ _ hpend) hod) hok
  | hb m hm hty hft hpt hpr hpl hlt hpc hen =>
    rw [hen, hm.1, hpr]
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
    have hlogn : S1.log[n.val]! = logOf r₁.p.log := by rw [d3, hpl]
    have hcL : uint.Z r₁.p.commit ≤ r₁.p.log.length := by
      have := nat_commit_le hrf; rwa [hx.hfl] at this
    have hold : S1.commitIndex[n.val]! < uint.Z r₁.p.commit := by rw [d4]; exact hlt
    have hcbc : (S1.confirmed[n.val]!).term = uint.Z r₁.p.term ∧
        uint.Z r₁.p.commit ≤ (S1.confirmed[n.val]!).index := by
      rcases hnet.2.1 m hm.2.2.1 hty n hm.2.2.2.1 hle with ⟨h1, h2⟩ | h
      · rw [hpt, hpc]; exact ⟨h1, h2⟩
      · rw [← hpc] at h; omega
    have hv : (nameOf r₁.p.vote != (if uint.Z r₁.p.term != S1.currentTerm[n.val]! then [] else S1.vote n.val))
        = false := by
      rcases hft with ⟨h1, h2⟩ | ⟨h1, -, h2⟩
      · have e : (uint.Z r₁.p.term != S1.currentTerm[n.val]!) = true := by
          rw [bne_iff_ne, d1, hpt]; omega
        rw [e, if_pos rfl, h2, nameOf_zero]; rfl
      · have e : (uint.Z r₁.p.term != S1.currentTerm[n.val]!) = false := by
          rw [d1, hpt, h1]; exact bne_self_eq_false _
        rw [e, if_neg (by simp), d2, h2]; exact bne_self_eq_false _
    have hm' := inMemory_nl_eq n hc go!"recv" (hm.1 ▸ hbyE) .follower (by decide) r₁.p.term r₁.p.vote
      r₁.p.commit [] (fun h => by cases h)
    have hcG : r₁.p.log.take (uint.nat r₁.p.commit) = G.committed.take (uint.nat r₁.p.commit) := by
      have := hrf.2.2.1; rwa [hx.hfl] at this
    obtain ⟨p, hpm, hod⟩ := onDisk_fhb n hc r₁.p.term r₁.p.vote r₁.p.commit m
      (S1.role.set n.val (roleOf .follower)) S1.leaders S1.ledLog S1.chain S1.termLen S1.viol hty hpt.symm
      (by rw [hpt]; exact hle) ⟨i, hin', by rw [hpt]; exact hti⟩ hv (get!_set_self _ hn3) hsd hold
      (by rw [hlogn, logOf_length]; exact hcL) (by rw [hpc]; exact Int.le_refl _) hcbc
      (by rw [hlogn]; exact cs_ok hgo1.2.2.2.2.1 hcG)
      (by rw [hlogn]; exact lc_ok hl hgo1.2.2.2.1 hrf.2.2.2.1 hcG (hx.boot1 (by have := hx.d1; rw [hpt]; omega)))
      (by rw [hlogn]; exact ch_ok hgo1.2.2.2.2.1 hcG)
    rw [hlogn] at hod hpm
    obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := commit_fields (n := n) (T := r₁.p.term) hb hgo1 hcL hcG hrf.2.1
      hrf.2.2.2.1 hold
    have hok := readyOk_fol hx (M := S1.msgs) (cf := S1.confirmed[n.val]!) hpr hft hpt
      rfl (Int.le_of_lt hlt) (fun f hf => hf) (fun f hf hn => absurd hf hn) hpm f1 f2 f3 f4 f5 f6 f7
      (.inl rfl) (fun l hl => by rw [← hlogn]; exact hb.2.2.2.2.1 n l hl)
      (fol_tl hs1 hgo1 hl hx.hdk hm.2.2.1 (.inr hty) hm.2.2.2.1 hle hpt (by rw [hpc]; exact Int.le_refl _)).1
      (fol_tl hs1 hgo1 hl hx.hdk hm.2.2.1 (.inr hty) hm.2.2.2.1 hle hpt (by rw [hpc]; exact Int.le_refl _)).2
      (with_sorted _ _ hb.tlSorted)
    rw [hpr] at hok
    exact hx.finish (ready_of hq0 hm' rfl (queued_recv _ _ _ _ _ _ _ _ _ hpend) hod) hok
  | store m hm hty hft hpt hpr hpc0 hprv hsl hcmv hchg =>
    have hpend := pending_of (hno n) (htold hm.1) hm.2.1
    obtain ⟨i, hin', hsi, hti⟩ := hsender m hm
    have hpay : AppPayloadOk m := (hnet.2.2.1 m hm.2.2.1).1 hty
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
    have hcL : uint.Z r₁.p.commit ≤ r₁.p.log.length := by
      have := nat_commit_le hrf; rwa [hx.hfl] at this
    have hv : (nameOf r₁.p.vote != (if uint.Z r₁.p.term != S1.currentTerm[n.val]! then [] else S1.vote n.val))
        = false := by
      rcases hft with ⟨h1, h2⟩ | ⟨h1, -, h2⟩
      · have e : (uint.Z r₁.p.term != S1.currentTerm[n.val]!) = true := by
          rw [bne_iff_ne, d1, hpt]; omega
        rw [e, if_pos rfl, h2, nameOf_zero]; rfl
      · have e : (uint.Z r₁.p.term != S1.currentTerm[n.val]!) = false := by
          rw [d1, hpt, h1]; exact bne_self_eq_false _
        rw [e, if_neg (by simp), d2, h2]; exact bne_self_eq_false _
    have hm' := inMemory_nl_eq n hc go!"recv" (hm.1 ▸ hbyE) .follower (by decide) r₁.p.term r₁.p.vote
      r₁.p.commit rd.ents (fun h => by cases h)
    have hcG : r₁.p.log.take (uint.nat r₁.p.commit) = G.committed.take (uint.nat r₁.p.commit) := by
      have := hrf.2.2.1; rwa [hx.hfl] at this
    have hlogv : S1.log[n.val]! = logOf (V n).ps.log := d3
    have hprev := prevOk_of_match hlogv hprv
    obtain ⟨l, hll, -⟩ := sendable_inv hsd
    rcases hsl with ⟨hen, hpl, hall⟩ | ⟨d, e, hed, hen, hncf, hbef, hidx, hile, hpl⟩
    · -- nothing stored: the commit moves
      rw [hm.1, hen, hpr]
      rw [hen] at hm'
      have hlogn : S1.log[n.val]! = logOf r₁.p.log := by rw [d3, hpl]
      obtain ⟨hlt, hcc, hcl⟩ : uint.Z (V n).ps.commit < uint.Z r₁.p.commit ∧
          uint.Z r₁.p.commit ≤ uint.Z m.commit ∧
          uint.Z r₁.p.commit ≤ uint.Z m.index + (m.entries.length : Int) := by
        rcases hcmv with h | h
        · rcases hchg with h' | h'
          · exact absurd hpl h'
          · exact absurd h h'
        · exact h
      have hold : S1.commitIndex[n.val]! < uint.Z r₁.p.commit := by rw [d4]; exact hlt
      have hfirst := hasFirst_of_match hlogv hpay m.entries.length (Nat.le_refl _)
        (fun k e _ he => hall k e he)
      obtain ⟨p, hpm, hod⟩ := onDisk_fcommit n hc r₁.p.term r₁.p.vote r₁.p.commit m
        (S1.role.set n.val (roleOf .follower)) S1.leaders S1.ledLog S1.chain S1.termLen S1.viol hty
        hpt.symm (by rw [hpt]; exact hle) ⟨i, hin', by rw [hpt]; exact hti⟩ hv (get!_set_self _ hn3) hsd
        hold (by rw [hlogn, logOf_length]; exact hcL) hcc hcl hprev hfirst
        (by rw [hlogn]; exact cs_ok hgo1.2.2.2.2.1 hcG)
        (by rw [hlogn]; exact lc_ok hl hgo1.2.2.2.1 hrf.2.2.2.1 hcG (hx.boot1 (by have := hx.d1; rw [hpt]; omega)))
        (by rw [hlogn]; exact ch_ok hgo1.2.2.2.2.1 hcG)
      rw [hlogn] at hod hpm
      obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := commit_fields (n := n) (T := r₁.p.term) hb hgo1 hcL hcG
        hrf.2.1 hrf.2.2.2.1 hold
      have hcfe : Confirmed.mk (uint.Z r₁.p.term) (fConfIdx S1 n.val false (uint.Z r₁.p.term)
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
      have hok := readyOk_fol hx (L1 := logOf r₁.p.log)
        (cf := Confirmed.mk (uint.Z r₁.p.term) (fConfIdx S1 n.val false (uint.Z r₁.p.term)
          (uint.Z m.index + m.entries.length)))
        (M := lset.add S1.msgs (ackFact (nameOf (nodeId n)) (nameOf m.src) (uint.Z r₁.p.term)
          (uint.Z m.index + m.entries.length)))
        hpr hft hpt rfl (Int.le_of_lt hlt) (fun f hf => mem_lset_add.mpr (.inl hf))
        (fun f hf hn => by
          rcases mem_lset_add.mp hf with h | h
          · exact absurd h hn
          · subst h
            refine ⟨rfl, rfl, ⟨i, by show nameOf m.src = _; rw [hsi]⟩, rfl, .inl ⟨rfl, ?_⟩⟩
            exact fConfIdx_ge S1 n.val false (uint.Z r₁.p.term) _)
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
          · obtain ⟨o1, o2, o3⟩ := hb.2.2.2.2.1 n l' (by rw [ht]; exact hll')
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
        (fol_tl hs1 hgo1 hl hx.hdk hm.2.2.1 (.inl hty) hm.2.2.2.1 hle hpt hcc).1
        (fol_tl hs1 hgo1 hl hx.hdk hm.2.2.1 (.inl hty) hm.2.2.2.1 hle hpt hcc).2
        (with_sorted _ _ hb.tlSorted)
      rw [hpr] at hok
      exact hx.finish (ready_of hq0 hm' rfl (queued_recv _ _ _ _ _ _ _ _ _ hpend) hod) hok
    · exact hstoreB m hm hty hft hpt hpr hpc0 hprv ⟨d, e, hed, hen, hncf, hbef, hidx, hile, hpl⟩ hcmv
  | win src rej mt h1 h2 h3 h4 h5 h6 h7 => exact hwin src rej mt h1 h2 h3 h4 h5 h6 h7
  | prop es h1 h2 h3 h4 h5 h6 h7 h8 h9 => exact hprop es h1 h2 h3 h4 h5 h6 h7 h8 h9
  | cmt h1 h2 h3 h4 h5 h6 h7 h8 h9 => exact hcmt h1 h2 h3 h4 h5 h6 h7 h8 h9

set_option maxHeartbeats 2000000 in
/-- **A follower's store** (`store` with entries from the first conflict): `onDisk_fstore`. -/
theorem ready_storeB {S : State} {V : Fin R.N → NodeView} {net : List Msg} {evs : List Event}
    {G : RaftFacts} {n : Fin R.N} {r₁ : RState} {rd : ReadyD} {S1 : State}
    (hx : RdCtx R dec S V net xnet evs G n r₁ rd S1)
    (m : Msg) (hm : RecvAt (nodeId n) net (V n) m) (hty : m.ty = .app)
    (hft : FolTerm (V n).ps m r₁.p) (hpt : r₁.p.term = m.term) (hpr : r₁.p.role = .follower)
    (hpc0 : uint.Z (V n).ps.commit ≤ uint.Z m.index)
    (hprv : PlogMatches base0 (V n).ps.log (entryID.mk m.logterm m.index))
    (hsl : ∃ (d : Nat) (e : EntryM), m.entries[d]? = some e ∧ rd.ents = m.entries.drop d ∧
        ¬ PlogMatches base0 (V n).ps.log (entId e) ∧
        (∀ (k : Nat) (e' : EntryM), k < d → m.entries[k]? = some e' →
          PlogMatches base0 (V n).ps.log (entId e')) ∧
        uint.Z e.Index' = uint.Z m.index + (d : Int) + 1 ∧
        uint.Z e.Index' ≤ ((V n).ps.log.length : Int) + 1 ∧
        r₁.p.log = (V n).ps.log.take (uint.nat e.Index' - 1) ++ rd.ents)
    (hcmv : r₁.p.commit = (V n).ps.commit ∨ (uint.Z (V n).ps.commit < uint.Z r₁.p.commit ∧
        uint.Z r₁.p.commit ≤ uint.Z m.commit ∧
        uint.Z r₁.p.commit ≤ uint.Z m.index + (m.entries.length : Int))) :
    ReadyGoal R dec V net xnet evs G n r₁ rd := by
  obtain ⟨d, e, hed, hen, hncf, hbef, hidx, hile, hpl⟩ := hsl
  have hs1 := hx.hs1
  have hgo1 := hx.hgo1
  have hl := hx.hl
  have hsh := hs1.1
  have hb := hs1.2.1
  have hnet := hs1.2.2.1
  have hno := hs1.2.2.2.2
  have hc := hx.hc
  have hn3 := hx.hn3
  have hlg3 := hx.hlg3
  have d1 := hx.d1
  have d2 := hx.d2
  have d3 := hx.d3
  have d4 := hx.d4
  have hq0 := hx.hq0
  have hrf := hx.hrf
  have htold := hx.htold
  have hbyE := reach_byE hx.hr hx.hro hx.hrep
  unfold ReadyGoal
  rw [hm.1]
  have hpend := pending_of (hno n) (htold hm.1) hm.2.1
  obtain ⟨i, hin', hsi, hti⟩ : ∃ i : Fin R.N, i ≠ n ∧ m.src = nodeId i ∧
      uint.Z m.term ≤ S1.currentTerm[i.val]! := by
    obtain ⟨-, ⟨i, hi, hti⟩, -⟩ := hnet.1 m hm.2.2.1
    refine ⟨i, fun h => ?_, hi, hti.resolve_left (hx.hin m hm.2.2.1).notPre⟩
    subst h
    exact (hnet.2.2.1 m hm.2.2.1).2.1 (by rw [hi, hm.2.2.2.1])
  have hpay : AppPayloadOk m := (hnet.2.2.1 m hm.2.2.1).1 hty
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
  have hcL : uint.Z r₁.p.commit ≤ r₁.p.log.length := by
    have := nat_commit_le hrf; rwa [hx.hfl] at this
  have hv : (nameOf r₁.p.vote != (if uint.Z r₁.p.term != S1.currentTerm[n.val]! then [] else S1.vote n.val))
      = false := by
    rcases hft with ⟨h1, h2⟩ | ⟨h1, -, h2⟩
    · have e : (uint.Z r₁.p.term != S1.currentTerm[n.val]!) = true := by
        rw [bne_iff_ne, d1, hpt]; omega
      rw [e, if_pos rfl, h2, nameOf_zero]; rfl
    · have e : (uint.Z r₁.p.term != S1.currentTerm[n.val]!) = false := by
        rw [d1, hpt, h1]; exact bne_self_eq_false _
      rw [e, if_neg (by simp), d2, h2]; exact bne_self_eq_false _
  have hcG : r₁.p.log.take (uint.nat r₁.p.commit) = G.committed.take (uint.nat r₁.p.commit) := by
    have := hrf.2.2.1; rwa [hx.hfl] at this
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
      logOf r₁.p.log := by
    rw [hpl, hents, hlogv, logOf_take, logOf, logOf, logOf, List.map_append]
    congr 3; omega
  have hm' := inMemory_nl_eq n hc go!"recv" (hm.1 ▸ hbyE) .follower (by decide) r₁.p.term r₁.p.vote
    r₁.p.commit rd.ents (fun h => by cases h)
  rw [hents] at hm'
  obtain ⟨eqb, heqb⟩ := entriesEqual_logOf r₁.p.log (V n).ps.log
  have hold0 : S1.commitIndex[n.val]! ≤ uint.Z r₁.p.commit := by
    rw [d4]; rcases hcmv with h | h
    · rw [h]; exact Int.le_refl _
    · exact Int.le_of_lt h.1
  obtain ⟨p, hpm, hod⟩ := onDisk_fstore n hc r₁.p.term r₁.p.vote r₁.p.commit m e (m.entries.drop (d + 1))
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
    (by rw [hL1eq]; exact lm_ok hl hx.logG hgo1.2.2.1 hsh.2.2.2.2.1)
    (by rw [hL1eq]; exact cs_ok hgo1.2.2.2.2.1 hcG)
    (by rw [hL1eq]; exact lc_ok hl hgo1.2.2.2.1 hrf.2.2.2.1 hcG (hx.boot1 (by have := hx.d1; rw [hpt]; omega)))
    (by rw [hL1eq]; exact ch_ok hgo1.2.2.2.2.1 hcG)
    (fun h => by rw [h]; exact (hb.2.2.1 n).1)
  rw [hL1eq] at hod hpm
  -- the acknowledgement's guard at the log after the write
  have hb0 : uint.Z (base0 : go_etcd_io.raft.v3.entryID).index' = 0 := rfl
  have hpm1 : PlogMatches base0 r₁.p.log (entryID.mk m.logterm m.index) := by
    show plogTermAt base0 r₁.p.log m.index = some m.logterm
    have h' : plogTermAt base0 (V n).ps.log m.index = some m.logterm := hprv
    by_cases hi0 : uint.Z m.index = 0
    · unfold plogTermAt at h' ⊢
      rw [hb0, if_neg (by omega), if_pos hi0] at h' ⊢; exact h'
    · rw [hpl, plog_take_append hjv (by omega), if_pos (by omega)]; exact h'
  have hpmk : ∀ (k : Nat) (x : EntryM), m.entries[k]? = some x → PlogMatches base0 r₁.p.log (entId x) := by
    intro k x hx
    have hxi := hpay.1 k x hx
    simp only at hxi; push_cast at hxi
    show plogTermAt base0 r₁.p.log x.Index' = some x.Term'
    rw [hpl, plog_take_append hjv (by omega)]
    by_cases hkd : k < d
    · rw [if_pos (by omega)]; exact hbef k x hkd hx
    · rw [if_neg (by omega), hen, List.getElem?_drop]
      have : d + (uint.Z x.Index' - ↑(uint.nat e.Index' - 1) - 1).toNat = k := by omega
      rw [this, hx]; rfl
  let S' : State := { S1 with log := S1.log.set n.val (logOf r₁.p.log) }
  have hlog' : S'.log[n.val]! = logOf r₁.p.log := get!_set_self _ hlg3
  have hgo' : GlobalOk R S' net G := by
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := hgo1
    refine ⟨g1, g2, fun k => ?_, g4, g5, g6, g7, g8, g9⟩
    by_cases hk : k = n
    · subst hk; exact ⟨r₁.p.log, hx.logG, hlog'⟩
    · show ∃ l ∈ G.logs, (S1.log.set n.val (logOf r₁.p.log))[k.val]! = logOf l
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
  have hcmono : (S1.confirmed[n.val]!).term = uint.Z r₁.p.term →
      (S1.confirmed[n.val]!).index ≤ uint.Z m.index + m.entries.length := by
    intro ht
    rw [hpt] at ht
    obtain ⟨o1, o2, o3⟩ := hb.2.2.2.2.1 n l (by rw [ht]; exact hll)
    refine Int.not_lt.mp fun hlt => hncf ?_
    rw [hlogv, logOf_length] at o1
    have hj : (uint.Z e.Index' - 1).toNat = uint.nat e.Index' - 1 := by omega
    have h1 := congrArg (·[(uint.Z e.Index' - 1).toNat]?) o3
    have h2 := congrArg (·[(uint.Z e.Index' - 1).toNat]?) m3
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_take_of_lt (by omega)] at h1
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_take_of_lt (by omega)] at h2
    rw [← h2, hlogv] at h1
    have h3 : (logOf r₁.p.log)[(uint.Z e.Index' - 1).toNat]? = some (entOf e) := by
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
  have hhas : S1.ledLog.has (uint.Z r₁.p.term) = true := by rw [hpt]; exact TermFn.has_of_get hll
  have hconf : ∀ l', S1.ledLog.get (Confirmed.mk (uint.Z r₁.p.term) (uint.Z m.index + m.entries.length)).term
      = .ok l' → (uint.Z m.index + m.entries.length : Int) ≤ (logOf r₁.p.log).length ∧
      (uint.Z m.index + m.entries.length : Int) ≤ l'.length ∧
      (logOf r₁.p.log).take (uint.Z m.index + (m.entries.length : Int)).toNat =
        l'.take (uint.Z m.index + (m.entries.length : Int)).toNat := by
    intro l' hl'
    change S1.ledLog.get (uint.Z r₁.p.term) = .ok l' at hl'
    have hll' : S1.ledLog.get (uint.Z m.term) = .ok l := hll
    rw [hpt, hll'] at hl'; cases hl'
    exact ⟨m1, m2, m3⟩
  rw [hpr, hents]
  by_cases hlt : S1.commitIndex[n.val]! < uint.Z r₁.p.commit
  · rw [if_pos hlt, if_pos hlt] at hod
    have hFT := fol_tl (cc := r₁.p.commit) hs1 hgo1 hl hx.hdk hm.2.2.1 (.inl hty) hm.2.2.2.1 hle hpt (by
      rcases hcmv with h | h
      · rw [d4, h] at hlt; exact absurd hlt (Int.lt_irrefl _)
      · exact h.2.1)
    obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := commit_fields (n := n) (T := r₁.p.term) hb hgo1 hcL hcG
      hrf.2.1 hrf.2.2.2.1 hlt
    have hok := readyOk_fol hx (L1 := logOf r₁.p.log)
      (cf := Confirmed.mk (uint.Z r₁.p.term) (uint.Z m.index + m.entries.length))
      (M := lset.add S1.msgs (ackFact (nameOf (nodeId n)) (nameOf m.src) (uint.Z r₁.p.term)
        (uint.Z m.index + m.entries.length)))
      hpr hft hpt rfl (by rw [← d4]; exact Int.le_of_lt hlt)
      (fun f hf => mem_lset_add.mpr (.inl hf))
      (fun f hf hn => by
        rcases mem_lset_add.mp hf with h | h
        · exact absurd h hn
        · subst h
          exact ⟨rfl, rfl, ⟨i, by show nameOf m.src = _; rw [hsi]⟩, rfl, .inl ⟨rfl, Int.le_refl _⟩⟩)
      hpm f1 f2 f3 f4 f5 f6 f7 (.inr ⟨rfl, hhas, hcmono⟩) hconf hFT.1 hFT.2 (with_sorted _ _ hb.tlSorted)
    rw [hpr] at hok
    exact hx.finish (ready_of hq0 hm' rfl (queued_recv _ _ _ _ _ _ _ _ _ hpend) hod) hok
  · rw [if_neg hlt, if_neg (fun h => hlt h.1), if_neg hlt] at hod
    have hceq : uint.Z r₁.p.commit = S1.commitIndex[n.val]! := by omega
    have hok := readyOk_fol hx (L1 := logOf r₁.p.log)
      (cf := Confirmed.mk (uint.Z r₁.p.term) (uint.Z m.index + m.entries.length))
      (M := S1.msgs) (ch := S1.chain) (tl := S1.termLen)
      hpr hft hpt rfl (by rw [← d4]; exact hold0)
      (fun f hf => hf) (fun f hf hn => absurd hf hn) hpm (List.prefix_refl _)
      ⟨by rw [hceq]; exact (hb.2.2.1 n).1,
        ch_ok hgo1.2.2.2.2.1 hcG (by rw [hceq]; exact (hb.2.2.1 n).1)⟩
      hb.2.1
      (by
        rcases hb.2.2.2.1 n with h | ⟨q, hq, h1, h2⟩
        · exact .inl (hceq ▸ h)
        · refine .inr ⟨q, hq, ?_, hceq ▸ h2⟩
          have := hle; rw [← hpt] at this; omega)
      (fun q hq => ⟨q, hq, rfl, Int.le_refl _⟩) hgo1.2.2.2.2.1 hgo1.2.2.2.2.2.1
      (.inr ⟨rfl, hhas, hcmono⟩) hconf (fun _ => Int.le_refl _) (fun _ h => absurd h (Int.lt_irrefl _))
      hb.tlSorted
    rw [hpr] at hok
    exact hx.finish (ready_of hq0 hm' rfl (queued_recv _ _ _ _ _ _ _ _ _ hpend) hod) hok

/-- **`antSim_ready` for every kind but a leader's** from the context (`win`, `prop`, `cmt` as
premises). -/
theorem ready_nonleader {S : State} {V : Fin R.N → NodeView} {net : List Msg} {evs : List Event}
    {G : RaftFacts} {n : Fin R.N} {r₁ : RState} {rd : ReadyD} {S1 : State}
    (hx : RdCtx R dec S V net xnet evs G n r₁ rd S1)
    (hwin : ∀ (src : w64) (rej : Bool) (mt : GMap w64 w64), (V n).ps.role = .candidate →
      ((∃ m, RecvAt (nodeId n) net (V n) m ∧ m.ty = .voteResp ∧ m.term = (V n).ps.term ∧ m.src = src ∧
          m.reject = rej) ∨
        (src = nodeId n ∧ rej = false ∧ ∃ q ∈ (V n).qs, q.ty = .voteResp)) →
      JQuorum (CfgM.simple R.voters0 ∅) (granted (recordVote (V n).ps.votes src (!rej))) →
      LeaderMatchOk (nodeId n) (V n).ps mt →
      LeadC (CfgM.simple R.voters0 ∅) (nodeId n)
        (pwinState (nodeId n) { (V n).ps with votes := recordVote (V n).ps.votes src (!rej) } mt) r₁.p →
      rd.ents = [pleaderEntry (V n).ps] → r₁.p.commit = (V n).ps.commit →
      ReadyGoal R dec V net xnet evs G n r₁ rd)
    (hprop : ∀ es : List EntryM, (V n).byE = go!"propose" → (V n).ps.role = .leader → es ≠ [] →
      rd.ents = es.mapIdx (stamp (V n).ps.term (plastIndex (V n).ps)) → r₁.p.log = (V n).ps.log ++ rd.ents →
      r₁.p.role = .leader → r₁.p.term = (V n).ps.term → r₁.p.vote = (V n).ps.vote →
      r₁.p.commit = (V n).ps.commit → ReadyGoal R dec V net xnet evs G n r₁ rd)
    (hcmt : (V n).ps.role = .leader → r₁.p.role = .leader → r₁.p.term = (V n).ps.term →
      r₁.p.vote = (V n).ps.vote → r₁.p.log = (V n).ps.log → rd.ents = [] →
      uint.Z (V n).ps.commit < uint.Z r₁.p.commit → CmtOk (CfgM.simple R.voters0 ∅) r₁.p r₁.p.commit →
      NoSelf (nodeId n) r₁.p → ReadyGoal R dec V net xnet evs G n r₁ rd) :
    ReadyGoal R dec V net xnet evs G n r₁ rd :=
  ready_main hx (fun m hm hty hft hpt hpr hpc0 hprv hsl hcmv =>
      ready_storeB hx m hm hty hft hpt hpr hpc0 hprv hsl hcmv) hwin hprop hcmt

end main

end AntSim
end EtcdGrove
end Perennial
