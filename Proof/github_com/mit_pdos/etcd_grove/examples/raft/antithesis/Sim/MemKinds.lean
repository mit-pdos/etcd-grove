/-
Lean-first (no Rocq counterpart).

# Parity B2: `memNode_lead`'s kind-dependent premises (#33 parity B2, Sim round 16)

At a `-parallel` leader's `mem` (no write queued, no split write), `memNode_lead` leaves the premises
that depend on the kind of the `Ready` (`ReadyKind`'s leader kinds: a win, a proposal, a commit):

- the term grown (`memLead_term`: every leader kind keeps the term, `kind_leadKeep`);
- the queued self-acknowledgement (`memLead_qs`: `QsAckW`, at the `Ready`'s last index, within the log
  of the disk with the queued write made), every kind;
- the handed-out entries a prefix of the disk (`memLead_pfx`) when the log extends the view's and the
  commit is within the view's log;
- the recorded commit (`memLead_mcKeep`) when the commit is kept (a win, a proposal);
- a proposal's leader part (`memLead_lpProp`): the `Match` values kept, the indices up to them of the
  old log (the leader's own by `SelfMatchLe`), whose acknowledgements the old part has.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.MemNode
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.ReadyProp
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.ReadyWin

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open GMap go_etcd_io.raft.v3 AntCheck

section memKinds
variable [GooseExts]
variable {R : RunCfg} {dec : CCDec} {S : State} {V : Fin R.N → NodeView} {net : List Msg}
  {xnet : List XMsg} {G : RaftFacts} {n : Fin R.N} {r : MemResult} {c : Int} {i : Int}
  {r₁ : RState} {rd : ReadyD}

/-- An acknowledgement of `k'` acknowledges every `k ≤ k'`. -/
theorem AckInX.le {N : Nat} {S : State} {n j : Fin N} {t k k' : Int} (h : AckInX S n j t k')
    (hk : k ≤ k') : AckInX S n j t k := by
  obtain ⟨a, ha, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨a, ha, h1, h2, h3, h4, Int.le_trans hk h5, h6⟩

/-- The disk's log is raft's (no write queued: `DiskFold`; snapshots off: no ghost prefix). -/
theorem LdCtx.dlog (hx : LdCtx R.syncOff dec V net xnet G n r₁ rd S) : (V n).dur.log = (V n).ps.log := by
  have hfp0 : (V n).r.fp = [] := (hx.hv.facts.snap0 hx.hsnf).2.1
  rw [hx.hdn]; show (V n).r.fp ++ (V n).r.p.log = _; rw [hfp0]; rfl

/-- **The term grown**: a leader's `Ready` keeps the term (`kind_leadKeep`). -/
theorem memLead_term (hx : LdCtx R.syncOff dec V net xnet G n r₁ rd S) (hrl : r₁.p.role = .leader) :
    uint.Z (V n).ps.term ≤ uint.Z r₁.p.term :=
  Int.le_of_eq (congrArg (fun t : w64 => uint.Z t) (kind_leadKeep hx.hk hrl).1).symm

/-- **The queued self-acknowledgement** waits for the write (`QsAckW`): at the `Ready`'s last index,
the log of the disk with the queued write made. -/
theorem memLead_qs (hx : LdCtx R.syncOff dec V net xnet G n r₁ rd S) (hrl : r₁.p.role = .leader)
    (hpar0 : (V n).parts = []) {S' : State} {P : List Msg} :
    ∀ q ∈ rd.qs, QsOk R S' n (memView (V n) r₁ rd P) q ∨ QsAckW n (memView (V n) r₁ rd P) q := by
  intro q hq
  right
  rcases (qs_self hx.hro hx.hso (by rw [hrl]; decide) q hq).2 with ⟨-, rfl⟩ | ⟨hc, -⟩
  · refine ⟨rfl, rfl, rfl, rfl, rfl, hrl, List.cons_ne_nil _ _, ?_⟩
    show uint.nat (plastIndex r₁.p) ≤
      (([rd.memRec (V n)] ++ (V n).parts).foldl DurW.write (V n).dur).log.length
    rw [hpar0]
    show _ ≤ ((V n).dur.write (rd.memRec (V n))).log.length
    rw [write_memRec hx.hro hx.hsn]
    show _ ≤ r₁.full.length
    rw [hx.hfl]
    have h1 := plastIndex_le r₁.p
    rw [hx.base1] at h1
    unfold plogLastIndexZ at h1
    have hb0 : uint.Z (base0 : go_etcd_io.raft.v3.entryID).index' = 0 := rfl
    rw [hb0] at h1
    have e : ((uint.nat (plastIndex r₁.p) : Nat) : Int) = uint.Z (plastIndex r₁.p) := by word
    omega
  · rw [hrl] at hc; cases hc

/-- **The handed-out entries a prefix of the disk** when the `Ready`'s log extends the view's and its
commit is within the view's log (`lead_pfx`). -/
theorem memLead_pfx (hx : LdCtx R.syncOff dec V net xnet G n r₁ rd S)
    (hlog : (V n).ps.log <+: r₁.p.log) (hc : uint.Z r₁.p.commit ≤ (V n).ps.log.length) :
    (V n).delivered ++ rd.ce <+: (V n).dur.log :=
  lead_pfx hx.hro hx.hfl hx.dlog hlog hc

/-- **The recorded commit, kept**: a `Ready` whose log extends the view's and whose commit is the
view's (a win, a proposal) keeps `MemCommitOk` (`chain` and `termLen` grow at a `mem`, `MemOk`). -/
theorem memLead_mcKeep (hs : AntSimD R dec S V net xnet) (hok : MemOk R dec S V G n r c)
    (hx : LdCtx R.syncOff dec V net xnet G n r₁ rd S) (hrl : r₁.p.role = .leader)
    (hpar0 : (V n).parts = []) (hlog : (V n).ps.log <+: r₁.p.log)
    (hpc : r₁.p.commit = (V n).ps.commit) {it : QItem} {P : List Msg} :
    MemCommitOk (memQ S r n.val it i) (memView (V n) r₁ rd P) := by
  intro _
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, d25⟩ := hs.2.2.2.2 n
  obtain ⟨m1, m2, m3⟩ := d25 hpar0
  have hcl := LdCtx.commit_le hx
  have hT := memLead_term hx hrl
  have hfp0 : (V n).r.fp = [] := (hx.hv.facts.snap0 hx.hsnf).2.1
  have hfull : (V n).r.full = (V n).ps.log := by
    show (V n).r.fp ++ (V n).r.p.log = _; rw [hfp0]; rfl
  obtain ⟨t, ht⟩ := hlog
  have hk' : uint.nat (V n).ps.commit ≤ S.chain.length := by word
  have hkl : uint.nat (V n).ps.commit ≤ (V n).ps.log.length := by word
  refine ⟨?_, ?_, ?_⟩
  · show uint.Z r₁.p.commit ≤ (r.chain.length : Int)
    have hl := hok.hchain.length_le
    rw [hpc]; omega
  · show r.chain.take (uint.nat r₁.p.commit) = (logOf r₁.full).take (uint.nat r₁.p.commit)
    rw [hpc, rr_take_prefix hok.hchain hk', m2, hx.hfl, ← ht, hfull]
    unfold logOf
    rw [List.map_append, List.take_append_of_le_length (by rw [List.length_map]; exact hkl)]
  · show r₁.p.commit = W64 0 ∨ ∃ p ∈ r.termLen, p.1 ≤ uint.Z r₁.p.term ∧ uint.Z r₁.p.commit ≤ p.2
    rw [hpc]
    rcases m3 with h | ⟨p, hp, h1, h2⟩
    · exact .inl h
    · obtain ⟨q', hq', e1, e2⟩ := hok.tlDom p hp
      exact .inr ⟨q', hq', by omega, by omega⟩

/-- **A proposal's leader part** at the `mem`: the `Match` values kept (`prop_matched`); an index up to
a `Match` of the leader's term is of the old log (the leader's own `Match` within it, `SelfMatchLe`;
another node's `0` or acknowledged), so acknowledged as the old part says; the leader log the
`mem`'s; the confirmation the old one (the disk unchanged). -/
theorem memLead_lpProp (hs : AntSimD R dec S V net xnet) (hok : MemOk R dec S V G n r c)
    (hx : LdCtx R.syncOff dec V net xnet G n r₁ rd S) (hvl : (V n).ps.role = .leader)
    (hrll : r.ledLog.get (uint.Z r₁.p.term) = .ok (logOf r₁.p.log))
    (hmt : r₁.p.matched = (V n).ps.matched) (hplog : r₁.p.log = (V n).ps.log ++ rd.ents)
    (hpt : r₁.p.term = (V n).ps.term) {it : QItem} {P : List Msg} :
    LeaderPartD (memQ S r n.val it i) n (memView (V n) r₁ rd P) := by
  intro _
  have hv := hs.2.2.2.2 n
  obtain ⟨l1, -, l3, l4, l5⟩ := hv.2.2.2.2.2.2.2.2.1 hvl
  have hsm := ((nodeOkD_factsS hv).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 hvl).1
  rw [hx.d8] at hsm
  unfold plogLastIndexZ at hsm
  have hb0 : uint.Z (base0 : go_etcd_io.raft.v3.entryID).index' = 0 := rfl
  rw [hb0, Int.zero_add] at hsm
  have hmo : ∀ j : Fin R.N, matchOf (accepted r₁).p (nodeId j) = matchOf (V n).ps (nodeId j) := by
    intro j; unfold matchOf; show (r₁.p.matched !! nodeId j).getD (W64 0) = _; rw [hmt]
  refine ⟨?_, ?_, fun j k hk hkt => ?_, fun j hj => ?_, ?_⟩
  · show r.leaders.contains { server := nameOf (nodeId n), term := uint.Z r₁.p.term } = true
    rw [hpt]; exact List.contains_iff_mem.mpr (hok.lsub _ (List.contains_iff_mem.mp l1))
  · show r.ledLog.get (uint.Z r₁.p.term) = .ok (logOf r₁.full)
    rw [hx.hfl]; exact hrll
  · change uint.Z k ≤ uint.Z (matchOf (accepted r₁).p (nodeId j)) at hk
    rw [hmo j] at hk
    have hkt' : plogTermAt base0 r₁.p.log k = some r₁.p.term := by
      change plogTermAt r₁.p.base r₁.p.log k = some r₁.p.term at hkt
      rw [hx.base1] at hkt; exact hkt
    show AckInX (memQ S r n.val it i) n j (uint.Z r₁.p.term) (uint.Z k)
    rw [hpt]
    by_cases hkL : uint.Z k ≤ (V n).ps.log.length
    · rw [hplog, plog_append_le hkL, hpt] at hkt'
      exact l3 j k hk (by rw [hx.d8]; exact hkt')
    · by_cases hjn : j = n
      · subst hjn; omega
      · rcases l4 j hjn with h0 | h1
        · exfalso; rw [h0] at hk; have : uint.Z (W64 0) = 0 := rfl; omega
        · exact h1.le hk
  · show matchOf (accepted r₁).p (nodeId j) = W64 0 ∨
      AckInX (memQ S r n.val it i) n j (uint.Z r₁.p.term) (uint.Z (matchOf (accepted r₁).p (nodeId j)))
    rw [hmo j, hpt]; exact l4 j hj
  · intro _
    show ((memQ S r n.val it i).confirmed[n.val]!).term = uint.Z r₁.p.term ∧
      ((V n).dur.log.length : Int) ≤ ((memQ S r n.val it i).confirmed[n.val]!).index
    rw [hpt]
    exact l5 (.inl (by rw [hx.hdn]; rfl))

/-! ## A win: the new leader's own `Match` is the old last index -/

/-- A leader's own `Match` at most `L0`. -/
def OwnLe (id : w64) (L0 : Int) (s : PState) : Prop :=
  s.role = .leader → uint.Z (matchOf s id) ≤ L0

section own
variable {kk : NodeK} {cf : CfgM} {id : w64} {L0 : Int}

theorem ownLe_ne {t : PState} (h : t.role ≠ .leader) : OwnLe id L0 t := fun hl => absurd hl h

theorem ownLe_win {s s' : PState} (h : WinEnd cf id s s') (hL : plogLastIndexZ s.base s.log ≤ L0) :
    OwnLe id L0 s' := by
  obtain ⟨mt, ms, hlm, -, rfl⟩ := h
  intro _
  show uint.Z ((mt !! id).getD (W64 0)) ≤ L0
  rw [hlm.1, Option.getD_some]; exact Int.le_trans (plastIndex_le s) hL

/-- From a non-leader, the type switch ends at a leader only by a win (at the state's last index). -/
theorem ownLe_handle {s s' : PState} {m : Msg} (hs : s.role ≠ .leader)
    (hL : plogLastIndexZ s.base s.log ≤ L0) (h : HandleEnd kk cf id s m s') : OwnLe id L0 s' := by
  unfold HandleEnd at h
  cases hm : m.ty <;> rw [hm] at h <;> simp only at h
  · rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact ownLe_ne hs
  · split at h
    · rcases h with ⟨-, rfl⟩ | ⟨-, hw⟩ | ⟨-, rfl⟩
      · exact ownLe_ne hs
      · exact ownLe_win hw hL
      · exact ownLe_ne (by simp [pbecomeFollower])
    · subst h; exact ownLe_ne hs
  · split at h
    · subst h; exact ownLe_ne hs
    · exact ownLe_ne (by rw [(appEnd_facts h).2.2]; simp [padoptLeader])
  · split at h
    · rename_i hl; exact absurd hl hs
    · subst h; exact ownLe_ne hs
  · split at h
    · subst h; exact ownLe_ne hs
    · subst h; exact ownLe_ne (by simp [psendMsgs, padoptLeader])
  · split at h
    · rename_i hl; exact absurd hl hs
    · subst h; exact ownLe_ne hs
  · unfold ProposeEnd at h
    split at h
    · rename_i hl; exact absurd hl hs
    · split at h
      · subst h; exact ownLe_ne hs
      · subst h; exact ownLe_ne hs
  · split at h
    · subst h; exact ownLe_ne hs
    · rcases h with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;>
        exact ownLe_ne (by simp [psendMsgs, padoptLeader])
  · rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact ownLe_ne hs
  · split at h
    · rcases h with rfl | ⟨-, peers, -, rfl⟩
      · exact ownLe_ne hs
      · exact ownLe_ne (by simp [psendMsgs, pbecomeCandidate])
    · subst h; exact ownLe_ne hs
  · exact ownLe_ne (by rw [(readIdxEnd_keep h).role]; exact hs)
  · exact ownLe_ne (by rw [(readResp_keep h id).1.2.2.2.1]; exact hs)

theorem ownLe_recv {s s' : PState} {m : Msg} (hs : s.role ≠ .leader)
    (hL : plogLastIndexZ s.base s.log ≤ L0) (h : RecvEnd kk cf id s m s') : OwnLe id L0 s' := by
  rcases h with ⟨-, hh⟩ | ⟨-, -, hst⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, hh⟩
  · exact ownLe_handle hs hL hh
  · rcases hst with rfl | ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact ownLe_ne hs
  · exact ownLe_ne hs
  · rcases hpre with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, rfl⟩
    · refine ownLe_handle ?_ ?_ hh
      · simp [pbecomeFollower]
      · exact hL
    · exact ownLe_handle hs hL hh
    · exact ownLe_handle hs hL hh

/-- `Advance` of self-votes from a state of last index at most `L0` while not leading. -/
theorem ownLe_adv {T : w64} {s s' : PState} {qs : List Msg} (h : AdvanceEnd kk cf id s qs s')
    (hq : ∀ q ∈ qs, SelfMsg id T q ∧ q.ty = .voteResp)
    (hi : OwnLe id L0 s ∧ (s.role ≠ .leader → plogLastIndexZ s.base s.log ≤ L0) ∧ s.term = T) :
    OwnLe id L0 s' := by
  induction h with
  | nil => exact hi.1
  | cons s s1 s' q qs hr _ ih =>
    refine ih (fun x hx => hq x (List.mem_cons_of_mem _ hx)) ?_
    obtain ⟨⟨-, -, hqt, -, -⟩, hty⟩ := hq q List.mem_cons_self
    obtain ⟨hO, hL, hT⟩ := hi
    have hh := recvEnd_self (.inr hty) (hqt.trans hT.symm) hr
    unfold HandleEnd at hh; rw [hty] at hh; simp only at hh
    split at hh
    · rename_i hc
      have hnl : s.role ≠ .leader := by rw [hc]; decide
      rcases hh with ⟨-, rfl⟩ | ⟨-, hw⟩ | ⟨-, rfl⟩
      · exact ⟨ownLe_ne hnl, fun _ => hL hnl, hT⟩
      · have hO' := ownLe_win (id := id) hw (hL hnl)
        obtain ⟨mt, ms, -, -, rfl⟩ := hw
        exact ⟨hO', fun h' => absurd rfl h', hT⟩
      · exact ⟨ownLe_ne (by simp [pbecomeFollower]), fun _ => hL hnl, hT⟩
    · subst hh; exact ⟨hO, hL, hT⟩

/-- **A non-leader's `Ready` state that leads** (a win) has its own `Match` at most the view's last
index: a win sets it to the last index then (the log unchanged before it), and a non-leader's queue
holds no acknowledgement. -/
theorem ownLe_reachP {net : List Msg} {xnet : List XMsg} {v : NodeView} {ps₁ : PState}
    (hvl : v.ps.role ≠ .leader) (hqs : ∀ q ∈ v.qs, q.ty ≠ .preVoteResp → SelfMsg id v.ps.term q)
    (hqv : ∀ q ∈ v.qs, q.ty ≠ .appResp) (hr : ReachP kk cf id net xnet v ps₁) :
    OwnLe id (plogLastIndexZ v.ps.base v.ps.log) ps₁ := by
  cases hr with
  | stay _ _ => exact ownLe_ne hvl
  | recv m _ _ _ _ _ _ _ _ hO => exact ownLe_recv hvl (Int.le_refl _) hO
  | recvP m _ _ _ _ _ _ _ _ _ hO => exact ownLe_recv hvl (Int.le_refl _) hO
  | tick _ _ _ ht =>
    rcases ht with rfl | ⟨-, -, hce⟩ | ⟨-, -, -, peers, -, rfl⟩ | ⟨hl, -⟩ | ⟨hl, -⟩
    · exact ownLe_ne hvl
    · obtain ⟨peers, -, rfl⟩ := hce.sends; exact ownLe_ne (by simp [psendMsgs, pbecomeCandidate])
    · exact ownLe_ne (by simp [psendMsgs])
    · exact absurd hl hvl
    · exact absurd hl hvl
  | propose d _ _ _ hh =>
    unfold ProposeEnd at hh
    split at hh
    · rename_i hl; exact absurd hl hvl
    · split at hh
      · subst hh; exact ownLe_ne hvl
      · subst hh; exact ownLe_ne hvl
  | read d _ _ _ hh => exact ownLe_ne (by rw [(readIdxEnd_keep hh).role]; exact hvl)
  | advance _ _ _ _ hno ha =>
    refine ownLe_adv ha (fun q hq => ⟨hqs q hq (hno q hq), ?_⟩) ⟨ownLe_ne hvl, fun _ => Int.le_refl _, rfl⟩
    rcases (hqs q hq (hno q hq)).2.2.2.2 with h | h
    · exact absurd h (hqv q hq)
    · exact h
  | advP _ _ _ _ _ _ _ ha =>
    rcases ha with rfl | ⟨-, -, peers, -, rfl⟩
    · exact ownLe_ne hvl
    · exact ownLe_ne (by simp [psendMsgs, pbecomeCandidate])
  | sends _ _ _ hl _ => exact absurd hl hvl
  | adoptX x _ _ _ _ _ _ => exact ownLe_ne (by simp [pbecomeFollower])
  | campX x p1 _ _ _ _ _ _ _ _ _ hc _ =>
    obtain ⟨peers, -, rfl⟩ := hc.sends; exact ownLe_ne (by simp [psendMsgs, pbecomeCandidate])

end own

/-- **A win's leader part** at the `mem`: the other nodes' `Match` values `0` (`LeaderMatchOk`), its
own the old last index (`ownLe_reachP`), and no index up to it is of the new term (the candidate's log
of earlier terms, `CandLt`, and the term past `0`); the leader log the `mem`'s; the confirmation's
premise false (the disk is the candidate's log). -/
theorem memLead_lpWin (hs : AntSimD R dec S V net xnet) (hok : MemOk R dec S V G n r c)
    (hx : LdCtx R.syncOff dec V net xnet G n r₁ rd S) (hvc : (V n).ps.role = .candidate)
    (hrll : r.ledLog.get (uint.Z r₁.p.term) = .ok (logOf r₁.p.log))
    (hplog : r₁.p.log = (V n).ps.log ++ [pleaderEntry (V n).ps])
    (hmo : ∀ j : Fin R.N, j ≠ n → matchOf r₁.p (nodeId j) = W64 0)
    (hct : S.currentTerm[n.val]! = uint.Z r₁.p.term) (hT0 : 0 < uint.Z r₁.p.term)
    (hpt : r₁.p.term = (V n).ps.term) {it : QItem} {P : List Msg} :
    LeaderPartD (memQ S r n.val it i) n (memView (V n) r₁ rd P) := by
  intro hrl
  have hrl' : r₁.p.role = .leader := hrl
  have hv := hs.2.2.2.2 n
  have hcl : CandLt (V n).ps := (nodeOkD_factsS hv).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hvnl : (V n).ps.role ≠ .leader := by rw [hvc]; decide
  have hown := ownLe_reachP hvnl hx.hqs
    (fun q hq ht => hvnl (qsD_lead (nodeOkD_qsS hv q hq) ht)) hx.hr hrl'
  rw [hx.d8] at hown
  unfold plogLastIndexZ at hown
  have hb0 : uint.Z (base0 : go_etcd_io.raft.v3.entryID).index' = 0 := rfl
  rw [hb0, Int.zero_add] at hown
  have hlt : ∀ e ∈ (V n).ps.log, uint.Z e.Term' < uint.Z r₁.p.term := fun e he => by
    rw [hpt]; exact hcl hvc e he
  refine ⟨?_, ?_, fun j k hk hkt => ?_, fun j hj => .inl (hmo j hj), ?_⟩
  · show r.leaders.contains { server := nameOf (nodeId n), term := uint.Z r₁.p.term } = true
    rw [← hct]; exact List.contains_iff_mem.mpr hok.lself
  · show r.ledLog.get (uint.Z r₁.p.term) = .ok (logOf r₁.full)
    rw [hx.hfl]; exact hrll
  · exfalso
    change uint.Z k ≤ uint.Z (matchOf r₁.p (nodeId j)) at hk
    have hkt' : plogTermAt base0 r₁.p.log k = some r₁.p.term := by
      change plogTermAt r₁.p.base r₁.p.log k = some r₁.p.term at hkt
      rw [hx.base1] at hkt; exact hkt
    have hkL : uint.Z k ≤ (V n).ps.log.length := by
      by_cases hjn : j = n
      · subst hjn; exact Int.le_trans hk hown
      · rw [hmo j hjn] at hk
        have : uint.Z (W64 0) = 0 := rfl
        have := List.length ((V n).ps.log) |>.zero_le
        omega
    rw [hplog, plog_append_le hkL] at hkt'
    have h2 := (termAt_of_plog hkt').2
    have h3 := termAt_lt_of (k := uint.Z k) hlt hT0
    omega
  · rintro (hd | ⟨e, he, het⟩)
    · exfalso
      have h1 := congrArg List.length hd
      change (V n).dur.log.length = r₁.full.length at h1
      rw [hx.dlog, hx.hfl, hplog, List.length_append] at h1
      simp at h1
    · exfalso
      change e ∈ (V n).dur.log at he
      rw [hx.dlog] at he
      have := hlt e he
      have e2 : r₁.p.term = e.Term' := het.symm
      rw [e2] at this
      exact Int.lt_irrefl _ this

end memKinds

end AntSim
end EtcdGrove
end Perennial
