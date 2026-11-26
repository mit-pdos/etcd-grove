/-
Lean-first (no Rocq counterpart). #33 parity B1, driver group E (`node.drain`): **the pure bridges
from raft's `Ready` to the Sim's reading** (S4's `DrainPure`, `DrainReports.readyOutP_of`, over
`RState`, `Fin R.N` and `mskB1`), independent of the `RawNode` API's mode argument:
- `roleStr_go`: Go `roleOf(s)` is the Sim's reported role of `s` (the pre-candidate flag and the
  protocol role `roleProto`);
- `readyDOf`: a `Ready`'s data as the harness reads it (`AntSim.ReadyD`), from raft's `Ready` post
  (the node's state `r`, the role after it, the entries, committed entries, messages, the queue,
  the read states): the protocol messages `absMsgOf`, the transfer messages `xmsgOf`, nothing
  held back (sync);
- `readyOutP_of`: raft's `ReadyOut` at a drain's loop head is the Sim's `ReadyOutP`, given the
  facts raft's `Ready` post does not state (see its premises);
- `reported_iff`: the drain's report test (`write || role != n.role`) is the Sim's `Reported`;
- `reach_ce`, `reachIn_b1`: a loop head's `Reach` (the `.loop` phase's) is a `ReachIn mskB1` over
  any later sent lists, in a run without conf changes and at a drain of the driver's `by`;
- `xPendOk_of`: a transfer message of a `Ready` is pending at the node (`XPendOk`), from raft's
  `XReadyOk` and its destination facts.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessReport
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Mono
public import Proof.go_etcd_io.raft.v3.RawNodeAbsSpecs

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-! ## Roles -/

/-- **Go `roleOf(s)` is the Sim's reported role of `s`**: `"precandidate"` exactly for
`StatePreCandidate`, otherwise the protocol role's string (`roleProto`; a value raft never reports
a follower, as in Go). -/
theorem roleStr_go (s : w64) :
    roleStr s = AntSim.roleStr (decide (s = StatePreCandidate)) (roleProto s) := by
  unfold roleStr AntSim.roleStr roleProto
  by_cases h1 : s = StateLeader
  · subst h1; simp [StateLeader, StateCandidate, StatePreCandidate, AntSim.roleOf]
  · by_cases h2 : s = StateCandidate
    · subst h2; simp [StateLeader, StateCandidate, StatePreCandidate, AntSim.roleOf]
    · by_cases h3 : s = StatePreCandidate
      · subst h3; simp [StateLeader, StateCandidate, StatePreCandidate]
      · simp [h1, h2, h3, AntSim.roleOf]

/-! ## A `Ready`'s data -/

/-- **A `Ready`'s data as the harness reads it** (`AntSim.ReadyD`), taken at the node's state `r`,
the role after it `s` (`roleAfter rs.role ss`): the protocol role and hard state `ReadyOut` reports
(`r.p`'s), a pre-candidate flag for `StatePreCandidate`, the entries `es`, the messages' protocol
readings (`absMsgOf`) and transfer readings (`xmsgOf`), none held back for the write (sync), the
queue `qs` `Advance` steps, the committed entries `ce`, the read states `sts`, no snapshot. -/
def readyDOf (r : RState) (s : w64) (es ce : List EntryM) (ms : List QMsg) (qs : List Msg)
    (sts : List ReadStateM) : AntSim.ReadyD :=
  { role := r.p.role, pre := decide (s = StatePreCandidate), term := r.p.term, vote := r.p.vote,
    commit := r.p.commit, ents := es, msgs := ms.filterMap (fun q => absMsgOf q.st), resp := [],
    xmsgs := ms.filterMap (fun q => xmsgOf q.st), qs := qs, ce := ce, reads := sts, snap := none }

/-- The reported role of `readyDOf` is Go's `roleOf` of the role after the `Ready`. -/
theorem readyDOf_roleStr {r : RState} {s : w64} {es ce : List EntryM} {ms : List QMsg}
    {qs : List Msg} {sts : List ReadStateM} (hrole : roleProto s = r.p.role) :
    AntSim.roleStr (readyDOf r s es ce ms qs sts).pre (readyDOf r s es ce ms qs sts).role =
      roleStr s := by
  rw [roleStr_go, hrole]; rfl

theorem lcpLen_take' : ∀ (l1 l2 : List EntryM), l1.take (lcpLen l1 l2) = l2.take (lcpLen l1 l2)
  | [], _ => by simp [lcpLen]
  | _ :: _, [] => by simp [lcpLen]
  | a :: xs, b :: ys => by
    unfold lcpLen
    split
    · rename_i h; subst h; simp [lcpLen_take' xs ys]
    · simp

theorem lcpLen_ne' : ∀ (l1 l2 : List EntryM) (a b : EntryM), l1[lcpLen l1 l2]? = some a →
    l2[lcpLen l1 l2]? = some b → a ≠ b
  | [], _, _, _ => by simp [lcpLen]
  | _ :: _, [], _, _ => by simp [lcpLen]
  | x :: xs, y :: ys, a, b => by
    unfold lcpLen
    split
    · intro h1 h2; exact lcpLen_ne' xs ys a b (by simpa using h1) (by simpa using h2)
    · rename_i hne
      intro h1 h2
      simp at h1 h2
      rw [← h1, ← h2]; exact hne

/-- No entries and no snapshot: the durable state's entries are kept. -/
theorem readyDurable_nil (S : RaftState) (h' : HardStateM) :
    (readyDurable S h' none []).ents = S.ents := by
  simp [readyDurable, RaftState.next, appendEnts]

/-- **`ReadyOut` at the protocol level** (`ReadyOutP`, S4's `readyOutP_of` over `RState`): raft's
`Ready` binding at a drain's loop head (the record against the view, `RsView`; no committed entries
left to report; the in-progress boundary at the common prefix of the view's log and the node's),
with what raft's `Ready` post says besides `ReadyOut` (the first entry at the boundary, the queue)
and the facts it does not state:
- `hpk`: a pre-candidate only with the node's pre-vote flag on (raft's invariant
  `s.role = .preCandidate → s.prevote = true`, not in `ReadyOut`);
- `hsts`: the read states handed out the node's (`r.p.rd.states`; not in `ReadyOut`);
- `hx`: the transfer messages pending at the node (`xPendOk_of`);
- `hfp`, `hdl`, `hsnap`, `hidx`: no ghost prefix, the disk's log the view's protocol log (the Sim's
  `SyncDisk`, `NodeFacts.snap0` with snapshots off), the outbox without snapshots from `base0`, the
  full log's indices its positions (a certified log, `raftFactsOwn`);
- `hmatch`: log matching between the disk's log and the node's (raft's laws: both certified);
- `hvot`: the messages' destinations servers (`msgShape`). -/
theorem readyOutP_of {R : AntSim.RunCfg} {n : Fin R.N} {v : AntSim.NodeView} {rs : RNState}
    {r : RState} {h : HardStateM} {es ce : List EntryM} {ms : List QMsg}
    {ss : Option (w64 × StateType)} {L : Option SnapLoan} {qs : List Msg} {sts : List ReadStateM}
    {ip : Nat}
    (hRs : RsView rs v) (hce : v.ce = []) (hfp : r.fp = []) (hdl : v.dur.log = v.r.p.log)
    (hip : ip = lcpLen v.r.p.log r.p.log)
    (hout : ReadyOut (AntSim.nodeId n) rs r.p h es ce ms ss L)
    (hfirst : ∀ e0 ∈ es.head?, uint.nat e0.Index' = ip + 1)
    (hqs : qs.Perm (r.p.outbox.filter (fun m => decide (m.dst = AntSim.nodeId n))))
    (hpk : roleAfter rs.role ss = StatePreCandidate → (R.k n).prevote = true)
    (hasync : R.md.async = false)
    (hx : ∀ x ∈ ms.filterMap (fun q => xmsgOf q.st), AntSim.XPendOk R.N (AntSim.nodeId n) r.p x)
    (hsts : sts = r.p.rd.states)
    (hsnap : R.md.snapshots = false → r.p.base = base0 ∧ ∀ q ∈ r.p.outbox, q.ty ≠ .snap)
    (hidx : AntSim.LogIdx r.full)
    (hmatch : ∀ (k : Nat) (e f : EntryM), v.dur.log[k]? = some e → r.full[k]? = some f →
      e.Term' = f.Term' → e = f)
    (hvot : ∀ q ∈ ms.filterMap (fun q => absMsgOf q.st), ∃ j : Fin R.N, q.dst = AntSim.nodeId j) :
    AntSim.ReadyOutP R n v r (readyDOf r (roleAfter rs.role ss) es ce ms qs sts) := by
  obtain ⟨⟨hrole, -⟩, -, hdur, hdrop, hmsgs, -, hdlv, hdlen, hL⟩ := hout
  obtain ⟨-, hents, hdel, -, -, -⟩ := hRs
  subst hL
  rw [hce, List.append_nil] at hdel
  have hfull : r.full = r.p.log := by simp [RState.full, hfp]
  rw [← hdl] at hip
  refine ⟨rfl, ?_, rfl, rfl, rfl, ?_, ?_, hqs, ?_, ?_, hx, ?_, ?_, hsts, ?_, hidx, ?_⟩
  · intro hpre
    simp only [readyDOf, decide_eq_true_eq] at hpre ⊢
    refine ⟨?_, hpk hpre⟩
    rw [← hrole, hpre]; simp [roleProto, StatePreCandidate, StateCandidate, StateLeader]
  · intro _ hnil
    simp only [readyDOf] at hnil
    subst hnil
    rw [hfull, ← hdur, readyDurable_nil, hents]
  · intro e0 he0
    simp only [readyDOf] at he0 ⊢
    have hi := hfirst e0 he0
    have hk : uint.nat e0.Index' - 1 = lcpLen v.dur.log r.p.log := by omega
    rw [hk, hfull]
    have hd := hdrop e0 he0
    rw [hk] at hd
    refine ⟨?_, ?_⟩
    · rw [lcpLen_take', ← hd, List.take_append_drop]
    · intro e he hte
      have hf : r.p.log[lcpLen v.dur.log r.p.log]? = some e0 := by
        have : (r.p.log.drop (lcpLen v.dur.log r.p.log))[0]? = some e0 := by
          rw [hd, ← List.head?_eq_getElem?]; exact he0
        simpa using this
      exact lcpLen_ne' _ _ e e0 he hf (hmatch _ e e0 he (by rw [hfull]; exact hf) hte)
  · intro _; exact ⟨rfl, hmsgs⟩
  · intro ha; rw [hasync] at ha; cases ha
  · rw [hfull, ← hdel]; exact hdlv
  · rw [← hdel]; exact hdlen
  · intro hs
    obtain ⟨hb, hq⟩ := hsnap hs
    exact ⟨hb, rfl, hq⟩
  · intro q hq
    simp only [readyDOf, List.append_nil] at hq
    exact hvot q hq

/-! ## The report test -/

/-- A hard state that is not empty (`!raft.IsEmptyHardState`): the drain takes the `Ready`'s. -/
def HsNew (h : HardStateM) : Prop := ¬ (h.Term' = W64 0 ∧ h.Vote' = W64 0 ∧ h.Commit' = W64 0)

/-- **The drain's report test is `Reported`** (S4's `goReport_iff`): the `Ready` writes (a hard
state that is not empty, which raft hands out only when it differs from the last, or entries) or
its role string `rolG` (Go's `role`: the `SoftState`'s `roleOf`, or `n.role`) differs from the
last reported one, exactly when the Sim's `Reported` holds of `readyDOf`. -/
theorem reported_iff {v : AntSim.NodeView} {rs : RNState} {r : RState} {h : HardStateM} {s : w64}
    {es ce : List EntryM} {ms : List QMsg} {qs : List Msg} {sts : List ReadStateM}
    {rolG : AntCheck.Str}
    (hRs : RsView rs v)
    (hph : phsNext rs.phs h = HardStateM.mk r.p.term r.p.vote r.p.commit)
    (hne : HsNew h → h ≠ rs.phs) (hrole : roleProto s = r.p.role) (hrg : rolG = roleStr s) :
    (HsNew h ∨ es ≠ [] ∨ rolG ≠ AntSim.roleS v) ↔
      AntSim.Reported v (readyDOf r s es ce ms qs sts) := by
  have hphs := hRs.1
  have hrs := readyDOf_roleStr (es := es) (ce := ce) (ms := ms) (qs := qs) (sts := sts) hrole
  unfold AntSim.Reported
  rw [hrs, ← hrg]
  simp only [readyDOf]
  by_cases hn : HsNew h
  · have hh : h = HardStateM.mk r.p.term r.p.vote r.p.commit := by
      rw [← hph]; unfold phsNext HsNew at *; simp only [hn, ↓reduceIte]
    have hd := hne hn
    rw [hh, hphs] at hd
    have : r.p.term ≠ v.dur.term ∨ r.p.vote ≠ v.dur.vote ∨ r.p.commit ≠ v.dur.commit := by
      refine Classical.byContradiction fun hc => ?_
      simp only [not_or, Classical.not_not] at hc
      exact hd (by rw [hc.1, hc.2.1, hc.2.2])
    constructor
    · intro _
      rcases this with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (Or.inl h1))
    · intro _; exact Or.inl hn
  · have hh : phsNext rs.phs h = rs.phs := by unfold phsNext HsNew at *; simp only [Classical.not_not.mp hn, and_self, ↓reduceIte]
    rw [hh, hphs] at hph
    simp only [HardStateM.mk.injEq] at hph
    obtain ⟨h1, h2, h3⟩ := hph
    rw [← h1, ← h2, ← h3]
    simp [hn]

/-! ## The loop head's `Reach` -/

/-- At a loop head nothing committed is left to report. -/
theorem reach_ce {R : AntSim.RunCfg} {dec : CCDec} {Adm : List EntryM → CCState → Prop}
    {net : List Msg} {xnet : List XMsg} {n : Fin R.N} {v : AntSim.NodeView} {r₁ : RState}
    (h : AntSim.Reach R dec Adm net xnet n v r₁) : v.ce = [] :=
  match h with
  | .stay _ hI _ => hI.2.2.2.1
  | .input _ _ _ hI _ _ _ _ _ _ => hI.2.2.2.1
  | .advance _ _ _ _ hce _ _ _ _ => hce

/-- **A loop head's `Reach` is a `ReachIn mskB1`** over any later sent lists: an input of the
driver's drains (`ByOk`: none of the B2/B3 inputs, `snapStatus`, `applyConf`, `storeAck`), and no
conf change proposed in a run without conf changes. -/
theorem reachIn_b1 {R : AntSim.RunCfg} {dec : CCDec} {Adm : List EntryM → CCState → Prop}
    {net₀ net : List Msg} {xnet₀ xnet : List XMsg} {n : Fin R.N} {v : AntSim.NodeView}
    {r₁ : RState}
    (hcc : R.md.confChanges = false) (hby : ByOk v.byE)
    (h : AntSim.Reach R dec Adm net₀ xnet₀ n v r₁) (hn : net₀ <+: net) (hx : xnet₀ <+: xnet) :
    AntSim.ReachIn AntSim.mskB1 R dec Adm net xnet n v r₁ := by
  match AntSim.Reach.mono hn hx h with
  | .stay _ hI hb => exact .stay _ hI hb
  | .advance _ _ h1 h2 h3 h4 h5 h6 h7 => exact .advance _ _ h1 h2 h3 h4 h5 h6 h7
  | .input _ inp _ hI hby' hc hxc hm hxm hst =>
    refine .input _ inp _ ?_ hI hby' hc hxc hm hxm hst
    rw [hby'] at hby
    cases inp with
    | proposeConf ty d =>
      simp only [AntSim.InputStep] at hst; rw [hcc] at hst; exact absurd hst.1 (by simp)
    | snapStatus to ok => simp [ByOk, AntSim.Input.byE] at hby
    | applyConf k => simp only [AntSim.InputStep] at hst
    | storeAck resp => simp [ByOk, AntSim.Input.byE] at hby
    | _ => simp [AntSim.Input.InMask, AntSim.mskB1]

/-! ## Transfer messages -/

/-- **A `Ready`'s transfer message is pending at the node** (`XPendOk`): raft's `XReadyOk`, with the
destination facts it leaves to the caller: a `MsgTimeoutNow`'s destination a server (from
`isRaftMsg`'s acknowledgement clause and the acknowledgements' names, or the driver), a
`MsgTransferLeader`'s term past `0` (raft stamps a forward with the node's term, which a node with a
leader has: `XScopeOk`), and the initial voters servers. -/
theorem xPendOk_of {R : AntSim.RunCfg} {γ : RaftNames} {id : w64} {p : PState} {x : XMsg}
    (hok : XReadyOk γ id p x) (hcfg : ∀ a ∈ γ.reCfg, ∃ j : Fin R.N, a = AntSim.nodeId j)
    (htn : x.ty = .timeoutNow → ∃ j : Fin R.N, x.dst = AntSim.nodeId j)
    (htl : x.ty = .transferLeader → x.term ≠ W64 0) :
    AntSim.XPendOk R.N id p x := by
  obtain ⟨h1, h2, h3⟩ := hok
  cases hty : x.ty with
  | timeoutNow =>
    obtain ⟨hd, ht⟩ := h2 (Or.inl hty)
    exact ⟨hd, htn hty, ht, fun _ => (h1 hty).1⟩
  | transferLeader =>
    have hz := htl hty
    obtain ⟨hd, ht⟩ := h2 (Or.inr hz)
    exact ⟨hd, hcfg _ (h3 hty hz), ht, fun h => by rw [hty] at h; cases h⟩

end pure

end AntHarness
end EtcdGrove
end Perennial
