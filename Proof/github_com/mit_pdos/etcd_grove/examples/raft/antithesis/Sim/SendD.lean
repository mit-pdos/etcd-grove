/-
Lean-first (no Rocq counterpart).

# Parity B2: `send` over `AntSimD` (`antSim_sendD_in`, #33 parity B2, Sim round 7)

A sync, unbatched node's next pending message is reported (`evSend`) and taken (`Send`, B 510-593).
Two arms:
- **after the write** (`mems = []`, no split write: the disk is raft's state, `DiskFold`): B1's case
  analysis (`Send.lean`'s `antSim_send_in`, restated over node `n`'s facts alone: `sendD_step`) at the
  node part of the run with the driver modes off (`nodeOkD_syncOff`);
- **a `-parallel` leader's request before its write** (`mems ≠ []`, an append or heartbeat): the
  leader's term is written (its win's `leaders` record, `BindingOk`'s leaders clause); `Sendable`'s
  commit is the in-memory one, recorded at its `mem` (`MemCommitOk`, `leader_sendableM`); its commit is
  within `MemCommit` (`LeadCommitMsgOkD`).
The relation after it is `send_relD` (`SendRel.send_rel` over `AntSimD`: the cleared undo record
raises the node's `EffTerm` only; a new heartbeat's commit against its receiver's undo record from the
leader's acknowledgements outside it and `UndoBindOk`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Send
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.QuietP
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.CarryD

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open GMap go_etcd_io.raft.v3 AntCheck

section sendD
variable [GooseExts]

/-! ## The step after the write: B1's case analysis over the node's facts -/

theorem BindingOkM.toW {R : RunCfg} {dec : CCDec} {S : State} (hb : BindingOkM R dec S) :
    BindingOkW R dec S := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := hb
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15.1, h16, h17, h18⟩

/-- **`send`'s step and side conditions from node `n`'s B1 facts** (`antSim_send_in`'s case
analysis): what it reads of the network is the cause's `Sendable` and the pre-vote voters. -/
theorem sendD_step {R : RunCfg} {dec : CCDec} {S1 : State} {net : List Msg} {G : RaftFacts}
    {n : Fin R.N} {v : NodeView} {q : Msg} {rest : List Msg}
    (hsn : R.md.snapshots = false) (hsh : Shape R S1) (hb : BindingOkW R dec S1) (hl : RaftLaws G)
    (hgo1 : GlobalOk R S1 net G)
    (hcs : ∀ m ∈ net, m.dst = nodeId n → S1.currentTerm[n.val]! ≤ uint.Z m.term → m.ty = .app →
      (toAppendFact (msgOf m m.dst) >>= S1.sendable) = .ok true)
    (hpv : ∀ m ∈ net, PreVoterOk R m) (hcz : ∀ j : Fin R.N, 0 ≤ S1.commitIndex[j.val]!)
    (hno : NodeOk R dec S1 net n v) (hdur : v.dur = durOf v.r) (hpend : v.pend = q :: rest)
    (htold : Told v)
    (hq7 : q.ty = .app ∨ q.ty = .appResp ∨ q.ty = .vote ∨ q.ty = .voteResp ∨ q.ty = .heartbeat ∨
      q.ty = .heartbeatResp ∨ q.ty = .propose ∨ q.ty = .preVote ∨ q.ty = .preVoteResp ∨
      q.ty = .readIndex ∨ q.ty = .readIndexResp) :
    ∃ M C, S1.step (evSend (nodeId n) v.byE q) = .ok (some (sendS S1 n.val M C)) ∧
      SendOk R S1 n q M C := by
  have hd := hno.disk
  have hmem := hno.mem
  have hL := hno.leader
  have hC := hno.cand
  have hT := hno.told
  have hca := hno.cause
  have hf := hno.facts
  have hfp : v.r.fp = [] := (hf.snap0 hsn).2.1
  have hb0 : v.ps.base = base0 := (hf.snap0 hsn).1
  have hfull : v.r.full = v.ps.log := by unfold RState.full; rw [hfp]; rfl
  have hct : S1.currentTerm[n.val]! = uint.Z v.ps.term := by rw [hd.1, hdur]; rfl
  have hvt : S1.vote n.val = nameOf v.ps.vote := by rw [hd.2.1, hdur]; rfl
  have hlg : S1.log[n.val]! = logOf v.ps.log := by rw [hd.2.2.1, hdur]; unfold durOf; simp only [hfull]
  have hcmt : S1.commitIndex[n.val]! = uint.Z v.ps.commit := by rw [hd.2.2.2, hdur]; rfl
  have hlidx : LogIdx v.ps.log := by
    have := hf.logIdx; rw [hdur] at this; unfold durOf at this; simp only [hfull] at this; exact this
  obtain ⟨hne, ⟨j, hj⟩, hcase⟩ := hno.pend q (by rw [hpend]; exact List.mem_cons_self ..)
  have hc : S1.cfg = R.cfg := hsh.1
  have hsrv : S1.cfg.server.has (nameOf q.dst) = true := by rw [hc, hj]; exact cfg_has R j
  have hne' : (nameOf q.dst != nameOf (nodeId n)) = true := by
    rw [bne_iff_ne]; intro h; exact hne (nameOf_inj h)
  have hrl0 : v.ps.role = .leader → S1.role[n.val]! = leader := fun hr => by
    have hpf : v.pre = false := by
      cases h : v.pre
      · rfl
      · have := hf.preRole h; rw [hr] at this; cases this
    rw [hmem.1, hr]; rfl
  cases hty : q.ty <;> simp only [hty] at hcase
  case vote =>
    obtain ⟨h1, h2, h3, -, h5, h6⟩ := hcase
    have hterm : S1.currentTerm[n.val]! = uint.Z q.term := by rw [hct, h3]
    obtain ⟨-, hvr⟩ := hC h2
    have hidx := plogLast_idx hlidx
    have e : S1.voteRequest n.val (S1.currentTerm[n.val]!) = Fact.mk go!"vote" (nameOf (nodeId n)) []
        (uint.Z q.term) (uint.Z q.index) (uint.Z q.logterm) 0 := by
      unfold State.voteRequest State.lastTerm
      rw [server_of hc n, hterm, hlg, h5, h6, hb0, hidx.1, hidx.2, logOf_length]
    rw [e] at hvr
    have hvf := List.contains_iff_mem.mpr hvr
    exact ⟨_, _, send_vote_eq n q _ hc hsrv hne' hty h1 hterm hvf,
      SendOk.plain hsh hb (hlcm := fun h _ _ => h.elim (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h)) (hhb := fun h => nomatch hty.symm.trans h) (.inl hty) ⟨h1, by omega⟩ ⟨j, hj⟩
        (fun h => h.elim (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h))
        (fun _ => ⟨_, voteFact_msgOf q q.dst, by rw [h1]; exact hvr⟩)
        (fun h => nomatch hty.symm.trans h.1) (fun h => nomatch hty.symm.trans h.1)⟩
  case voteResp =>
    obtain ⟨h1, h2, h3⟩ := hcase
    have hterm : S1.currentTerm[n.val]! = uint.Z q.term := by rw [hct, h2]
    cases hrej : q.reject
    · have hvd := h3 hrej
      have hvn : S1.vote n.val = nameOf q.dst := by rw [hvt, hvd]
      have hv0 := hb.2.2.2.2.2.2.2.2.2.2.1 n (by rw [hvn, hj]; exact nameOf_ne_nil j)
      rw [hvn, hterm] at hv0
      have hv := List.contains_iff_mem.mpr hv0
      exact ⟨_, _, send_grant_eq n q _ hc hsrv hne' hty h1 hrej hv,
        SendOk.ofGrant hsh hb hty h1 (by omega) j hj⟩
    · exact ⟨_, _, send_voteRej_eq n q _ hc hsrv hne' hty h1 hrej,
        SendOk.plain hsh hb (hlcm := fun h _ _ => h.elim (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h)) (hhb := fun h => nomatch hty.symm.trans h) (.inr (.inl hty)) ⟨h1, by omega⟩ ⟨j, hj⟩
          (fun h => h.elim (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h))
          (fun h => nomatch hty.symm.trans h)
          (fun h => by rw [hrej] at h; exact absurd h.2 (by decide))
          (fun h => nomatch hty.symm.trans h.1)⟩
  case app =>
    obtain ⟨hrole, hok⟩ := hcase
    obtain ⟨-, h1, h2, -, hpt, hcm, -, hpre, hpay⟩ := hok
    have hterm : S1.currentTerm[n.val]! = uint.Z q.term := by rw [hct, h2]
    have hrl : S1.role[n.val]! = leader := hrl0 hrole
    rw [hb0] at hpt hpre
    have hes : (v.ps.log.drop (uint.nat q.index)).take q.entries.length = q.entries := by
      have hp2 := hpay.2
      have hw : uint.Z (q.index + W64 1) = uint.Z q.index + 1 := by word
      unfold plogFrom at hpre
      rw [hw, base0_index] at hpre
      have e : (uint.Z q.index + 1 - 0 - 1).toNat = uint.nat q.index := by word
      rw [e] at hpre
      exact (List.prefix_iff_eq_take.mp hpre).symm
    have hsd := leader_sendable hb hct hlg hcmt hfull hL hrole (nameOf q.dst) hpt hes hcm
    rw [← h2] at hsd
    exact ⟨_, _, send_app_eq n q _ hc hsrv hne' hty h1 hterm hrl hsd,
      SendOk.plain hsh hb (hlcm := fun _ _ _ => by rw [hcmt]; exact hcm) (hhb := fun h => nomatch hty.symm.trans h) (.inr (.inr (.inl hty))) ⟨h1, by omega⟩ ⟨j, hj⟩
        (fun _ => by rw [toAppendFact_msgOf, eok_bind, h1]; exact hsd)
        (fun h => nomatch hty.symm.trans h)
        (fun h => nomatch hty.symm.trans h.1) (fun h => nomatch hty.symm.trans h.1)⟩
  case heartbeat =>
    obtain ⟨hrole, hok, hi0, hlt0, hen⟩ := hcase
    obtain ⟨-, h1, h2, -, hcm, hmt⟩ := hok
    have hterm : S1.currentTerm[n.val]! = uint.Z q.term := by rw [hct, h2]
    have hrl : S1.role[n.val]! = leader := hrl0 hrole
    have hhb : q.ty = .heartbeat → ∀ j' : Fin R.N, q.dst = nodeId j' →
        S1.currentTerm[j'.val]! ≤ uint.Z q.term →
        ((S1.confirmed[j'.val]!).term = uint.Z q.term ∧ uint.Z q.commit ≤ (S1.confirmed[j'.val]!).index) ∨
          uint.Z q.commit ≤ S1.commitIndex[j'.val]! := by
      intro _ j' hj' hle
      have hjn : j' ≠ n := fun e => hne (by rw [hj', e])
      obtain ⟨-, -, -, -, -, hb8, -, -, -, -, -, hb14, -, -, -, -, -⟩ := hb
      obtain ⟨-, -, -, l4, -⟩ := hL hrole
      have hc0 : 0 ≤ S1.commitIndex[j'.val]! := hcz j'
      rw [hj'] at hmt
      rcases l4 j' hjn with h0 | ⟨a, ha, haty, hasrc, -, hat, hai⟩
      · right; rw [h0] at hmt; have : uint.Z (W64 0) = 0 := rfl; omega
      · have hqt : uint.Z q.term = uint.Z v.ps.term := by rw [h2]
        have hat' : a.term = S1.currentTerm[j'.val]! := by
          have := hb14 j' a ha haty hasrc
          omega
        rcases hb8 j' a ha haty hasrc hat' with ⟨c1, c2⟩ | c
        · left; exact ⟨by omega, by omega⟩
        · right; omega
    have hpt : plogTermAt base0 v.ps.log (W64 0) = some (W64 0) := by
      unfold plogTermAt; simp [base0]
    have hsd0 := leader_sendable (es := []) hb hct hlg hcmt hfull hL hrole (nameOf q.dst) hpt rfl hcm
    have hsd : S1.sendable ⟨nameOf (nodeId n), nameOf q.dst, uint.Z q.term, uint.Z q.index, uint.Z q.logterm,
        logOf q.entries, uint.Z q.commit⟩ = .ok true := by
      rw [hi0, hlt0, hen, h2]; exact hsd0
    exact ⟨_, _, send_hb_eq n q _ hc hsrv hne' hty h1 hterm hrl hsd,
      SendOk.plain hsh hb (hlcm := fun _ _ _ => by rw [hcmt]; exact hcm) (hhb := hhb) (.inr (.inr (.inr (.inr (.inl hty))))) ⟨h1, by omega⟩ ⟨j, hj⟩
        (fun _ => by rw [toAppendFact_msgOf, eok_bind, h1]; exact hsd)
        (fun h => nomatch hty.symm.trans h)
        (fun h => nomatch hty.symm.trans h.1) (fun h => nomatch hty.symm.trans h.1)⟩
  case heartbeatResp =>
    obtain ⟨h1, h2⟩ := hcase
    have hterm : S1.currentTerm[n.val]! = uint.Z q.term := by rw [hct, h2]
    exact ⟨_, _, send_hbresp_eq n q _ hc hsrv hne' hty h1 (by omega),
      SendOk.plain hsh hb (hlcm := fun h _ _ => h.elim (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h)) (hhb := fun h => nomatch hty.symm.trans h) (.inr (.inr (.inr (.inr (.inr (.inl hty)))))) ⟨h1, by omega⟩ ⟨j, hj⟩
        (fun h => h.elim (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h))
        (fun h => nomatch hty.symm.trans h)
        (fun h => nomatch hty.symm.trans h.1) (fun h => nomatch hty.symm.trans h.1)⟩
  case propose =>
    obtain ⟨h1, h2⟩ := hcase
    have h0 : 0 ≤ uint.Z v.ps.term := by word
    have hz : uint.Z q.term = 0 := by rw [h2]; rfl
    exact ⟨_, _, send_prop_eq n q _ hc hsrv hne' hty,
      SendOk.plain hsh hb (hlcm := fun h _ _ => h.elim (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h)) (hhb := fun h => nomatch hty.symm.trans h) (.inr (.inr (.inr (.inr (.inr (.inr hty)))))) ⟨h1, by omega⟩ ⟨j, hj⟩
        (fun h => h.elim (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h))
        (fun h => nomatch hty.symm.trans h)
        (fun h => nomatch hty.symm.trans h.1) (fun h => nomatch hty.symm.trans h.1)⟩
  case appResp =>
    obtain ⟨h1, hby, hcase⟩ := hcase
    have hreq : (q.ty = .app ∨ q.ty = .heartbeat) →
        (toAppendFact (msgOf q q.dst) >>= S1.sendable) = .ok true :=
      fun h => h.elim (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h)
    rcases hcase with hcase | ⟨m, hcm, hmty, -, hlt, hqe⟩
    rotate_left
    · obtain ⟨m', hcm', hpd⟩ := (hT (htold hby)).resolve_right
        (fun ⟨x, hx, _⟩ => by rw [(hno.xcause x hx).2] at hcm; cases hcm)
      rw [hcm] at hcm'; cases hcm'
      have hqt2 : q.term = v.ps.term := by rw [hqe]
      have hterm : S1.currentTerm[n.val]! = uint.Z q.term := by rw [hct, hqt2]
      have hrej : q.reject = false := by rw [hqe]
      have hi' : (uint.Z q.index == 0) = true := by rw [hqe]; rfl
      have hlt' : uint.Z m.term < S1.currentTerm[n.val]! := by rw [hterm, hqt2]; exact hlt
      exact ⟨_, _, send_appRespStale_eq n q _ hc hsrv hne' hty h1 hrej m hpd hmty hlt' hi' hterm.symm,
        SendOk.plain hsh hb (hlcm := fun h _ _ => h.elim (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h)) (hhb := fun h => nomatch hty.symm.trans h) (.inr (.inr (.inr (.inl hty)))) ⟨h1, by omega⟩ ⟨j, hj⟩ hreq
          (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h.1)
          (fun h => h.2.2 (by rw [hqe]))⟩
    obtain ⟨m, hcm, hmty, hqd, hqt, hqt2, hacc⟩ := hcase
    have hterm : S1.currentTerm[n.val]! = uint.Z q.term := by rw [hct, hqt2]
    cases hrej : q.reject
    case true =>
      exact ⟨_, _, send_appRespRej_eq n q _ hc hsrv hne' hty h1 hrej,
        SendOk.plain hsh hb (hlcm := fun h _ _ => h.elim (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h)) (hhb := fun h => nomatch hty.symm.trans h) (.inr (.inr (.inr (.inl hty)))) ⟨h1, by omega⟩ ⟨j, hj⟩ hreq
          (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h.1)
          (fun h => by rw [hrej] at h; exact absurd h.2.1 (by decide))⟩
    case false =>
    obtain ⟨m', hcm', hpd⟩ := (hT (htold hby)).resolve_right (fun ⟨x, hx, _⟩ => by rw [(hno.xcause x hx).2] at hcm; cases hcm)
    rw [hcm] at hcm'; cases hcm'
    have hqtZ : uint.Z q.term = uint.Z m.term := by rw [hqt]
    have hmt : S1.currentTerm[n.val]! = uint.Z m.term := by rw [hterm, hqtZ]
    by_cases hi : uint.Z q.index = 0
    · have hi' : (uint.Z q.index == 0) = true := by simpa using hi
      exact ⟨_, _, send_appResp0_eq n q _ hc hsrv hne' hty h1 hrej m hpd hmty hmt hi',
        SendOk.plain hsh hb (hlcm := fun h _ _ => h.elim (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h)) (hhb := fun h => nomatch hty.symm.trans h) (.inr (.inr (.inr (.inl hty)))) ⟨h1, by omega⟩ ⟨j, hj⟩ hreq
          (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h.1)
          (fun h => h.2.2 (by word))⟩
    · have hi' : (uint.Z q.index == 0) = false := by simpa using hi
      obtain ⟨hmn, hmd⟩ := hca m hcm
      have hsd : S1.sendable (recvFact m (nodeId n)) = .ok true := by
        have := hcs m hmn hmd (by omega) hmty; rw [toAppendFact_msgOf, eok_bind, hmd] at this; exact this
      have hG := ack_guard_eq S1 n.val m (nodeId n) (uint.Z q.index)
      by_cases hg : uint.Z q.index = recvLast m ∧ AckGuard S1 n.val m (nodeId n)
      · rw [decide_eq_true hg] at hG
        exact ⟨_, _, send_ack_eq n q _ hc hsrv hne' hty h1 hrej m hpd hmty hmt hi' hsd hqd hqtZ hG,
          SendOk.ofAck hsh hb hl hgo1 hty h1 hmt j hj hqd hqtZ hg.1 hi hsd hg.2⟩
      · rw [decide_eq_false hg] at hG
        rcases hacc hrej with ⟨a1, a2, a3⟩ | ⟨s1, s2⟩
        · exact absurd (accept_guard hlg a1 (by rw [← hb0]; exact a2) (fun k e h => by rw [← hb0]; exact a3 k e h)) hg
        · have hst : uint.Z m.index < S1.commitIndex[n.val]! := by rw [hcmt]; exact s1
          have hqi : uint.Z q.index = S1.commitIndex[n.val]! := by rw [hcmt, s2]
          exact ⟨_, _, send_stale_eq n q _ hc hsrv hne' hty h1 hrej m hpd hmty hmt hi' hsd hqd hqtZ hG hst hqi,
            SendOk.ofStale hsh hb hty h1 (by omega) j hj hqd hqtZ hqi⟩
  case preVote =>
    obtain ⟨h1, hvt⟩ := hcase
    exact ⟨_, _, send_pre_eq n q _ hc hsrv hne' (.inl hty) h1,
      SendOk.plainP hsh hb (by simp [hty]) ⟨h1, .inl (.inl hty)⟩
        (fun hcc => ⟨fun _ => by rw [h1]; rw [(hf.conf0 hcc).1, CfgM.voters_simple] at hvt; exact hvt,
          fun h => nomatch hty.symm.trans h⟩) ⟨j, hj⟩
        (fun h => h.elim (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h))
        (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h.1)
        (fun h => nomatch hty.symm.trans h.1) (fun h => nomatch hty.symm.trans h)
        (fun h _ _ => h.elim (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h))⟩
  case preVoteResp =>
    obtain ⟨h1, hgr, hrjt⟩ := hcase
    have hsrc : PreTermKeep q ∨ uint.Z q.term ≤ S1.currentTerm[n.val]! := by
      cases hrej : q.reject
      · exact .inl (.inr ⟨hty, hrej⟩)
      · exact .inr (Int.le_of_eq (by rw [hct, hrjt hrej]))
    have hpvo : PreVoterOk R q := by
      refine fun hcc => ⟨fun h => (nomatch hty.symm.trans h), fun _ hrej => ?_⟩
      obtain ⟨m, hcm, hmty, hqd⟩ := hgr hrej
      obtain ⟨hmn, -⟩ := hca m hcm
      rw [hqd]; exact (hpv m hmn hcc).1 hmty
    exact ⟨_, _, send_pre_eq n q _ hc hsrv hne' (.inr hty) h1,
      SendOk.plainP hsh hb (by simp [hty]) ⟨h1, hsrc⟩ hpvo ⟨j, hj⟩
        (fun h => h.elim (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h))
        (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h.1)
        (fun h => nomatch hty.symm.trans h.1) (fun h => nomatch hty.symm.trans h)
        (fun h _ _ => h.elim (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h))⟩
  case readIndex =>
    obtain ⟨h0, i, hi⟩ := hcase
    exact ⟨_, _, send_readIdx_eq n q _ hc hsrv hne' hty, SendOk.readIdx hsh hb hty h0 ⟨i, hi⟩ ⟨j, hj⟩⟩
  case readIndexResp =>
    obtain ⟨h1, h2⟩ := hcase
    exact ⟨_, _, send_readResp_eq n q _ hc hsrv hne' hty h1,
      SendOk.plainP hsh hb (by simp [hty]) ⟨h1, .inr (Int.le_of_eq (by rw [hct, h2]))⟩
        (fun _ => ⟨fun h => (nomatch hty.symm.trans h), fun h => (nomatch hty.symm.trans h)⟩) ⟨j, hj⟩
        (fun h => h.elim (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h))
        (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h.1)
        (fun h => nomatch hty.symm.trans h.1) (fun h => nomatch hty.symm.trans h)
        (fun h _ _ => h.elim (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h))⟩
  all_goals (exfalso; rw [hty] at hq7; simp at hq7)

/-! ## What `send` leaves: the restart facts -/

theorem effTerm_sendS_ge {S : State} {n : Nat} {M : List Fact} {C : List Confirmed}
    (hn : n < S.undo.length) (j : Nat) : S.effTerm j ≤ (sendS S n M C).effTerm j := by
  by_cases hj : j = n
  · subst hj
    have e : (sendS S j M C).effTerm j = S.currentTerm[j]! := by
      unfold State.effTerm; simp only [sendS]; rw [get!_set_self _ hn]
    rw [e]; exact effTerm_le S j
  · have e : (sendS S n M C).effTerm j = S.effTerm j := by
      unfold State.effTerm; simp only [sendS]; rw [get!_set_ne _ _ hj]
    rw [e]; exact Int.le_refl _

theorem effTerm_sendS_self {S : State} {n : Nat} {M : List Fact} {C : List Confirmed}
    (hn : n < S.undo.length) : (sendS S n M C).effTerm n = S.currentTerm[n]! := by
  unfold State.effTerm; simp only [sendS]; rw [get!_set_self _ hn]

theorem sendS_undo_some {S : State} {n : Nat} {M : List Fact} {C : List Confirmed}
    (hn : n < S.undo.length) {j : Nat} {u : Pre} (h : (sendS S n M C).undo[j]! = some u) :
    j ≠ n ∧ S.undo[j]! = some u := by
  by_cases hj : j = n
  · subst hj; change (S.undo.set j none)[j]! = some u at h; rw [get!_set_self _ hn] at h; cases h
  · change (S.undo.set n none)[j]! = some u at h; rw [get!_set_ne _ _ hj] at h; exact ⟨hj, h⟩

theorem AckOut.sendS {N : Nat} {S : State} {n j : Fin N} {M : List Fact} {C : List Confirmed} {a : Fact}
    (hn : n.val < S.undo.length) (h : j ≠ n → AckOut S j a) : AckOut (sendS S n.val M C) j a := by
  intro u hu hm
  obtain ⟨hj, hu'⟩ := sendS_undo_some hn hu
  exact h (fun e => hj (by rw [e])) u hu' hm

theorem AckInD.sendS {N : Nat} {S : State} {n i : Fin N} {M : List Fact} {C : List Confirmed}
    {dst : Str} {t k : Int} (hn : n.val < S.undo.length) (hsub : ∀ f ∈ S.msgs, f ∈ M)
    (h : AckInD S i dst t k) : AckInD (sendS S n.val M C) i dst t k := by
  obtain ⟨a, ha, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨a, hsub a ha, h1, h2, h3, h4, h5, AckOut.sendS hn (fun _ => h6)⟩

theorem AckInX.sendS {N : Nat} {S : State} {n k j : Fin N} {M : List Fact} {C : List Confirmed}
    {t i : Int} (hn : n.val < S.undo.length) (hsub : ∀ f ∈ S.msgs, f ∈ M)
    (h : AckInX S k j t i) : AckInX (sendS S n.val M C) k j t i := by
  obtain ⟨a, ha, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨a, hsub a ha, h1, h2, h3, h4, h5, fun hj => AckOut.sendS hn (fun _ => h6 hj)⟩

/-- `SendOk` with a leader's request's commit within `MemCommit` (`LeadCommitMsgOkD`: a `-parallel`
leader's request carries a commit announced but maybe not written) and a new heartbeat's commit
against its receiver's undo record (`HbCommitOkD`). -/
structure SendOkD (R : RunCfg) (S : State) (n : Fin R.N) (q : Msg) (M : List Fact)
    (C : List Confirmed) : Prop where
  sub : ∀ f ∈ S.msgs, f ∈ M
  new : ∀ f ∈ M, f ∉ S.msgs → f.type ≠ go!"vote" ∧ f.src = nameOf (nodeId n) ∧
    ∃ j : Fin R.N, f.dst = nameOf (nodeId j)
  clen : C.length = R.N
  cother : ∀ k : Fin R.N, k ≠ n → C[k.val]! = S.confirmed[k.val]!
  conf : ∀ l, S.ledLog.get (C[n.val]!).term = .ok l →
    (C[n.val]!).index ≤ (S.log[n.val]!).length ∧ (C[n.val]!).index ≤ l.length ∧
    (S.log[n.val]!).take (C[n.val]!).index.toNat = l.take (C[n.val]!).index.toNat
  acks : ∀ a ∈ M, a.type = go!"ack" → a.src = nameOf (nodeId n) → a.term = S.currentTerm[n.val]! →
    ((C[n.val]!).term = a.term ∧ a.index ≤ (C[n.val]!).index) ∨ a.index ≤ S.commitIndex[n.val]!
  ty : q.ty = .vote ∨ q.ty = .voteResp ∨ q.ty = .app ∨ q.ty = .appResp ∨ q.ty = .heartbeat ∨
    q.ty = .heartbeatResp ∨ q.ty = .propose ∨ q.ty = .preVote ∨ q.ty = .preVoteResp ∨
    q.ty = .readIndex ∨ q.ty = .readIndexResp
  src : q.ty ≠ .readIndex → q.src = nodeId n ∧ (PreTermKeep q ∨ uint.Z q.term ≤ S.currentTerm[n.val]!)
  fwd : q.ty = .readIndex → q.term = W64 0 ∧ ∃ i : Fin R.N, q.src = nodeId i
  pvo : PreVoterOk R q
  dst : ∃ j : Fin R.N, q.dst = nodeId j
  req : (q.ty = .app ∨ q.ty = .heartbeat) → (toAppendFact (msgOf q q.dst) >>= S.sendable) = .ok true
  vote : q.ty = .vote → ∃ f, voteFact (msgOf q q.dst) = .ok f ∧ f ∈ M
  grant : (q.ty = .voteResp ∧ q.reject = false) →
    ({ type := go!"grant", src := nameOf q.src, dst := nameOf q.dst, term := uint.Z q.term } : Fact) ∈ M
  ack : (q.ty = .appResp ∧ q.reject = false ∧ q.index ≠ W64 0) →
    AckIn (sendS S n.val M C) (nameOf q.src) (nameOf q.dst) (uint.Z q.term) (uint.Z q.index)
  ackt : ∀ a ∈ M, a ∉ S.msgs → a.type = go!"ack" → a.term ≤ S.currentTerm[n.val]!
  cmono : C[n.val]! = S.confirmed[n.val]! ∨
    ((C[n.val]!).term = S.currentTerm[n.val]! ∧ S.ledLog.has (C[n.val]!).term = true ∧
      ((S.confirmed[n.val]!).term = (C[n.val]!).term →
        (S.confirmed[n.val]!).index ≤ (C[n.val]!).index))
  hb : q.ty = .heartbeat → ∀ j : Fin R.N, q.dst = nodeId j → S.currentTerm[j.val]! ≤ uint.Z q.term →
    ((C[j.val]!).term = uint.Z q.term ∧ uint.Z q.commit ≤ (C[j.val]!).index) ∨
      uint.Z q.commit ≤ S.commitIndex[j.val]!
  lcm : (q.ty = .app ∨ q.ty = .heartbeat) → S.role[n.val]! ≠ follower →
    S.currentTerm[n.val]! = uint.Z q.term → ∃ c, S.memCommit n.val = .ok c ∧ uint.Z q.commit ≤ c
  hbU : q.ty = .heartbeat → ∀ j : Fin R.N, q.dst = nodeId j → ∀ u : Pre, S.undo[j.val]! = some u →
    u.made = false → u.term ≤ uint.Z q.term →
    (u.confirmed.term = uint.Z q.term ∧ uint.Z q.commit ≤ u.confirmed.index) ∨ uint.Z q.commit ≤ u.commit

/-- `SendOk` of a node with no queued `mem` (`MemCommit` is the disk's commit). -/
theorem SendOk.toD {R : RunCfg} {S : State} {n : Fin R.N} {q : Msg} {M : List Fact} {C : List Confirmed}
    (hok : SendOk R S n q M C) (hq : S.queue[n.val]! = [])
    (hbU : q.ty = .heartbeat → ∀ j : Fin R.N, q.dst = nodeId j → ∀ u : Pre, S.undo[j.val]! = some u →
      u.made = false → u.term ≤ uint.Z q.term →
      (u.confirmed.term = uint.Z q.term ∧ uint.Z q.commit ≤ u.confirmed.index) ∨
        uint.Z q.commit ≤ u.commit) :
    SendOkD R S n q M C :=
  { sub := hok.sub, new := hok.new, clen := hok.clen, cother := hok.cother, conf := hok.conf,
    acks := hok.acks, ty := hok.ty, src := hok.src, fwd := hok.fwd, pvo := hok.pvo, dst := hok.dst,
    req := hok.req, vote := hok.vote, grant := hok.grant, ack := hok.ack, ackt := hok.ackt,
    cmono := hok.cmono, hb := hok.hb,
    lcm := fun a b c => ⟨_, memCommit_nil hq, hok.lcm a b c⟩, hbU := hbU }

/-- **A leader's heartbeat's commit against its receiver's undo record**: its `Match` for the
receiver is backed by an acknowledgement outside the receiver's unmade write (`LeaderPartD`'s
`AckInX`), at the heartbeat's term; `UndoBindOk` bounds it by the undo record's confirmation or
commit. -/
theorem hbU_of_leader {R : RunCfg} {S : State} {n : Fin R.N} {v : NodeView} {q : Msg}
    (hu : UndoBindOk R.N S) (hL : LeaderPartD S n v) (hrole : v.ps.role = .leader)
    (hne : q.dst ≠ nodeId n) (hqt : q.term = v.ps.term)
    (hmt : uint.Z q.commit ≤ uint.Z (matchOf v.ps q.dst)) :
    ∀ j : Fin R.N, q.dst = nodeId j → ∀ u : Pre, S.undo[j.val]! = some u → u.made = false →
      u.term ≤ uint.Z q.term →
      (u.confirmed.term = uint.Z q.term ∧ uint.Z q.commit ≤ u.confirmed.index) ∨
        uint.Z q.commit ≤ u.commit := by
  intro j hj u hu1 hu2 hut
  have hjn : j ≠ n := fun e => hne (by rw [hj, e])
  obtain ⟨-, -, -, l4, -⟩ := hL hrole
  obtain ⟨-, -, -, u4, -, -, u7, u8⟩ := hu.2.2 j u hu1 hu2
  have hqZ : uint.Z q.term = uint.Z v.ps.term := by rw [hqt]
  rw [hj] at hmt
  rcases l4 j hjn with h0 | ⟨a, ha, haty, hasrc, -, hat, hai, hout⟩
  · right; rw [h0] at hmt; have : uint.Z (W64 0) = 0 := rfl; omega
  · have han : a ∉ u.msgs := hout hjn u hu1 hu2
    have h1 := u7 a ha han haty hasrc
    have hat' : a.term = u.term := by omega
    rcases u8 a ha han haty hasrc hat' with ⟨c1, c2⟩ | c
    · left; exact ⟨by omega, by omega⟩
    · right; omega

/-- C3 after a `send` (`send_rel`'s). -/
theorem SendOkD.bindingOk {R : RunCfg} {dec : CCDec} {S : State} {n : Fin R.N} {q : Msg}
    {M : List Fact} {C : List Confirmed} (hb : BindingOkM R dec S) (hok : SendOkD R S n q M C) :
    BindingOkM R dec (sendS S n.val M C) := by
  have hsub := hok.sub
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17⟩ := hb
  refine ⟨hb1, hb2, hb3, hb4, ?_, ?_, hb7, hb8, ?_, hb10, hb11, ?_, hb13, ?_, hb15, hb16, hb17.1,
    hb17.2.1, fun f hf ht => (Classical.em (f ∈ S.msgs)).elim (fun hm => hb17.2.2 f hm ht)
      (fun hm => absurd ht (hok.new f hf hm).1)⟩
  · intro k l hl
    by_cases hk : k = n
    · subst hk; exact hok.conf l hl
    · change S.ledLog.get (C[k.val]!).term = .ok l at hl
      change (C[k.val]!).index ≤ (S.log[k.val]!).length ∧ (C[k.val]!).index ≤ l.length ∧
        (S.log[k.val]!).take (C[k.val]!).index.toNat = l.take (C[k.val]!).index.toNat
      rw [hok.cother k hk] at hl ⊢
      exact hb5 k l hl
  · intro k a ha ht hsa hta
    by_cases hk : k = n
    · subst hk; exact hok.acks a ha ht hsa hta
    · change ((C[k.val]!).term = a.term ∧ a.index ≤ (C[k.val]!).index) ∨ a.index ≤ S.commitIndex[k.val]!
      by_cases hm : a ∈ S.msgs
      · rw [hok.cother k hk]; exact hb6 k a hm ht hsa hta
      · exact absurd (name_inj ((hok.new a ha hm).2.1.symm.trans hsa)).symm hk
  · intro f hf ht
    by_cases hm : f ∈ S.msgs
    · exact hb9 f hm ht
    · obtain ⟨_, h1, j, h2⟩ := hok.new f hf hm
      exact ⟨⟨n, h1⟩, j, h2⟩
  · intro k a ha ht hsa
    by_cases hm : a ∈ S.msgs
    · exact hb12 k a hm ht hsa
    · have hkn : k = n := (name_inj ((hok.new a ha hm).2.1.symm.trans hsa)).symm
      subst hkn; exact hok.ackt a ha hm ht
  · intro k
    by_cases hk : k = n
    · subst hk
      change ((C[k.val]!).index = 0 ∨ S.ledLog.has (C[k.val]!).term = true ∨
        ∀ i : Fin R.N, (C[k.val]!).term < S.currentTerm[i.val]!) ∧ (C[k.val]!).term ≤ S.currentTerm[k.val]!
      rcases hok.cmono with e | ⟨e1, e2, -⟩
      · rw [e]; exact hb14 k
      · exact ⟨.inr (.inl e2), Int.le_of_eq e1⟩
    · change ((C[k.val]!).index = 0 ∨ S.ledLog.has (C[k.val]!).term = true ∨
        ∀ i : Fin R.N, (C[k.val]!).term < S.currentTerm[i.val]!) ∧ (C[k.val]!).term ≤ S.currentTerm[k.val]!
      rw [hok.cother k hk]; exact hb14 k

/-- The restart facts after a `send`: the node's undo record goes (its `EffTerm` rises to its term),
the facts it adds are its own. -/
theorem SendOkD.undoBindOk {R : RunCfg} {S : State} {n : Fin R.N} {q : Msg} {M : List Fact}
    {C : List Confirmed} (hn : n.val < S.undo.length) (hu : UndoBindOk R.N S) (hok : SendOkD R S n q M C) :
    UndoBindOk R.N (sendS S n.val M C) := by
  obtain ⟨hu1, hu2, hu3⟩ := hu
  refine ⟨fun T hT => (hu1 T hT).imp id (fun h i => Int.lt_of_lt_of_le (h i) (effTerm_sendS_ge hn i.val)),
    fun j => ?_, fun j u hu hm => ?_⟩
  · have mono : ∀ (x : Confirmed), (x.index = 0 ∨ S.ledLog.has x.term = true ∨
        ∀ i : Fin R.N, x.term < S.effTerm i.val) →
        (x.index = 0 ∨ S.ledLog.has x.term = true ∨
          ∀ i : Fin R.N, x.term < (sendS S n.val M C).effTerm i.val) :=
      fun x h => h.imp id (fun h => h.imp id (fun h i => Int.lt_of_lt_of_le (h i) (effTerm_sendS_ge hn i.val)))
    change (C[j.val]!).index = 0 ∨ S.ledLog.has (C[j.val]!).term = true ∨
      ∀ i : Fin R.N, (C[j.val]!).term < (sendS S n.val M C).effTerm i.val
    by_cases hj : j = n
    · subst hj
      rcases hok.cmono with e | ⟨-, e2, -⟩
      · rw [e]; exact mono _ (hu2 j)
      · exact .inr (.inl e2)
    · rw [hok.cother j hj]; exact mono _ (hu2 j)
  · obtain ⟨hjn, hu'⟩ := sendS_undo_some hn hu
    have hjn' : j ≠ n := fun e => hjn (by rw [e])
    obtain ⟨u1, u2, u3, u4, u5, u6, u7, u8⟩ := hu3 j u hu' hm
    have hold : ∀ a ∈ M, a ∉ u.msgs → a.type = go!"ack" → a.src = nameOf (nodeId j) → a ∈ S.msgs := by
      intro a ha _ _ hsa
      by_cases hm : a ∈ S.msgs
      · exact hm
      · exact absurd (nodeId_inj (nameOf_inj ((hok.new a ha hm).2.1.symm.trans hsa))).symm hjn'
    exact ⟨u1, u2, u3, u4, u5, u6, fun a ha hn' ht hs => u7 a (hold a ha hn' ht hs) hn' ht hs,
      fun a ha hn' ht hs => u8 a (hold a ha hn' ht hs) hn' ht hs⟩

/-- A node part after a `send` (`NodeOk.send` over `NodeOkD`): one unreported message fewer (`p`), the
undo record `u` and `made` `b` the caller's (cleared for the sender). -/
theorem NodeOkD.sendD {R : RunCfg} {dec : CCDec} {S : State} {net : List Msg} {k n : Fin R.N}
    {v : NodeView} {M : List Fact} {C : List Confirmed} {q : Msg} (hn : n.val < S.undo.length)
    (hbat : R.drv.batch = false) (hok : SendOkD R S n q M C) (h : NodeOkD R dec S net k v)
    (hcm : C[k.val]! = S.confirmed[k.val]! ∨ S.currentTerm[k.val]! = uint.Z v.ps.term)
    (p : List Msg) (hp : ∀ x ∈ p, x ∈ v.pend) (u : Option DurW) (b : Bool)
    (hu : UndoIs (sendS S n.val M C) k { v with pend := p, undo := u, made := b })
    (hsd : SyncDisk R { v with pend := p, undo := u, made := b })
    (huf : UndoFacts R { v with pend := p, undo := u, made := b })
    (hum : R.md.async = false → R.drv.batch = false → u ≠ none → b = false) :
    NodeOkD R dec (sendS S n.val M C) (net ++ [q]) k { v with pend := p, undo := u, made := b } := by
  have hsub := hok.sub
  obtain ⟨d1, d2, -, -, d5, d6, d7, d8, d9, d10, d11, -, d13, d14, d15, d16, d17, d18, d19, -, d21,
    d22, d23, -, d25⟩ := h
  have hack : ∀ {src dst : Str} {t k : Int}, AckIn S src dst t k → AckIn (sendS S n.val M C) src dst t k :=
    fun h => AckIn.mono hsub h
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := d8
  obtain ⟨j1, j2, j3, j4, j5, j6⟩ := d22
  refine ⟨d1, d2, hsd, hu, d5, d6, d7, ⟨f1, f2, f3, f4, f5, f6, fun x hx => f7 x (hp x hx), f8⟩, ?_, ?_,
    fun hb x hx => d11 hb x (hp x hx), fun hb' => (by rw [hbat] at hb'; cases hb'), d13, ?_, d15, ?_,
    d17, d18, d19, huf, d21, ⟨j1, j2, j3, j4, fun j hj => ⟨fun m hm => ⟨List.mem_append_left _
      ((j5 j hj).1 m hm).1, ((j5 j hj).1 m hm).2⟩, (j5 j hj).2⟩, fun ha x hx => j6 ha x (hp x hx)⟩,
    d23, hum, d25⟩
  · intro hl
    obtain ⟨l1, l2, l3, l4, l5⟩ := d9 hl
    refine ⟨l1, l2, fun j i h1 h2 => AckInX.sendS hn hsub (l3 j i h1 h2),
      fun j hj => (l4 j hj).imp id (AckInX.sendS hn hsub), fun hpre => ?_⟩
    obtain ⟨c1, c2⟩ := l5 hpre
    change (C[k.val]!).term = uint.Z v.ps.term ∧ (v.dur.log.length : Int) ≤ (C[k.val]!).index
    by_cases hk : k = n
    · subst hk
      rcases hcm with e | hct
      · rw [e]; exact ⟨c1, c2⟩
      · rcases hok.cmono with e | ⟨e1, -, e3⟩
        · rw [e]; exact ⟨c1, c2⟩
        · have ht : (S.confirmed[k.val]!).term = (C[k.val]!).term := c1.trans (hct.symm.trans e1.symm)
          exact ⟨e1.trans hct, Int.le_trans c2 (e3 ht)⟩
    · rw [hok.cother k hk]; exact ⟨c1, c2⟩
  · intro hc
    obtain ⟨c1, c2⟩ := d10 hc
    exact ⟨fun j hj => granted_mono (s1 := sendS S n.val M C) (s := S) k.val rfl rfl hsub rfl (c1 j hj),
      fun hd => hsub _ (c2 hd)⟩
  · intro x hx
    refine (d14 x hx).elim (fun hQ' => Or.inl ?_) Or.inr
    obtain ⟨a1, a2, a3, ⟨a4, a5⟩ | a6⟩ := hQ'
    · exact ⟨a1, a2, a3, .inl ⟨a4, a5.imp (fun h => ⟨h.1, h.2.1, hack h.2.2⟩) id⟩⟩
    · exact ⟨a1, a2, a3, .inr a6⟩
  · intro m hm
    obtain ⟨h1, h2⟩ := d16 m hm
    exact ⟨List.mem_append_left _ h1, h2⟩

/-- C4 after a `send` (`send_rel`'s `NetOk` over `NetOkD`). -/
theorem SendOkD.netOkD {R : RunCfg} {dec : CCDec} {S : State} {V : Fin R.N → NodeView} {net : List Msg}
    {n : Fin R.N} {q : Msg} {M : List Fact} {C : List Confirmed} (hn : n.val < S.undo.length)
    (hb : BindingOkM R dec S) (hno : ∀ k, NodeOkD R dec S net k (V k)) (hnet : NetOkD R S net)
    (hok : SendOkD R S n q M C) (hshape : MsgShape q) (hmask : MsgMask R q)
    (hnum : q.ty = .readIndexResp → MsgNums (2 ^ 61) q) :
    NetOkD R (sendS S n.val M C) (net ++ [q]) := by
  have hsub := hok.sub
  have hge := effTerm_sendS_ge (M := M) (C := C) hn
  have hb14 : ConfirmedOk R.N S := hb.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨fun m hm => ?_, fun m hm hty j hdst => ?_, fun m hm => ?_, fun m hm hty i hsrc hro hct => ?_,
    fun m hm => ?_, fun m hm => ?_, fun m hm => ?_⟩
  · rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨hty, ⟨i, hsrc, h2, h3⟩, j, hdst, hj⟩ := hnet.1 m hm
      refine ⟨hty, ⟨i, hsrc, h2.imp id (fun ⟨k, hk⟩ => ⟨k, Int.le_trans hk (hge k.val)⟩), h3⟩, j, hdst,
        fun hle => ?_⟩
      obtain ⟨r1, r2, r3, r4⟩ := hj (Int.le_trans (hge j.val) hle)
      refine ⟨r1, fun ht => ?_, fun ht => hsub _ (r3 ht), fun ht i hi => AckInD.sendS hn hsub (r4 ht i hi)⟩
      obtain ⟨f, hf, hfm⟩ := r2 ht
      exact ⟨f, hf, hsub f hfm⟩
    · rw [List.mem_singleton] at hm
      subst hm
      obtain ⟨j, hj⟩ := hok.dst
      have hz : ∀ i : Fin R.N, 0 ≤ S.currentTerm[i.val]! := fun i => by
        rw [(hno i).1.1]; word
      refine ⟨by rcases hok.ty with h | h | h | h | h | h | h | h | h | h | h <;> simp [h], ?_, j, hj,
        fun _ => ⟨hok.req, hok.vote, hok.grant, fun ht i hi => ?_⟩⟩
      · by_cases hri : m.ty = .readIndex
        · obtain ⟨h0, i, hi⟩ := hok.fwd hri
          have hz0 : uint.Z m.term = 0 := by rw [h0]; rfl
          refine ⟨i, hi, .inr ⟨n, ?_⟩, fun _ => .inr ?_⟩
          · rw [effTerm_sendS_self hn, hz0]; exact hz n
          · change uint.Z m.term ≤ S.currentTerm[i.val]!
            rw [hz0]; exact hz i
        · obtain ⟨hs1, hs2⟩ := hok.src hri
          exact ⟨n, hs1, hs2.imp id (fun h => ⟨n, by rw [effTerm_sendS_self hn]; exact h⟩), fun _ => hs2⟩
      · have hin : i = n := nodeId_inj (hi.symm.trans (hok.src (by rw [ht.1]; decide)).1)
        subst hin
        obtain ⟨a, ha, h1, h2, h3, h4, h5⟩ := hok.ack ht
        exact ⟨a, ha, h1, by rw [h2, hi], h3, h4, h5, AckOut.sendS hn (fun h => absurd rfl h)⟩
  · refine ⟨fun hle => ?_, fun u hu hm' hut => ?_⟩
    · change ((C[j.val]!).term = uint.Z m.term ∧ uint.Z m.commit ≤ (C[j.val]!).index) ∨
        uint.Z m.commit ≤ S.commitIndex[j.val]!
      rcases List.mem_append.mp hm with hm | hm
      · have hold := (hnet.2.1 m hm hty j hdst).1 hle
        by_cases hjn : j = n
        · subst hjn
          rcases hok.cmono with e | ⟨e1, -, e3⟩
          · rw [e]; exact hold
          · rcases hold with ⟨o1, o2⟩ | o
            · have hle' := (hb14 j).2
              have hle0 : S.currentTerm[j.val]! ≤ uint.Z m.term := hle
              have ht : (S.confirmed[j.val]!).term = (C[j.val]!).term := by
                rw [e1]; omega
              exact .inl ⟨ht.symm.trans o1, Int.le_trans o2 (e3 ht)⟩
            · exact .inr o
        · rw [hok.cother j hjn]; exact hold
      · rw [List.mem_singleton] at hm
        subst hm
        exact hok.hb hty j hdst hle
    · obtain ⟨-, hu'⟩ := sendS_undo_some hn hu
      rcases List.mem_append.mp hm with hm | hm
      · exact (hnet.2.1 m hm hty j hdst).2 u hu' hm' hut
      · rw [List.mem_singleton] at hm
        subst hm
        exact hok.hbU hty j hdst u hu' hm' hut
  · rcases List.mem_append.mp hm with hm | hm
    · exact hnet.2.2.1 m hm
    · rw [List.mem_singleton] at hm; subst hm; exact hshape
  · rcases List.mem_append.mp hm with hm | hm
    · exact hnet.2.2.2.1 m hm hty i hsrc hro hct
    · rw [List.mem_singleton] at hm
      subst hm
      have hi : i = n := nodeId_inj (hsrc.symm.trans (hok.src (by rcases hty with h | h <;> rw [h] <;> decide)).1)
      subst hi
      exact hok.lcm hty hro hct
  · rcases List.mem_append.mp hm with hm | hm
    · exact hnet.2.2.2.2.1 m hm
    · rw [List.mem_singleton] at hm; subst hm; exact hmask
  · rcases List.mem_append.mp hm with hm | hm
    · exact hnet.2.2.2.2.2.1 m hm
    · rw [List.mem_singleton] at hm; subst hm; exact hok.pvo
  · rcases List.mem_append.mp hm with hm | hm
    · exact hnet.2.2.2.2.2.2 m hm
    · rw [List.mem_singleton] at hm; subst hm; exact hnum

/-- **The relation after a `send`, B2** (`send_rel` over `AntSimD`). -/
theorem send_relD {R : RunCfg} {dec : CCDec} {S : State} {V : Fin R.N → NodeView} {net : List Msg}
    {xnet : List XMsg} {G : RaftFacts} {n : Fin R.N} {q : Msg} {rest : List Msg} {M : List Fact}
    {C : List Confirmed} (hbat : R.drv.batch = false)
    (hs : AntSimD R dec S V net xnet) (hgo : GlobalOk R S net G) (hpend : (V n).pend = q :: rest)
    (hmf : MsgFacts G q) (hok : SendOkD R S n q M C) (hshape : MsgShape q)
    (hcm : C[n.val]! = S.confirmed[n.val]! ∨ S.currentTerm[n.val]! = uint.Z (V n).ps.term)
    (hnum : q.ty = .readIndexResp → MsgNums (2 ^ 61) q) :
    AntSimD R dec (sendS S n.val M C) (setV V n { V n with pend := rest, undo := none, made := true })
        (net ++ [q]) xnet ∧
      GlobalOk R (sendS S n.val M C) (net ++ [q]) G := by
  obtain ⟨hsh, ⟨hb, hub⟩, hnet, hxn, hno⟩ := hs
  have hmask : MsgMask R q :=
    (hno n).2.2.2.2.2.2.2.1.2.2.2.2.2.2.1 q (by rw [hpend]; exact List.mem_cons_self ..)
  obtain ⟨sh0, sh1, sh2, sh3, sh4, sh5, sh6, sh7, sh8, sh9, sh10, sh11, sh12, sh13, sh14⟩ := hsh
  have hn : n.val < S.undo.length := by rw [sh11]; exact n.isLt
  refine ⟨⟨⟨sh0, sh1, sh2, sh3, sh4, sh5, sh6, sh7, sh8, sh9, hok.clen, by simpa [sendS] using sh11,
    sh12, sh13, sh14⟩, ⟨hok.bindingOk hb, hok.undoBindOk hn hub⟩,
    SendOkD.netOkD hn hb hno hnet hok hshape hmask hnum,
    fun x hx => (hxn x hx).imp fun i hi => Int.le_trans hi (effTerm_sendS_ge hn i.val), fun k => ?_⟩, ?_⟩
  · by_cases hk : k = n
    · subst hk
      simp only [setV, ite_true]
      have hsy := (hno k).2.2.1
      refine NodeOkD.sendD hn hbat hok (hno k) hcm rest
        (fun x hx => by rw [hpend]; exact List.mem_cons_of_mem _ hx) none true ⟨?_, ?_⟩
        (fun a b c d => ⟨(hsy a b c d).1, (hsy a b c d).2.1, fun h => absurd rfl h⟩)
        (fun d hd => by simp at hd) (fun _ _ h => absurd rfl h)
      · change ((S.undo.set k.val none)[k.val]!).isNone = true ↔ (none : Option DurW) = none
        rw [get!_set_self _ hn]; simp
      · intro p hp
        change (S.undo.set k.val none)[k.val]! = some p at hp
        rw [get!_set_self _ hn] at hp; cases hp
    · simp only [setV, hk, ite_false]
      have hne : k.val ≠ n.val := fun h => hk (Fin.ext h)
      have hu : UndoIs (sendS S n.val M C) k (V k) := by
        unfold UndoIs
        rw [show (sendS S n.val M C).undo[k.val]! = S.undo[k.val]! from get!_set_ne _ _ hne]
        exact (hno k).2.2.2.1
      obtain ⟨-, -, d3, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, d20, -, -, -, d24, -⟩ := hno k
      exact NodeOkD.sendD (v := V k) hn hbat hok (hno k) (.inl (hok.cother k hk)) (V k).pend
        (fun x hx => hx) (V k).undo (V k).made hu d3 d20 d24
  · obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := hgo
    refine ⟨g1, g2, g3, g4, g5, g6, fun m hm ht => ?_, g8, g9⟩
    rcases List.mem_append.mp hm with hm | hm
    · exact g7 m hm ht
    · rw [List.mem_singleton] at hm; subst hm; exact hmf.1 ht

/-! ## A `-parallel` leader's request before its write -/

/-- The last queued `mem`'s commit is the one the disk reaches by the queued writes. -/
theorem foldl_write_commit (l : List MemRec) (d : DurW) (x : MemRec) (h : l.getLast? = some x) :
    (l.foldl DurW.write d).commit = x.commit := by
  induction l generalizing d with
  | nil => simp at h
  | cons a t ih =>
    cases t with
    | nil => simp at h; subst h; rfl
    | cons b t' =>
      rw [List.foldl_cons]
      exact ih (DurW.write d a) (by rw [List.getLast?_cons_cons] at h; exact h)

/-- **A leader's request is `Sendable` from its in-memory commit** (`leader_sendable` with the commit
recorded at its `mem`, `MemCommitOk`, in place of the disk's). -/
theorem leader_sendableM {S : State} {N : Nat} {n : Fin N} {v : NodeView}
    (hld : S.leaders.contains { server := nameOf (nodeId n), term := uint.Z v.ps.term } = true)
    (hll : S.ledLog.get (uint.Z v.ps.term) = .ok (logOf v.ps.log))
    (hmc : uint.Z v.ps.commit ≤ S.chain.length ∧
      S.chain.take (uint.nat v.ps.commit) = (logOf v.ps.log).take (uint.nat v.ps.commit) ∧
      (v.ps.commit = W64 0 ∨ ∃ p ∈ S.termLen, p.1 ≤ uint.Z v.ps.term ∧ uint.Z v.ps.commit ≤ p.2))
    (dst : Str) {p pt c : w64} {es : List EntryM}
    (hpt : plogTermAt base0 v.ps.log p = some pt) (hes : (v.ps.log.drop (uint.nat p)).take es.length = es)
    (hcm : uint.Z c ≤ uint.Z v.ps.commit) :
    S.sendable ⟨nameOf (nodeId n), dst, uint.Z v.ps.term, uint.Z p, uint.Z pt, logOf es, uint.Z c⟩ =
      .ok true := by
  obtain ⟨hp, hptt⟩ := termAt_of_plog hpt
  obtain ⟨m1, m2, m3⟩ := hmc
  have hpZ : ((uint.nat p : Nat) : Int) = uint.Z p := by word
  have hcZ : ((uint.nat c : Nat) : Int) = uint.Z c := by word
  have hCZ : ((uint.nat v.ps.commit : Nat) : Int) = uint.Z v.ps.commit := by word
  have hlen := congrArg List.length m2
  simp only [List.length_take, logOf_length] at hlen
  have hrec : uint.nat c = 0 ∨ (uint.nat c ≤ v.ps.log.length ∧ uint.nat c ≤ S.chain.length ∧
      (∃ x ∈ S.termLen, x.1 ≤ uint.Z v.ps.term ∧ ((uint.nat c : Nat) : Int) ≤ x.2) ∧
      S.chain.take (uint.nat c) = (logOf v.ps.log).take (uint.nat c)) := by
    rcases m3 with h0 | ⟨x, hx, hx1, hx2⟩
    · left; rw [h0] at hcm; have : uint.Z (W64 0) = 0 := rfl; omega
    · right
      refine ⟨by omega, by omega, ⟨x, hx, hx1, by omega⟩, ?_⟩
      have e : uint.nat c = min (uint.nat c) (uint.nat v.ps.commit) := by omega
      rw [e, ← List.take_take, ← List.take_take, m2]
  have := sendable_leader (S := S) (dst := dst) (pt := uint.Z pt) hld hll (by rw [hpZ]; exact hptt)
    (by omega) hes hrec
  rw [hpZ, hcZ] at this
  exact this

/-- `SendOkD` of a leader's request (an append or a heartbeat), which adds no fact. -/
theorem SendOkD.ofReq {R : RunCfg} {dec : CCDec} {S : State} {n : Fin R.N} {q : Msg} (hsh : Shape R S)
    (hb : BindingOkW R dec S) (hty : q.ty = .app ∨ q.ty = .heartbeat)
    (hsrc : q.src = nodeId n ∧ uint.Z q.term ≤ S.currentTerm[n.val]!) (hdst : ∃ j : Fin R.N, q.dst = nodeId j)
    (hreq : (toAppendFact (msgOf q q.dst) >>= S.sendable) = .ok true)
    (hhb : q.ty = .heartbeat → ∀ j : Fin R.N, q.dst = nodeId j → S.currentTerm[j.val]! ≤ uint.Z q.term →
      ((S.confirmed[j.val]!).term = uint.Z q.term ∧ uint.Z q.commit ≤ (S.confirmed[j.val]!).index) ∨
        uint.Z q.commit ≤ S.commitIndex[j.val]!)
    (hlcm : ∃ c, S.memCommit n.val = .ok c ∧ uint.Z q.commit ≤ c)
    (hbU : q.ty = .heartbeat → ∀ j : Fin R.N, q.dst = nodeId j → ∀ u : Pre, S.undo[j.val]! = some u →
      u.made = false → u.term ≤ uint.Z q.term →
      (u.confirmed.term = uint.Z q.term ∧ uint.Z q.commit ≤ u.confirmed.index) ∨
        uint.Z q.commit ≤ u.commit) :
    SendOkD R S n q S.msgs S.confirmed where
  sub := fun _ h => h
  new := fun _ h h' => absurd h h'
  clen := hsh.2.2.2.2.2.2.2.2.2.2.1
  cother := fun _ _ => rfl
  conf := hb.2.2.2.2.1 n
  acks := hb.2.2.2.2.2.1 n
  ty := by rcases hty with h | h <;> simp [h]
  src := fun _ => ⟨hsrc.1, .inr hsrc.2⟩
  fwd := fun h => by rcases hty with h' | h' <;> rw [h'] at h <;> cases h
  pvo := fun _ => by rcases hty with h | h <;> simp [h]
  dst := hdst
  req := fun _ => hreq
  vote := fun h => by rcases hty with h' | h' <;> rw [h'] at h <;> cases h
  grant := fun h => by have h1 := h.1; rcases hty with h' | h' <;> rw [h'] at h1 <;> cases h1
  ack := fun h => by have h1 := h.1; rcases hty with h' | h' <;> rw [h'] at h1 <;> cases h1
  ackt := fun _ h h' => absurd h h'
  cmono := .inl rfl
  hb := hhb
  lcm := fun _ _ _ => hlcm
  hbU := hbU

/-- **`send` (sync, unbatched) over `AntSimD`**, for the runs a mask below `mskB2` admits: after the
node's write (no queued `mem`), or a `-parallel` leader's request before it. -/
theorem antSim_sendD_in (msk : SimMask) (hmsk : msk ≤ mskB2) :
    ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView)
      (net : List Msg) (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts)
      (n : Fin R.N) (q : Msg) (rest : List Msg),
      InMask msk R net xnet → SimPreD R dec S V net xnet evs G → R.md.async = false →
      R.drv.batch = false → (V n).pend = q :: rest → Told (V n) → MsgFacts G q →
      (q.ty = .readIndexResp → MsgNums (2 ^ 61) q) → (V n).parts = [] →
      ((V n).mems = [] ∨ isReqM q = true) →
      SimStepD R dec evs G (evSend (nodeId n) (V n).byE q)
        (setV V n { V n with pend := rest, undo := none, made := true }) (net ++ [q]) xnet := by
  intro R dec S V net xnet evs G n q rest hin ⟨hp, hs, hl, hgo⟩ ha hbat hpend htold hmf hnum hparts hmr
  obtain ⟨hsn, -, -⟩ := hin.b2 hmsk
  obtain ⟨S1, hgc, hs1, hgo1⟩ := antSim_gcD hbat hs hl hgo
  have hqp : q ∈ (V n).pend := by rw [hpend]; exact List.mem_cons_self ..
  have hq7 : q.ty = .app ∨ q.ty = .appResp ∨ q.ty = .vote ∨ q.ty = .voteResp ∨ q.ty = .heartbeat ∨
      q.ty = .heartbeatResp ∨ q.ty = .propose ∨ q.ty = .preVote ∨ q.ty = .preVoteResp ∨
      q.ty = .readIndex ∨ q.ty = .readIndexResp := by
    have hmk := (hs1.2.2.2.2 n).2.2.2.2.2.2.2.1.2.2.2.2.2.2.1 q hqp
    have hns : q.ty ≠ .snap := hmk.2.1 hsn
    rcases hmk.2.2.1 with (h | h | h | h | h | h | ⟨-, h | h⟩ | ⟨-, h | h⟩ | ⟨-, h⟩) | h
    all_goals first | exact absurd h hns | simp [h]
  suffices h : ∃ M C, S1.step (evSend (nodeId n) (V n).byE q) = .ok (some (sendS S1 n.val M C)) ∧
      SendOkD R S1 n q M C ∧
      (C[n.val]! = S1.confirmed[n.val]! ∨ S1.currentTerm[n.val]! = uint.Z (V n).ps.term) by
    obtain ⟨M, C, hst, hok, hcm⟩ := h
    have hshape := pendOk_shape ((hs1.2.2.2.2 n).2.2.2.2.2.2.2.2.2.2.1 hbat q hqp) hq7
    obtain ⟨hs2, hgo2⟩ := send_relD hbat hs1 hgo1 hpend hmf hok hshape hcm hnum
    exact ⟨_, Prefix.snoc hp hgc hst (violated_nil hs2.2.1.1.1 hl hgo2), hs2, hgo2⟩
  obtain ⟨hsh, ⟨hb, hub⟩, hn, -, hno⟩ := hs1
  have hcz : ∀ j : Fin R.N, 0 ≤ S1.commitIndex[j.val]! := fun j => by rw [(hno j).1.2.2.2]; word
  obtain ⟨d1, d2, -, -, d5, -, -, hf, hL, -, hpo, -, -, -, -, -, -, -, -, -, hdf, -, -, hum, hmc⟩ := hno n
  obtain ⟨hne, ⟨j, hj⟩, hcase⟩ := hpo hbat q hqp
  have hc : S1.cfg = R.cfg := hsh.1
  have hsrv : S1.cfg.server.has (nameOf q.dst) = true := by rw [hc, hj]; exact cfg_has R j
  have hne' : (nameOf q.dst != nameOf (nodeId n)) = true := by
    rw [bne_iff_ne]; intro h; exact hne (nameOf_inj h)
  -- a leader's heartbeat's commit against its receiver's undo record
  have hbU : q.ty = .heartbeat → ∀ j : Fin R.N, q.dst = nodeId j → ∀ u : Pre, S1.undo[j.val]! = some u →
      u.made = false → u.term ≤ uint.Z q.term →
      (u.confirmed.term = uint.Z q.term ∧ uint.Z q.commit ≤ u.confirmed.index) ∨
        uint.Z q.commit ≤ u.commit := by
    intro hty
    simp only [hty] at hcase
    obtain ⟨hrole, ⟨-, -, h2, -, -, hmt⟩, -⟩ := hcase
    exact hbU_of_leader hub hL hrole hne h2 hmt
  rcases hm : (V n).mems with _ | ⟨w, ws⟩
  · -- after the write: B1's case analysis at the run with the driver modes off
    have hd : (V n).dur = durOf (V n).r := by have := hdf hparts; rw [hm] at this; exact this
    have hno' : NodeOk R.syncOff dec S1 net n (V n) :=
      nodeOkD_syncOff ha hbat hm hparts hd (hum ha hbat) (hno n)
    have hcs : ∀ m ∈ net, m.dst = nodeId n → S1.currentTerm[n.val]! ≤ uint.Z m.term → m.ty = .app →
        (toAppendFact (msgOf m m.dst) >>= S1.sendable) = .ok true := by
      intro m hm' hd' hle hty
      obtain ⟨-, -, j', hj', hjk⟩ := hn.1 m hm'
      have e : j' = n := nodeId_inj (hj'.symm.trans hd')
      subst e
      exact (hjk (Int.le_trans (effTerm_le _ _) hle)).1 (.inl hty)
    obtain ⟨M, C, hst, hok⟩ := sendD_step (R := R.syncOff) hsn hsh (BindingOkM.toW hb) hl hgo1 hcs
      hn.2.2.2.2.2.1 hcz hno' hd hpend htold hq7
    have hok' : SendOk R S1 n q M C :=
      { sub := hok.sub, new := hok.new, clen := hok.clen, cother := hok.cother, conf := hok.conf,
        acks := hok.acks, ty := hok.ty, src := hok.src, fwd := hok.fwd, pvo := hok.pvo, dst := hok.dst,
        req := hok.req, vote := hok.vote, grant := hok.grant, ack := hok.ack, ackt := hok.ackt,
        cmono := hok.cmono, hb := hok.hb, lcm := hok.lcm }
    have hqn : S1.queue[n.val]! = [] := by rw [d5, hm]; rfl
    exact ⟨M, C, hst, hok'.toD hqn hbU, .inr (by rw [d1.1, hd]; rfl)⟩
  · -- a `-parallel` leader's request before its write
    have hreq : isReqM q = true := hmr.resolve_left (by rw [hm]; simp)
    have hq2 : q.ty = .app ∨ q.ty = .heartbeat := of_decide_eq_true hreq
    have hfp : (V n).r.fp = [] := (hf.2.1 hsn).2.1
    have hb0 : (V n).ps.base = base0 := (hf.2.1 hsn).1
    have hfull : (V n).r.full = (V n).ps.log := by unfold RState.full; rw [hfp]; rfl
    have hrole : (V n).ps.role = .leader := by
      rcases hq2 with hty | hty <;> simp only [hty] at hcase <;> exact hcase.1
    obtain ⟨l1, l2, -, l4, -⟩ := hL hrole
    rw [hfull] at l2
    have hct : S1.currentTerm[n.val]! = uint.Z (V n).ps.term := by
      have h8 := hb.2.2.2.2.2.2.2.1 n _ (List.contains_iff_mem.mp l1) rfl
      have hdt := hf.2.2.2.2.2.2.2.1
      rw [d1.1] at h8 ⊢
      simp only at h8
      omega
    have hrl : S1.role[n.val]! = leader := by rw [d2.1, hrole]; rfl
    obtain ⟨m1, m2, m3⟩ := hmc hparts
    rw [hfull] at m2
    have hmc' : uint.Z (V n).ps.commit ≤ S1.chain.length ∧
        S1.chain.take (uint.nat (V n).ps.commit) = (logOf (V n).ps.log).take (uint.nat (V n).ps.commit) ∧
        ((V n).ps.commit = W64 0 ∨ ∃ p ∈ S1.termLen, p.1 ≤ uint.Z (V n).ps.term ∧
          uint.Z (V n).ps.commit ≤ p.2) := ⟨m1, m2, m3⟩
    have hmcm : S1.memCommit n.val = .ok (uint.Z (V n).ps.commit) := by
      have hfold := congrArg DurW.commit (hdf hparts)
      rw [hm] at hfold
      cases hx : (w :: ws).getLast? with
      | none => simp at hx
      | some x =>
        rw [foldl_write_commit _ _ x hx] at hfold
        unfold State.memCommit
        rw [d5, hm, List.getLast?_map, hx]
        simp only [Option.map_some]
        unfold MemRec.item
        split <;> (simp only [evMemB, evMem, need, hfold]; rfl)
    have hhbs : q.ty = .heartbeat → ∀ j' : Fin R.N, q.dst = nodeId j' →
        S1.currentTerm[j'.val]! ≤ uint.Z q.term →
        ((S1.confirmed[j'.val]!).term = uint.Z q.term ∧ uint.Z q.commit ≤ (S1.confirmed[j'.val]!).index) ∨
          uint.Z q.commit ≤ S1.commitIndex[j'.val]! := by
      intro hty j' hj' hle
      simp only [hty] at hcase
      obtain ⟨-, ⟨-, -, h2, -, -, hmt⟩, -⟩ := hcase
      have hjn : j' ≠ n := fun e => hne (by rw [hj', e])
      obtain ⟨-, -, -, -, -, hb8, -, -, -, -, -, hb14, -, -, -, -, -⟩ := hb
      have hc0 : 0 ≤ S1.commitIndex[j'.val]! := hcz j'
      rw [hj'] at hmt
      rcases l4 j' hjn with h0 | ⟨a, ha, haty, hasrc, -, hat, hai, -⟩
      · right; rw [h0] at hmt; have : uint.Z (W64 0) = 0 := rfl; omega
      · have hqt : uint.Z q.term = uint.Z (V n).ps.term := by rw [h2]
        have hat' : a.term = S1.currentTerm[j'.val]! := by
          have := hb14 j' a ha haty hasrc
          omega
        rcases hb8 j' a ha haty hasrc hat' with ⟨c1, c2⟩ | c
        · left; exact ⟨by omega, by omega⟩
        · right; omega
    rcases hq2 with hty | hty
    · simp only [hty] at hcase
      obtain ⟨-, -, h1, h2, -, hpt, hcm, -, hpre, hpay⟩ := hcase
      have hterm : S1.currentTerm[n.val]! = uint.Z q.term := by rw [hct, h2]
      rw [hb0] at hpt hpre
      have hes : ((V n).ps.log.drop (uint.nat q.index)).take q.entries.length = q.entries := by
        have hp2 := hpay.2
        have hw : uint.Z (q.index + W64 1) = uint.Z q.index + 1 := by word
        unfold plogFrom at hpre
        rw [hw, base0_index] at hpre
        have e : (uint.Z q.index + 1 - 0 - 1).toNat = uint.nat q.index := by word
        rw [e] at hpre
        exact (List.prefix_iff_eq_take.mp hpre).symm
      have hsd := leader_sendableM l1 l2 hmc' (nameOf q.dst) hpt hes hcm
      rw [← h2] at hsd
      exact ⟨_, _, send_app_eq n q _ hc hsrv hne' hty h1 hterm hrl hsd,
        SendOkD.ofReq hsh (BindingOkM.toW hb) (.inl hty) ⟨h1, by omega⟩ ⟨j, hj⟩
          (by rw [toAppendFact_msgOf, eok_bind, h1]; exact hsd) (fun h => nomatch hty.symm.trans h)
          ⟨_, hmcm, hcm⟩ (fun h => nomatch hty.symm.trans h), .inl rfl⟩
    · have hcase' := hcase
      simp only [hty] at hcase'
      obtain ⟨-, ⟨-, h1, h2, -, hcm, -⟩, hi0, hlt0, hen⟩ := hcase'
      have hterm : S1.currentTerm[n.val]! = uint.Z q.term := by rw [hct, h2]
      have hpt : plogTermAt base0 (V n).ps.log (W64 0) = some (W64 0) := by
        unfold plogTermAt; simp [base0]
      have hsd0 := leader_sendableM (es := []) l1 l2 hmc' (nameOf q.dst) hpt rfl hcm
      have hsd : S1.sendable ⟨nameOf (nodeId n), nameOf q.dst, uint.Z q.term, uint.Z q.index,
          uint.Z q.logterm, logOf q.entries, uint.Z q.commit⟩ = .ok true := by
        rw [hi0, hlt0, hen, h2]; exact hsd0
      exact ⟨_, _, send_hb_eq n q _ hc hsrv hne' hty h1 hterm hrl hsd,
        SendOkD.ofReq hsh (BindingOkM.toW hb) (.inr hty) ⟨h1, by omega⟩ ⟨j, hj⟩
          (by rw [toAppendFact_msgOf, eok_bind, h1]; exact hsd) hhbs ⟨_, hmcm, hcm⟩ hbU, .inl rfl⟩

end sendD

end AntSim
end EtcdGrove
end Perennial
