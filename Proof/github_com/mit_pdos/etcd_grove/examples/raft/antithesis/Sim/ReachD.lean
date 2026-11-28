/-
Lean-first (no Rocq counterpart).

# Parity B2: `ReachIn` over the B2 node part (`NodeOkD`)

`Sim/MsgShape`'s `reach_fp` and `dst_reach`, and `Sim/Scope`'s `ReachIn.toP`, over `NodeOkD`/`NetOkD`
for the masks below `mskB2`, unbatched (#33 parity B2, round 6): the harness's `reach_fpD.law` and
`dst_reachD.law` (`DrainB2Laws`). The B1 proofs read only the node's facts, its self-addressed queue and
its leader hint, which `NodeOkD` has as `NodeOk` does (the outbox empty without batching; a transfer's
term within the disk's, which is within raft's).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.QuietP
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.MsgShape
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.CarryD

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open GMap go_etcd_io.raft.v3

section reachD
variable [GooseExts]

theorem nodeOkD_factsS {R : RunCfg} {dec : CCDec} {S : AntCheck.State} {net : List Msg} {n : Fin R.N}
    {v : NodeView} (h : NodeOkD R dec S net n v) : NodeFactsD R n v :=
  h.2.2.2.2.2.2.2.1

theorem nodeOkD_qsS {R : RunCfg} {dec : CCDec} {S : AntCheck.State} {net : List Msg} {n : Fin R.N}
    {v : NodeView} (h : NodeOkD R dec S net n v) : ∀ q ∈ v.qs, QsOk R S n v q ∨ QsAckW n v q :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem qsD_ty3 {R : RunCfg} {S : AntCheck.State} {n : Fin R.N} {v : NodeView} {q : Msg}
    (h : QsOk R S n v q ∨ QsAckW n v q) : q.ty = .appResp ∨ q.ty = .voteResp ∨ q.ty = .preVoteResp :=
  h.elim QsOk.ty3 fun h => .inl h.2.2.2.1

theorem qsD_self {R : RunCfg} {S : AntCheck.State} {n : Fin R.N} {v : NodeView} {q : Msg}
    (h : QsOk R S n v q ∨ QsAckW n v q) (hne : q.ty ≠ .preVoteResp) : SelfMsg (nodeId n) v.ps.term q :=
  h.elim (fun h => h.self hne) fun ⟨h1, h2, h3, h4, h5, _⟩ => ⟨h1, h2, h5, h3, .inl h4⟩

/-- `AdvanceEnd.split` over the B2 queue (a leader's self-acknowledgement may wait for its write,
`QsAckW`). -/
theorem AdvanceEnd.splitD {R : RunCfg} {S : AntCheck.State} {n : Fin R.N} {v : NodeView} {k : NodeK}
    {c : CfgM} {s' : PState} (hqs : ∀ q ∈ v.qs, QsOk R S n v q ∨ QsAckW n v q)
    (h : AdvanceEnd k c (nodeId n) v.ps v.qs s') :
    (∀ q ∈ v.qs, q.ty ≠ .preVoteResp) ∨
    ((∀ q ∈ v.qs, q.ty = .preVoteResp ∧ q.reject = false) ∧ nodeId n ∈ v.r.cfg.cfg.voters ∧
      (R.k n).prevote = true ∧
      (s' = v.ps ∨ (v.ps.role = .follower ∧ v.ps.lead = W64 0 ∧ CampaignSends c (nodeId n) v.ps [] s'))) := by
  by_cases hex : ∃ q ∈ v.qs, q.ty = .preVoteResp
  · obtain ⟨q, hq, hty⟩ := hex
    have hpo : ∀ q' ∈ v.qs, q'.ty = .preVoteResp → QsOk R S n v q' := fun q' hq' ht =>
      (hqs q' hq').resolve_right fun hw => by rw [hw.2.2.2.1] at ht; cases ht
    obtain ⟨-, -, -, ⟨-, h1 | h1⟩ | ⟨-, -, hvt, hpv, hall⟩⟩ := hpo q hq hty
    · rw [hty] at h1; cases h1.1
    · rw [hty] at h1; cases h1.1
    have hpr : ∀ q ∈ v.qs, q.ty = .preVoteResp ∧ q.reject = false :=
      fun q' hq' => ⟨hall q' hq', (hpo q' hq' (hall q' hq')).2.2.1⟩
    exact .inr ⟨hpr, hvt, hpv, advanceEnd_pre hpr h⟩
  · exact .inl fun q hq hty => hex ⟨q, hq, hty⟩

theorem nodeOkD_leadOkS {R : RunCfg} {dec : CCDec} {S : AntCheck.State} {net : List Msg} {n : Fin R.N}
    {v : NodeView} (h : NodeOkD R dec S net n v) : LeadOk n v :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem ReachIn.toPD {msk : SimMask} (hmsk : msk ≤ mskB2) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {net : List Msg} {xnet : List XMsg} {n : Fin R.N}
    {S : AntCheck.State} {v : NodeView} {r₁ : RState} (hin : InMask msk R net xnet)
    (hnet : NetOkD R S net) (hv : NodeOkD R dec S net n v)
    (hr : ReachIn msk R dec Adm net xnet n v r₁) :
    ReachP (R.k n) v.r.cfg.cfg (nodeId n) net xnet v r₁.p := by
  have hm1 := SimMask.b1Of_le hmsk
  have hr := hr.syncOff
  obtain ⟨hmd, -, -, -, -, hty⟩ := hin.syncOff.b1 hm1
  have hcc : R.md.confChanges = false := (InMask.b2 hmsk hin).2.1
  have hf := nodeOkD_factsS hv
  have hdt : uint.Z v.dur.term ≤ uint.Z v.ps.term := hf.2.2.2.2.2.2.2.1
  cases hr with
  | stay hi hb => exact .stay _ hi hb
  | input inp _ hinp hi hbe hca hxc hm hx hs =>
    rcases Input.step_b1 hm1 hinp hs with ⟨m, rfl⟩ | ⟨hti, hs⟩ | ⟨d, rfl⟩ | ⟨d, rfl⟩ | ⟨x, rfl⟩ |
        ⟨to, rfl⟩ | ⟨⟨t, rfl⟩, rfl⟩
    · obtain ⟨hmn, hmd', hm0⟩ := hm m rfl
      have hne : ∀ {t : MsgType}, m.ty = t → (t = .preVote ∨ t = .preVoteResp) → m.term ≠ W64 0 :=
        fun he ht => hm0 (by rw [he]; rcases ht with rfl | rfl <;> nofun)
      rcases hty m hmn with h4 | hpt | hpt
      · exact .recv _ m _ hi hbe hca hmn hmd' hm0 h4 hs.1
      · exact .recvP _ m _ hi hbe hca hmn hmd' (hne hpt (.inl rfl)) (.inl hpt)
          (fun h1 => by rw [hpt] at h1; cases h1) hs.1
      · refine .recvP _ m _ hi hbe hca hmn hmd' (hne hpt (.inr rfl)) (.inr hpt) (fun h1 h2 => ?_) hs.1
        have := ((hnet.2.2.2.2.2.1 m hmn) hcc).2 h1 h2
        rw [(hf.2.2.1 hcc).1, CfgM.voters_simple]; exact hmd' ▸ this
    · have hti' : TickBy v.byE := by rcases hti with rfl | rfl <;> simp [hbe, Input.byE, TickBy]
      exact .tick _ _ hi hti' hs.1
    · exact .propose _ d _ hi hbe (recvEnd_propMsg hs.1)
    · exact .read _ d _ hi hbe (recvEnd_readMsg hs.2.1)
    · obtain ⟨hxn, hxd, hxt⟩ := hx x rfl
      have hdb : DrainBy v.byE := .inr ⟨.recvX x, hbe⟩
      have hxc' : v.xcause = some x := hxc
      rcases hs with ⟨hty, ⟨-, rfl⟩ | ⟨hle, ⟨p1, hp1, hend⟩, -⟩⟩ | ⟨-, ⟨-, -, rfl⟩ | ⟨-, hT⟩ | ⟨hlt, rfl⟩⟩
      · exact .stay _ hi hdb
      · rcases hend with he | ⟨hl, hse⟩ | hce
        · rw [he]
          rcases hp1 with ⟨hlt, rfl⟩ | ⟨-, rfl⟩
          · exact .adoptX _ x hi hbe hxc' hxn hxd hlt
          · exact .stay _ hi hdb
        · rcases hp1 with ⟨-, rfl⟩ | ⟨-, rfl⟩
          · exact absurd hl (by simp [pbecomeFollower])
          · exact .sends _ _ hi hdb hl hse
        · exact .campX _ x p1 _ hi hbe hxc' hxn hxd hty hp1 hce.1 hce.2 (Int.le_trans (hxt hty) hdt)
      · exact .stay _ hi hdb
      · rcases transferEndR_p hT with he | ⟨hl, hse⟩
        · rw [he]; exact .stay _ hi hdb
        · exact .sends _ _ hi hdb hl hse
      · exact .adoptX _ x hi hbe hxc' hxn hxd hlt
    · rcases transferEndR_p hs with he | ⟨hl, hse⟩
      · rw [he]; exact .stay _ hi (.inr ⟨.transfer to, hbe⟩)
      · exact .sends _ _ hi (.inr ⟨.transfer to, hbe⟩) hl hse
    · exact .stay _ hi (.inr ⟨.unreachable t, hbe⟩)
  | advance _ hpd _ hce _ hb ha _ =>
    rcases AdvanceEnd.splitD (nodeOkD_qsS hv) (advanceEndR_toP ha) with hno | ⟨hpr, hvt, hpv, h⟩
    · exact .advance _ _ hpd hce hb hno (advanceEndR_toP ha)
    · exact .advP _ _ hpd hce hb hpr hvt hpv h

/-- **The ghost prefix is kept along `ReachIn`, B2** (`reach_fp` over `NodeOkD`). -/
theorem reach_fpD {msk : SimMask} (hmsk : msk ≤ mskB2) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {S : AntCheck.State} {net : List Msg} {xnet : List XMsg}
    {n : Fin R.N} {v : NodeView} {r₁ : RState} (hin : InMask msk R net xnet) (_hb : R.drv.batch = false)
    (hv : NodeOkD R dec S net n v) (hr : ReachIn msk R dec Adm net xnet n v r₁) :
    r₁.fp = v.r.fp := by
  have hm1 := SimMask.b1Of_le hmsk
  have hr := hr.syncOff
  obtain ⟨-, -, -, -, -, hty⟩ := hin.syncOff.b1 hm1
  cases hr with
  | stay _ => rfl
  | input inp _ hinp _ _ _ _ hm _ hs =>
    rcases Input.step_b1 hm1 hinp hs with ⟨m, rfl⟩ | ⟨-, hs⟩ | ⟨d, rfl⟩ | ⟨d, rfl⟩ | hx
    · obtain ⟨hmn, -, -⟩ := hm m rfl
      exact recvEndR_fp hs (b1rTy_ne_snap (hty m hmn))
    · exact hs.2.2.1
    · exact recvEndR_fp hs (by simp [propMsg])
    · exact recvEndR_fp hs.2 (by simp [readMsg])
    · exact (inputStep_x_keep hx hs).2.1
  | advance _ _ _ _ _ _ ha _ =>
    refine advanceEndR_fp ha fun q hq => ?_
    rcases qsD_ty3 (nodeOkD_qsS hv q hq) with h | h | h <;> rw [h] <;> decide

/-- **The destinations of the messages of the state a `Ready` is taken at, B2** (`dst_reach` over
`NetOkD`/`NodeOkD`, unbatched). -/
theorem dst_reachD {msk : SimMask} (hmsk : msk ≤ mskB2) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {S : AntCheck.State} {net : List Msg} {xnet : List XMsg}
    {n : Fin R.N} {v : NodeView} {r₁ : RState} (hin : InMask msk R net xnet) (hb : R.drv.batch = false)
    (hnet : NetOkD R S net) (hv : NodeOkD R dec S net n v)
    (hr : ReachIn msk R dec Adm net xnet n v r₁) : DstIn R.N (nodeId n) r₁.p := by
  have hcc := (InMask.b2 hmsk hin).2.1
  have hf := nodeOkD_factsS hv
  have hc : CfgIn R.N v.r.cfg.cfg := by
    rw [(hf.2.2.1 hcc).1]; exact cfgIn_voters0 R
  refine dst_reachP hc (hf.1 hb) (nodeOkD_leadOkS hv)
    ⟨hf.2.2.2.2.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
    (fun m hmn => by obtain ⟨i, hi, -⟩ := (hnet.1 m hmn).2.1; exact ⟨i, hi⟩)
    (fun q hq hne => ?_) (ReachIn.toPD hmsk hin hnet hv hr)
  obtain ⟨h1, -, -, -, h5⟩ := qsD_self (nodeOkD_qsS hv q hq) hne
  exact ⟨h5, h1⟩

end reachD

end AntSim
end EtcdGrove
end Perennial
