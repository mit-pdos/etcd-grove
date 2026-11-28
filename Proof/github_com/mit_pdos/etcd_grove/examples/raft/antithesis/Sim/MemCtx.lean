/-
Lean-first (no Rocq counterpart).

# Parity B2: a `-parallel` leader's `Ready` in context (`ldCtxD_of`)

A `-parallel` run is sync and unbatched. At a leader's reported `Ready` with no write queued and no
split write in progress (`antSim_memP_in`'s premises), the node's disk is raft's state (`DiskFold`),
so its B2 node part is the B1 one of the run with the driver modes off (`nodeOkD_syncOff`), read at
`liftC S1` (other nodes may have announced commits not yet written: `netOkD_toB1L`). That is
`LdCtx` at the state after `GC` (`antSim_gcD`), for the run with the driver modes off: the context
the B1 leader kinds' `InMemory` evaluations read (#33 parity B2, Sim round 10).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.LdCtx
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.QuietP
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.CarryD
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.MemEval

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open GMap go_etcd_io.raft.v3 AntCheck

section memCtx
variable [GooseExts]

/-- **`LdCtx` from `antSim_memP_in`'s premises** (with no write queued and no split write in
progress): `GC` to `S1`, `AntSimD` and `GlobalOk` there, and the node-local context of the run with
the driver modes off. -/
theorem ldCtxD_of {msk : SimMask} (hmsk : msk ≤ mskB2) {R : RunCfg} {dec : CCDec} {S : State}
    {V : Fin R.N → NodeView} {net : List Msg} {xnet : List XMsg} {evs : List Event} {G : RaftFacts}
    {n : Fin R.N} {r₁ : RState} {rd : ReadyD} {Adm : List EntryM → CCState → Prop}
    (hin : InMask msk R net xnet) (hpre : SimPreD R dec S V net xnet evs G)
    (ha : R.md.async = false) (hbat : R.drv.batch = false)
    (hm : (V n).mems = []) (hparts : (V n).parts = [])
    (hr : ReachIn msk R dec Adm net xnet n (V n) r₁) (hro : ReadyOutP R n (V n) r₁ rd)
    (hrep : Reported (V n) rd) (htold : Told (V n)) (hrf : ReadyFacts G (nodeId n) r₁)
    (htb : TermRoom (V n)) :
    ∃ S1, gcLoop (gcFuel S) S = .ok (S1, none) ∧ AntSimD R dec S1 V net xnet ∧
      GlobalOk R S1 net G ∧ LdCtx R.syncOff dec V net xnet G n r₁ rd S1 := by
  obtain ⟨-, hs, hl, hgo⟩ := hpre
  have hmsk' := SimMask.b1Of_le hmsk
  have hin' := hin.syncOff
  obtain ⟨hmd, hbt, hpar', hspl, -, -⟩ := hin'.b1 hmsk'
  obtain ⟨S1, hgc, hs1, hgo1⟩ := antSim_gcD hbat hs hl hgo
  refine ⟨S1, hgc, hs1, hgo1, ?_⟩
  have hsh := hs1.1
  have hvD := hs1.2.2.2.2 n
  have hu : (V n).undo ≠ none → (V n).made = false :=
    hvD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ha hbat
  have hd : (V n).dur = durOf (V n).r := by
    have := hvD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hparts
    rw [hm] at this; exact this
  have hqn : S1.queue[n.val]! = [] := by
    have hqi : QueueIs S1 n (V n) := hvD.2.2.2.2.1
    unfold QueueIs at hqi; rw [hqi, hm]; rfl
  have hv0 : NodeOk R.syncOff dec S1 net n (V n) := nodeOkD_syncOff ha hbat hm hd hu hvD
  have hv : NodeOk R.syncOff dec (liftC S1) net n (V n) := nodeOk_liftC hqn hv0
  have hnet : NetOk R.syncOff (liftC S1) net := netOkD_toB1L ha hsh.2.2.2.2.2.1 hs1.2.2.1
  have hr' := hr.syncOff
  have hsy := hv.sync (by rw [hmd]) hbt hspl hpar'
  have hsn0 := hv.facts.snap0 (by rw [hmd])
  have hfp0 : (V n).r.fp = [] := hsn0.2.1
  have hdl : (V n).dur.log = (V n).ps.log := by
    rw [hd]; show (V n).r.fp ++ (V n).r.p.log = _; rw [hfp0]; rfl
  have hfp : r₁.fp = [] := (reach_keep hmsk' hin' hv hr').1.2.1.trans hfp0
  have hfl : r₁.full = r₁.p.log := by unfold RState.full; rw [hfp]; rfl
  have hro' := hro
  obtain ⟨hR, hpre', -, -, -, -, -, -, -, -, -, -, -, -, hsnapC, -, -⟩ := hro'
  have hpf : rd.pre = true → rd.role = .follower := fun h => (hpre' h).1
  have hsnr : rd.snap = none := (hsnapC (by rw [show R.md = R.syncOff.md from rfl, hmd])).2.1
  have hcf : (V n).r.cfg.cfg = CfgM.simple R.voters0 ∅ := (hv.facts.conf0 (by rw [hmd])).1
  have hrP := ReachIn.toP hmsk' hin' hnet hv hr'
  rw [hcf] at hrP
  obtain ⟨e1, e2, e3, e4⟩ := hv0.disk
  obtain ⟨m1, -, m3, -⟩ := hv0.mem
  have hcv : (V n).conf = (V n).r.cfg := by
    rcases hv.confLag with h | ⟨h, -⟩
    · exact h.1
    · rw [hsn0.2.2] at h; cases h
  have d7 : (V n).ps.outbox = [] := hv.facts.outbox
  have d8 : (V n).ps.base = base0 := hsn0.1
  have hin2 : ∀ m ∈ net, RdTy m.ty → InMsg m := fun m hm h4 => ⟨h4, hnet.2.2.1 m hm⟩
  have hqs : ∀ q ∈ (V n).qs, q.ty ≠ .preVoteResp → SelfMsg (nodeId n) (V n).ps.term q :=
    fun q hq hne => (hv.qs q hq).self hne
  have hqc : (V n).ps.role = .candidate → ∀ q ∈ (V n).qs, q.ty ≠ .preVoteResp → q.ty = .voteResp :=
    fun hc q hq hne => by
      rcases ((hv.qs q hq).notPre hne).2.2.2.2 with ⟨-, hl, -⟩ | ⟨h, -⟩
      · rw [hc] at hl; cases hl
      · exact h
  have hkd : ReadyKind (CfgM.simple R.voters0 ∅) (nodeId n) net xnet (V n) r₁.p rd := by
    by_cases hch : Changed (V n) r₁.p
    · exact ready_kind hrP hro hfl hdl hsnr hch d8 (nodeId_ne_zero n) hv.voteSelf hin2 hqs hqc d7
    · exact kind_preFlag hro hfl hdl hch hrep hd hsnr hv.facts.preRole
  exact {
    hl := hl, hgo1 := hgo1, hsh := hsh, hb := hs1.2.1.1, hnet := hnet, hv := hv0, hdn := hd
    hlu := fun k hk hn => lead_uniqueD (R := R) hs1 hgo1 hl hk hn
    hc := hsh.1
    hn3 := by rw [hsh.2.2.2.2.2.2.1]; exact n.isLt
    hct3 := by rw [hsh.2.1]; exact n.isLt
    hlg3 := by rw [hsh.2.2.2.2.1]; exact n.isLt
    d1 := by rw [e1, hd]; rfl
    d2 := by rw [e2, hd]; rfl
    d3 := by rw [e3, hdl]
    d4 := by rw [e4, hd]; rfl
    d5 := m1
    d7 := d7, d8 := d8
    d9 := hdl ▸ hv.facts.logIdx
    hconf := by rw [m3, hcv]
    hcf := hcf
    hcc := by rw [hmd]
    hsnf := by rw [hmd]
    hq0 := hqn
    hpre := fun h => hR.symm.trans (hpf h)
    hsn := hsnr, hfl := hfl, hrf := hrf, hr := hrP, hro := hro
    htold := htold, htb := htb, hin := hin2, hqs := hqs, hqc := hqc
    hso := selfOut_reach hrP d7 hv.leadOk.1 hin2 (fun m hm => (hnet.2.2.1 m hm).2.1) hqs
    hvs := hv.voteSelf
    hvs1 := voteSelf_kind hkd hv.voteSelf
    hk := hkd }

end memCtx

end AntSim
end EtcdGrove
end Perennial
