/-
Lean-first (no Rocq counterpart). #33 parity B2, driver group E: **a synchronous `Ready` read at the
loop head under B2** (`DrainB1Report.readyOutP_b1` over `NodeOkD`): `readyOutP_d`, raft's `Ready` post
is the Sim's `ReadyOutP` there, with `Sim/ReachD`'s `reach_fpD`, `dst_reachD` (`reach_fp`, `dst_reach`
over `NodeOkD`) and the disk's log the view's full log (`hdl`: the caller's, from `DiskFold`
with no `mem` queued).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB1Report
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.StmtsB2
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.MsgShape
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.CarryD
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.ReachD

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- `NodeOkD`'s `NodeFactsD`. -/
theorem nodeOkD_facts {R : AntSim.RunCfg} {dec : CCDec} {S : AntCheck.State} {net : List Msg}
    {n : Fin R.N} {v : AntSim.NodeView} (h : AntSim.NodeOkD R dec S net n v) :
    AntSim.NodeFactsD R n v :=
  h.2.2.2.2.2.2.2.1

/-- **The disk is raft's own state with no `mem` queued** (`DiskFold`, outside a split write's
parts). -/
theorem nodeOkD_dur {R : AntSim.RunCfg} {dec : CCDec} {S : AntCheck.State} {net : List Msg}
    {n : Fin R.N} {v : AntSim.NodeView} (h : AntSim.NodeOkD R dec S net n v) (hm : v.mems = [])
    (hp : v.parts = []) : v.dur = AntSim.durOf v.r := by
  have hf : AntSim.DiskFold v := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have := hf hp
  rw [hm] at this
  exact this

/-- **Raft's `Ready` at a loop head is the Sim's `ReadyOutP`, B2** (`readyOutP_b1` over `NodeOkD`,
unbatched, synchronous): the disk's log the view's full log (`hdl`), no ghost prefix (`AntSim.reach_fpD`,
`NodeFactsD`), the messages' destinations servers (`AntSim.dst_reachD`), log matching from the two logs'
records. Also: the node's full log is its protocol log. -/
theorem readyOutP_d
    {msk : AntSim.SimMask} (hmsk : msk ≤ AntSim.mskB2)
    {R : AntSim.RunCfg} {dec : CCDec} {Adm : List EntryM → CCState → Prop}
    {S : AntCheck.State} {net : List Msg} {xnet : List XMsg} {j : Fin R.N} {v : AntSim.NodeView}
    {rs : RNState} {r : RState} {h : HardStateM} {es ce : List EntryM} {ms : List QMsg}
    {ss : Option (w64 × StateType)} {qs : List Msg} {sts : List ReadStateM} {ip : Nat}
    (hin : AntSim.InMask msk R net xnet) (hbt : R.drv.batch = false) (has : R.md.async = false)
    (hnet : AntSim.NetOkD R S net)
    (hok : AntSim.NodeOkD R dec S net j v) (hri : AntSim.ReachIn msk R dec Adm net xnet j v r)
    (hdl : v.dur.log = v.r.full)
    (hrv : RsView rs v) (hip : ip = lcpLen v.r.p.log r.p.log)
    (hout : ReadyOut (AntSim.nodeId j) rs r.p h es ce ms ss none)
    (hfirst : ∀ e0 ∈ es.head?, uint.nat e0.Index' = ip + 1)
    (hqs : qs.Perm (r.p.outbox.filter (fun m => decide (m.dst = AntSim.nodeId j))))
    (hpk : roleAfter rs.role ss = StatePreCandidate → (R.k j).prevote = true)
    (hx : ∀ x ∈ ms.filterMap (fun q => xmsgOf q.st), AntSim.XPendOk R.N (AntSim.nodeId j) r.p x)
    (hsts : sts = r.p.rd.states)
    (hns : r.p.base = base0 ∧ ∀ m ∈ r.p.outbox, m.ty ≠ .snap)
    (hwf : PlogWf base0 r.p.log) (hvidx : AntSim.LogIdx v.r.full)
    (hag : RecsAgree base0 v.r.full base0 r.p.log) :
    AntSim.ReadyOutP R j v r (readyDOf r (roleAfter rs.role ss) es ce ms qs sts) ∧
      r.full = r.p.log ∧ v.r.full = v.r.p.log := by
  obtain ⟨hsn, -, -⟩ := AntSim.InMask.b2 hmsk hin
  have hfp := AntSim.reach_fpD hmsk hin hbt hok hri
  have hfp0 := ((nodeOkD_facts hok).2.1 hsn).2.1
  have hfull : r.full = r.p.log := by simp [RState.full, hfp, hfp0]
  have hvfull : v.r.full = v.r.p.log := by simp [RState.full, hfp0]
  have hidx := logIdx_of_wf hwf
  have hds := AntSim.dst_reachD hmsk hin hbt hnet hok hri
  refine ⟨readyOutP_of hrv (reach_ce hri.reach) (hfp.trans hfp0) (hdl.trans hvfull) hip hout hfirst hqs
    hpk has hx hsts (fun _ => hns) (by rw [hfull]; exact hidx) ?_ ?_, hfull, hvfull⟩
  · intro k e f he hf ht
    rw [hdl] at he
    rw [hfull] at hf
    have htk := logMatch_of_recs hvidx hidx hag k e f he hf ht
    have h1 : (v.r.full.take (k + 1))[k]? = some e := by
      rw [List.getElem?_take]; simp [he]
    have h2 : (r.p.log.take (k + 1))[k]? = some f := by
      rw [List.getElem?_take]; simp [hf]
    rw [htk, h2] at h1
    exact (Option.some.inj h1).symm
  · intro q hq
    have hq' := (hout.2.2.2.2.1.mem_iff).mp hq
    rw [List.mem_filter] at hq'
    exact hds q hq'.1 (of_decide_eq_true hq'.2)

end pure

end AntHarness
end EtcdGrove
end Perennial
