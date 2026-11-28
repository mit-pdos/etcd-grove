/-
Lean-first (no Rocq counterpart).

# Parity B2: the kind-independent parts of a `-parallel` leader's view after its `mem`

The view after `antSim_memP_in`'s `mem` is the `Ready`'s drain phase with its write queued and the
disk unchanged (`memView`). It differs from B1's view after a reported `Ready` (`afterReady`, whose
`AfterOk` `afterOk_loc` gives) only in the disk, the undo record and the queued writes, which raft's
facts, the configuration lag, the pending and transfer messages' facts and the leader hint do not
read; the disk with the queued write made is the `afterReady`'s (`write_memRec`). `memView_of`: those
parts of `memNode_of`'s premises, from `AfterOk`, the old view's facts and three kind-dependent facts
(the handed-out entries a prefix of the old disk, the term grown, `CandLt`) (#33 parity B2, Sim
round 14).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Ready
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.QuietP
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.ReachD

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open GMap go_etcd_io.raft.v3

section memView
variable [GooseExts]

/-- The view after a `-parallel` leader's `mem`: the drain phase, its pending messages `P`, its write
queued. -/
abbrev memView (v : NodeView) (r₁ : RState) (rd : ReadyD) (P : List Msg) : NodeView :=
  { (v.drainOf r₁ rd) with pend := P, mems := [rd.memRec v] }

/-- **The disk with a `Ready`'s write made is raft's state after it** (`ReadyOutP`: the hard state,
and the entries from their first index; none, the disk's log). -/
theorem write_memRec {R : RunCfg} {n : Fin R.N} {v : NodeView} {r₁ : RState} {rd : ReadyD}
    (hro : ReadyOutP R n v r₁ rd) (hsn : rd.snap = none) :
    v.dur.write (rd.memRec v) = durOf (accepted r₁) := by
  obtain ⟨-, -, ht, hvo, hc, hne, hhd, -⟩ := hro
  have hlog : (match rd.ents.head? with
      | none => v.dur.log
      | some e0 => v.dur.log.take (uint.nat e0.Index' - 1) ++ rd.ents) = r₁.full := by
    cases he : rd.ents with
    | nil => exact (hne hsn he).symm
    | cons e0 es =>
      rw [he] at hhd
      exact ((hhd e0 rfl).1).symm
  show DurW.mk rd.term rd.vote rd.commit _ = DurW.mk r₁.p.term r₁.p.vote r₁.p.commit r₁.full
  rw [ht, hvo, hc]
  exact congrArg _ hlog

/-- **The kind-independent parts of the view after a `-parallel` leader's `mem`** (`memNode_of`'s
`hNF`, `hCL`, `hpend`, `hxpend`, `hlead`, `hDF`), from `AfterOk` of the `afterReady` view, the old
view's facts, and: the handed-out entries a prefix of the (unchanged) disk, the term grown, `CandLt`
at raft's state. -/
theorem memView_of {R : RunCfg} {dec : CCDec} {V : Fin R.N → NodeView} {n : Fin R.N} {r₁ : RState}
    {rd : ReadyD} {P : List Msg}
    (ha : AfterOk R.syncOff dec V n ((V n).afterReady r₁ rd)) (hv : NodeFactsD R n (V n))
    (hpar0 : (V n).parts = []) (hro : ReadyOutP R n (V n) r₁ rd) (hsn : rd.snap = none)
    (hP : ∀ q, q ∈ P ↔ q ∈ rd.msgs)
    (hpfx : (V n).delivered ++ rd.ce <+: (V n).dur.log)
    (hterm : uint.Z (V n).ps.term ≤ uint.Z r₁.p.term) (hcl : CandLt r₁.p) (hlt : LogTermsLe r₁.p) :
    NodeFactsD R n (memView (V n) r₁ rd P) ∧ ConfLag dec R (memView (V n) r₁ rd P) ∧
      (∀ q ∈ P, PendOk R.N (nodeId n) (memView (V n) r₁ rd P) q) ∧
      (∀ x ∈ rd.xmsgs, XPendOk R.N (nodeId n) (accepted r₁).p x) ∧
      LeadOk n (memView (V n) r₁ rd P) ∧
      ((V n).parts = [] → (V n).dur.write (rd.memRec (V n)) = durOf (accepted r₁)) := by
  have hw := write_memRec hro hsn
  obtain ⟨f1, f2, f3, -, -, f6, f7, -, f9, f10, f11, f12, f13, f14, f15⟩ := ha.facts
  obtain ⟨-, -, v3, v4, -, -, -, v8, -⟩ := hv
  refine ⟨⟨fun _ => f1, f2, fun h => ⟨(f3 h).1, (f3 h).2.1, (v3 h).2.2⟩, v4, hpfx, fun _ => ?_,
    fun q hq => f7 q ((hP q).mp hq), Int.le_trans v8 hterm, f9, f10, f11, f12, f13, f14, f15, hcl, hlt⟩,
    ha.confLag, fun q hq => ha.hpend q ((hP q).mp hq), ha.hxpend, ha.hlead, fun _ => hw⟩
  show _ ≤ uint.nat (([rd.memRec (V n)] ++ (V n).parts).foldl DurW.write (V n).dur).commit
  rw [hpar0]
  show _ ≤ uint.nat ((V n).dur.write (rd.memRec (V n))).commit
  rw [hw]
  exact f6

/-- A `Ready` of a leader keeps the view's term and vote (`ReadyKind`'s leader kinds: a win, a
proposal, a commit). -/
theorem kind_leadKeep {cf : CfgM} {id : w64} {net : List Msg} {xnet : List XMsg} {v : NodeView}
    {ps₁ : PState} {rd : ReadyD} (hk : ReadyKind cf id net xnet v ps₁ rd)
    (hl : ps₁.role = .leader) : ps₁.term = v.ps.term ∧ ps₁.vote = v.ps.vote := by
  cases hk with
  | camp _ _ hr => cases hl.symm.trans hr
  | grant _ _ _ _ _ _ _ hr => cases hl.symm.trans hr
  | adopt _ _ _ _ _ hr => cases hl.symm.trans hr
  | follow hr => cases hl.symm.trans hr
  | store _ _ _ _ _ hr => cases hl.symm.trans hr
  | hb _ _ _ _ _ hr => cases hl.symm.trans hr
  | win _ _ _ _ _ _ _ hlc => exact ⟨hlc.2.1, hlc.2.2.1⟩
  | prop _ _ _ _ _ _ _ ht hv => exact ⟨ht, hv⟩
  | cmt _ _ ht hv => exact ⟨ht, hv⟩
  | adoptX _ _ _ _ _ _ _ _ hr => cases hl.symm.trans hr

/-- **A leader's `Ready` keeps the disk's term and vote**, B2, sync and unbatched, with no write
queued and no split write in progress: the disk is raft's state (`DiskFold`), and a `Ready` reported
as a leader's is at an unchanged state or of one of `ReadyKind`'s leader kinds, which keep the term
and vote (`kind_leadKeep`). -/
theorem leadHs_reachD {msk : SimMask} (hmsk : msk ≤ mskB2) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {S : AntCheck.State} {net : List Msg} {xnet : List XMsg}
    {n : Fin R.N} {v : NodeView} {r₁ : RState} {rd : ReadyD}
    (hin : InMask msk R net xnet) (_has : R.md.async = false) (hbt : R.drv.batch = false)
    (hnet : NetOkD R S net) (hok : NodeOkD R dec S net n v) (hm : v.mems = []) (hparts : v.parts = [])
    (hr : ReachIn msk R dec Adm net xnet n v r₁) (hro : ReadyOutP R n v r₁ rd)
    (hl : rd.role = .leader) :
    r₁.p.term = v.dur.term ∧ r₁.p.vote = v.dur.vote := by
  have hf := nodeOkD_factsS hok
  obtain ⟨hsn0, -, -⟩ := InMask.b2 hmsk hin
  have hs0 := hf.2.1 hsn0
  have hdf : DiskFold v := hok.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hd : v.dur = durOf v.r := by
    have := hdf hparts; rw [hm] at this; exact this
  have hdl : v.dur.log = v.ps.log := by
    rw [hd]; show v.r.fp ++ v.r.p.log = _; rw [hs0.2.1]; rfl
  rw [hd]
  show r₁.p.term = v.ps.term ∧ r₁.p.vote = v.ps.vote
  by_cases hch : Changed v r₁.p
  case neg =>
    exact ⟨Classical.byContradiction fun h => hch (.inl h),
      Classical.byContradiction fun h => hch (.inr (.inl h))⟩
  have hfu : r₁.full = r₁.p.log := by
    unfold RState.full; rw [reach_fpD hmsk hin hbt hok hr, hs0.2.1]; rfl
  have hro' := hro
  obtain ⟨hR, -, -, -, -, -, -, -, -, -, -, -, -, -, hsnapC, -, -⟩ := hro'
  have hsnr : rd.snap = none := (hsnapC hsn0).2.1
  have hqc : v.ps.role = .candidate → ∀ q ∈ v.qs, q.ty ≠ .preVoteResp → q.ty = .voteResp := by
    intro hc q hq hne
    rcases nodeOkD_qsS hok q hq with hq' | hw
    · rcases (hq'.notPre hne).2.2.2.2 with ⟨-, hl', -⟩ | ⟨h, -⟩
      · rw [hc] at hl'; cases hl'
      · exact h
    · cases hc.symm.trans hw.2.2.2.2.2.1
  have hkd := ready_kind (ReachIn.toPD hmsk hin hnet hok hr) hro hfu hdl hsnr hch hs0.1
    (nodeId_ne_zero n) hok.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (fun m hmn h4 => ⟨h4, hnet.2.2.1 m hmn⟩) (fun q hq hne => qsD_self (nodeOkD_qsS hok q hq) hne)
    hqc (hf.1 hbt)
  exact kind_leadKeep hkd (hR.symm.trans hl)

end memView

end AntSim
end EtcdGrove
end Perennial
