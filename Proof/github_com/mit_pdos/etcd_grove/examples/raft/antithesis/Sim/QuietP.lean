/-
Lean-first (no Rocq counterpart).

# Parity B2: a `-parallel` leader's `Ready` the harness does not report (`antSim_quietP_in`)

A `-parallel` run is sync and unbatched; a leader's `Ready` that writes nothing and keeps the role is
`QuietIn.silentReady`'s step, its pending messages reordered (requests first, as `parallel` sends
them). With no queued write (`mems = []`) and no split write in progress (`parts = []`), the node's
disk is raft's state (`DiskFold`), so B1's `nodeOk_quiet` applies to the run with the driver modes
off (`RunCfg.syncOff`: the node's facts do not read `parallel` or `split` but through `SyncDisk`), and
its result is the B2 node part again (#33 parity B2, round 4).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Quiet
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.B1Carry

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open GMap go_etcd_io.raft.v3 AntCheck

section quietP
variable [GooseExts]

/-- The run with the driver modes off (sync and unbatched runs only differ from it in `SyncDisk`). -/
def RunCfg.syncOff (R : RunCfg) : RunCfg :=
  { R with drv := { R.drv with batch := false, parallel := false, split := 0, restarts := false } }

/-- The mask with the driver modes off. -/
def SimMask.b1Of (msk : SimMask) : SimMask :=
  { msk with batch := false, parallel := false, split := false, restarts := false }

theorem SimMask.b1Of_le {msk : SimMask} (h : msk ≤ mskB2) : msk.b1Of ≤ mskB1 := by
  obtain ⟨a, b, c, d, -, -, -, -⟩ := h
  exact ⟨a, b, c, d, by simp [BLe, SimMask.b1Of], by simp [BLe, SimMask.b1Of],
    by simp [BLe, SimMask.b1Of], by simp [BLe, SimMask.b1Of]⟩

theorem InMask.syncOff {msk : SimMask} {R : RunCfg} {net : List Msg} {xnet : List XMsg}
    (h : InMask msk R net xnet) : InMask msk.b1Of R.syncOff net xnet := by
  obtain ⟨a, b, -, -, -, -, e, f⟩ := h
  exact ⟨a, b, by simp [BLe, RunCfg.syncOff], by simp [BLe, RunCfg.syncOff],
    fun h => absurd rfl h, by simp [BLe, RunCfg.syncOff], e, f⟩

theorem ReachIn.syncOff {msk : SimMask} {R : RunCfg} {dec : CCDec} {Adm : List EntryM → CCState → Prop}
    {net : List Msg} {xnet : List XMsg} {n : Fin R.N} {v : NodeView} {r₁ : RState}
    (h : ReachIn msk R dec Adm net xnet n v r₁) :
    ReachIn msk.b1Of R.syncOff dec Adm net xnet n v r₁ := by
  cases h with
  | stay h1 h2 => exact .stay _ h1 h2
  | input inp _ h0 h1 h2 h3 h4 h5 h6 h7 =>
    refine .input _ inp _ ?_ h1 h2 h3 h4 h5 h6 h7
    cases inp <;> exact h0
  | advance _ h1 h2 h3 h4 h5 h6 h7 => exact .advance _ _ h1 h2 h3 h4 h5 h6 h7

/-- A sync, unbatched node part whose disk is raft's state, no write queued, an announced write not
made, is the node part of the run with the driver modes off. -/
theorem nodeOkD_syncOff {R : RunCfg} {dec : CCDec} {S : State} {net : List Msg} {n : Fin R.N}
    {v : NodeView} (ha : R.md.async = false) (hb : R.drv.batch = false) (hm : v.mems = [])
    (hd : v.dur = durOf v.r) (hu : v.undo ≠ none → v.made = false)
    (h : NodeOkD R dec S net n v) : NodeOk R.syncOff dec S net n v := by
  obtain ⟨d1, d2, -, d4, d5, d6, d7, hf, hl, hc, hp, -, hx, hqs, ht, hca, hxc, hlo, hvs, -⟩ := h
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hf
  refine ⟨d1, d2, fun _ _ _ _ => ⟨hm, hd, hu⟩, d4, d5, d6, d7, ⟨f1 hb, f2, f3, f4, f5, f6 ha, f7⟩,
    fun hrl => ?_, fun hrc => ?_, hp hb, hx, hqs, ht, hca, hxc, hlo, hvs⟩
  · obtain ⟨l1, l2, l3, l4, l5⟩ := hl hrl
    refine ⟨l1, l2, l3, l4, ?_⟩
    have hlog : v.dur.log = v.r.full := by rw [hd]; rfl
    obtain ⟨c1, c2⟩ := l5 (.inl hlog)
    exact ⟨c1, by rw [← hlog]; exact c2⟩
  · obtain ⟨c1, c2⟩ := hc hrc
    exact ⟨c1, c2 (by rw [hd]; rfl)⟩

/-- Back: the node part of the run with the driver modes off is the B2 node part of a `-parallel`
run, given the B2 bookkeeping of the view before (`w`: the same disk, undo record, queues). -/
theorem nodeOk_syncOffD {R : RunCfg} {dec : CCDec} {S : State} {net : List Msg} {n : Fin R.N}
    {v w : NodeView} (ha : R.md.async = false) (hb : R.drv.batch = false)
    (hpar : R.drv.parallel = true) (hm : v.mems = []) (hdu : v.dur = w.dur) (hun : v.undo = w.undo)
    (hj : v.jobs = []) (haj : v.ajobs = []) (huf : UndoFacts R w)
    (h : NodeOk R.syncOff dec S net n v) : NodeOkD R dec S net n v := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, hf, hl, hc, hp, hx, hqs, ht, hca, hxc, hlo, hvs⟩ := h
  have hd : v.dur = durOf v.r := (d3 ha rfl rfl rfl).2.1
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hf
  refine ⟨d1, d2, fun _ _ _ hp0 => (by rw [hpar] at hp0; cases hp0), d4, d5, d6, d7,
    ⟨fun _ => f1, f2, f3, f4, f5, fun _ => f6, f7⟩, fun hrl => ?_, fun hrc => ?_, fun _ => hp,
    fun hb' => (by rw [hb] at hb'; cases hb'), hx, hqs, ht, hca, hxc, hlo, hvs, ?_, ?_, ?_, ?_⟩
  · obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hl hrl
    refine ⟨l1, l2, l3, l4, fun _ => ⟨l5, ?_⟩⟩
    have hlog : v.dur.log = v.r.full := by rw [hd]; rfl
    rw [hlog]; exact l6
  · obtain ⟨c1, c2⟩ := hc hrc
    exact ⟨c1, fun _ => c2⟩
  · intro d hd'
    rw [hun] at hd'
    obtain ⟨u1, u2, u3⟩ := huf d hd'
    exact ⟨u1, u2, by rw [hdu]; exact u3⟩
  · intro _; rw [hm]; exact hd
  · refine ⟨fun _ => ⟨hj, haj⟩, (by rw [hj]; simp), (by rw [haj]; simp), fun ha' => (by rw [ha] at ha'; cases ha'),
      fun j hj' => (by rw [hj] at hj'; cases hj'), fun ha' => (by rw [ha] at ha'; cases ha')⟩
  · intro ha'; rw [ha] at ha'; cases ha'

/-- The node part keeps under a reordering of the pending messages. -/
theorem nodeOkD_pendPerm {R : RunCfg} {dec : CCDec} {S : State} {net : List Msg} {n : Fin R.N}
    {v : NodeView} (p : List Msg) (hp : ∀ q, q ∈ p ↔ q ∈ v.pend) (h : NodeOkD R dec S net n v) :
    NodeOkD R dec S net n { v with pend := p } := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, hf, hl, hc, hpo, hpb, hx, hqs, ht, hca, hxc, hlo, hvs, huf, hdf,
    hjo, hac⟩ := h
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := hf
  obtain ⟨j1, j2, j3, j4, j5, j6⟩ := hjo
  exact ⟨d1, d2, d3, d4, d5, d6, d7, ⟨f1, f2, f3, f4, f5, f6, fun q hq => f7 q ((hp q).mp hq), f8⟩, hl, hc,
    fun hb q hq => hpo hb q ((hp q).mp hq), fun hb q hq => hpb hb q ((hp q).mp hq), hx, hqs, ht, hca,
    hxc, hlo, hvs, huf, hdf, ⟨j1, j2, j3, j4, j5, fun ha q hq => j6 ha q ((hp q).mp hq)⟩, hac⟩

/-- **A `-parallel` leader's `Ready` the harness does not report** (no write, the same role;
`QuietIn.silentReady`'s step over `AntSimD`): the drain phase, its requests (appends and heartbeats)
pending first, in their order, then the others in theirs. The node has no queued write and no split
write in progress, and an announced write of it is not made (what the harness knows at a leader's
`Ready`: its last `-parallel` write was made and `wrote`). -/
theorem antSim_quietP_in (msk : SimMask) (hmsk : msk ≤ mskB2) :
    ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView)
      (net : List Msg) (xnet : List XMsg) (G : RaftFacts) (n : Fin R.N) (r₁ : RState)
      (rd : ReadyD) (Adm : List EntryM → CCState → Prop),
      InMask msk R net xnet → AntSimD R dec S V net xnet → RaftLaws G →
      GlobalOk R S net G →
      R.md.async = false → R.drv.batch = false → R.drv.parallel = true →
      (V n).mems = [] → (V n).parts = [] → ((V n).undo ≠ none → (V n).made = false) →
      ReachIn msk R dec Adm net xnet n (V n) r₁ → ReadyOutP R n (V n) r₁ rd →
      rd.role = .leader → rd.snap = none → ¬ Reported (V n) rd →
      ReadyFacts G (nodeId n) r₁ →
      AntSimD R dec S
        (setV V n { ((V n).drainOf r₁ rd) with
          pend := rd.msgs.filter isReqM ++ rd.msgs.filter (fun q => !isReqM q) })
        net xnet := by
  intro R dec S V net xnet G n r₁ rd Adm hin hs _ _ ha hb hpar hm hparts hu hr hrop _ _ hrep _
  obtain ⟨hsh, hbd, hn, hxn, hno⟩ := hs
  have hv := hno n
  have hd : (V n).dur = durOf (V n).r := by
    have := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hparts
    rw [hm] at this; exact this
  have hjo := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have huf := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv' := nodeOkD_syncOff ha hb hm hd hu hv
  have hq : QuietIn msk.b1Of R.syncOff dec Adm net xnet n (V n) ((V n).drainOf r₁ rd) :=
    .silentReady _ r₁ rd hr.syncOff hrop hrep
  have h1 := nodeOk_quiet (SimMask.b1Of_le hmsk) hin.syncOff hsh.1 (netOkD_toB1 ha hn) hv' hq
  have h2 : NodeOkD R dec S net n ((V n).drainOf r₁ rd) :=
    nodeOk_syncOffD ha hb hpar hm rfl rfl ((hjo.1 ha).1) ((hjo.1 ha).2) huf h1
  have h3 := nodeOkD_pendPerm (rd.msgs.filter isReqM ++ rd.msgs.filter (fun q => !isReqM q))
    (fun q => by
      show q ∈ _ ↔ q ∈ rd.msgs
      simp only [List.mem_append, List.mem_filter]
      cases isReqM q <;> simp) h2
  refine ⟨hsh, hbd, hn, hxn, fun j => ?_⟩
  unfold setV
  by_cases hj : j = n
  · subst hj; simp only [↓reduceIte]; exact h3
  · simp only [hj, ↓reduceIte]; exact hno j

end quietP

end AntSim
end EtcdGrove
end Perennial
