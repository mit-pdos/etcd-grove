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
  { N := R.N, K := R.K, boot := R.boot, k := R.k, md := R.md, hK := R.hK, hpv := R.hpv,
    drv := { R.drv with batch := false, parallel := false, split := 0, restarts := false } }

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

/-! ## The binding's facts without the other nodes' unmade acknowledgements

The B1 lemmas read a leader's acknowledgements as `AckIn`; `LeaderPartD` keeps the other nodes'
outside their unmade writes (`AckInX`). At the state with those acks removed (`stripU`), the B1
`AckIn` is `AckInX`. -/

open Classical in
/-- The binding's state without the acks of nodes other than `n` that their unmade writes added. -/
noncomputable def stripU {N : Nat} (n : Fin N) (S : State) : State :=
  { S with msgs := S.msgs.filter (fun a => !decide (∃ j : Fin N, j ≠ n ∧ a.type = go!"ack" ∧
      a.src = nameOf (nodeId j) ∧ ¬ AckOut S j a)) }

theorem stripU_sub {R : RunCfg} {n : Fin R.N} {S : State} {a : Fact} (h : a ∈ (stripU n S).msgs) :
    a ∈ S.msgs := (List.mem_filter.mp h).1

theorem stripU_keep {R : RunCfg} {n : Fin R.N} {S : State} {a : Fact} (h : a ∈ S.msgs)
    (hk : ∀ j : Fin R.N, j ≠ n → a.type = go!"ack" → a.src = nameOf (nodeId j) → AckOut S j a) :
    a ∈ (stripU n S).msgs := by
  refine List.mem_filter.mpr ⟨h, ?_⟩
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_exists, not_and,
    Classical.not_not]
  exact fun j hj ht hs => hk j hj ht hs

theorem stripU_nack {R : RunCfg} {n : Fin R.N} {S : State} {a : Fact} (h : a ∈ S.msgs)
    (ht : a.type ≠ go!"ack") : a ∈ (stripU n S).msgs :=
  stripU_keep h fun _ _ h' => absurd h' ht

theorem stripU_self {R : RunCfg} {n : Fin R.N} {S : State} {a : Fact} (h : a ∈ S.msgs)
    (hs : a.src = nameOf (nodeId n)) : a ∈ (stripU n S).msgs :=
  stripU_keep h fun j hj _ hs' => absurd (nodeId_inj (nameOf_inj (hs'.symm.trans hs))) hj

theorem stripU_ackX {R : RunCfg} {n j : Fin R.N} {S : State} {t k : Int}
    (h : AckIn (stripU n S) (nameOf (nodeId j)) (nameOf (nodeId n)) t k) : AckInX S n j t k := by
  obtain ⟨a, ha, h1, h2, h3, h4, h5⟩ := h
  refine ⟨a, stripU_sub ha, h1, h2, h3, h4, h5, fun hj => ?_⟩
  have := (List.mem_filter.mp ha).2
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_exists, not_and,
    Classical.not_not] at this
  exact this j hj h1 h2

theorem ackX_stripU {R : RunCfg} {n j : Fin R.N} {S : State} {t k : Int} (h : AckInX S n j t k) :
    AckIn (stripU n S) (nameOf (nodeId j)) (nameOf (nodeId n)) t k := by
  obtain ⟨a, ha, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨a, stripU_keep ha fun j' hj' _ hs => ?_, h1, h2, h3, h4, h5⟩
  have e : j' = j := nodeId_inj (nameOf_inj (hs.symm.trans h2))
  subst e; exact h6 hj'

theorem ackD_stripU {R : RunCfg} {n i : Fin R.N} {S : State} {dst : Str} {t k : Int} (h : AckInD S i dst t k) :
    AckInD (stripU n S) i dst t k := by
  obtain ⟨a, ha, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨a, stripU_keep ha fun j' _ _ hs => ?_, h1, h2, h3, h4, h5, h6⟩
  have e : j' = i := nodeId_inj (nameOf_inj (hs.symm.trans h2))
  subst e; exact h6

theorem stripU_granted {R : RunCfg} {n : Fin R.N} {S : State} (i : Nat) :
    (stripU n S).granted i = S.granted i := by
  refine granted_congr i rfl rfl (fun x => ?_) rfl
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem]
  exact ⟨stripU_sub, fun h => stripU_nack h (by dsimp only; decide)⟩

theorem ackX_stripX {R : RunCfg} {n j : Fin R.N} {S : State} {t k : Int} (h : AckInX S n j t k) :
    AckInX (stripU n S) n j t k := by
  obtain ⟨a, ha, h1, h2, h3, h4, h5, h6⟩ := h
  obtain ⟨b, hb, -⟩ := ackX_stripU ⟨a, ha, h1, h2, h3, h4, h5, h6⟩
  refine ⟨a, ?_, h1, h2, h3, h4, h5, h6⟩
  refine stripU_keep ha fun j' hj' _ hs => ?_
  have e : j' = j := nodeId_inj (nameOf_inj (hs.symm.trans h2))
  subst e; exact h6 hj'

/-- `NetOkD` holds at the stripped state. -/
theorem netOkD_stripU {R : RunCfg} {S : State} {net : List Msg} (n : Fin R.N) (h : NetOkD R S net) :
    NetOkD R (stripU n S) net := by
  obtain ⟨h1, hrest⟩ := h
  refine ⟨fun m hm => ?_, hrest⟩
  obtain ⟨hty, hsrc, j, hdst, hj⟩ := h1 m hm
  refine ⟨hty, hsrc, j, hdst, fun hle => ?_⟩
  obtain ⟨r1, r2, r3, r4⟩ := hj hle
  refine ⟨r1, fun ht => ?_, fun ht => stripU_nack (r3 ht) (by dsimp only; decide), fun ht i hi => ackD_stripU (r4 ht i hi)⟩
  obtain ⟨f, hf, hfm⟩ := r2 ht
  rw [voteFact_msgOf] at hf; cases hf
  exact ⟨_, voteFact_msgOf m m.dst, stripU_nack hfm (by dsimp only; decide)⟩

/-- A node part, unbatched, at the stripped state of its own index. -/
theorem nodeOkD_stripU {R : RunCfg} {dec : CCDec} {S : State} {net : List Msg} {n : Fin R.N} {v : NodeView}
    (hb : R.drv.batch = false) (h : NodeOkD R dec S net n v) : NodeOkD R dec (stripU n S) net n v := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, hf, hl, hc, hp, -, hx, hqs, rest⟩ := h
  refine ⟨d1, d2, d3, d4, d5, d6, d7, hf, fun hrl => ?_, fun hrc => ?_, hp,
    fun hb' => (by rw [hb] at hb'; cases hb'), hx, fun q hq => ?_, rest⟩
  · obtain ⟨l1, l2, l3, l4, l5⟩ := hl hrl
    exact ⟨l1, l2, fun j k hk ht => ackX_stripX (l3 j k hk ht), fun j hj => (l4 j hj).imp_right ackX_stripX, l5⟩
  · obtain ⟨c1, c2⟩ := hc hrc
    exact ⟨fun j hj => by rw [stripU_granted]; exact c1 j hj, fun hd => stripU_nack (c2 hd) (by dsimp only [State.voteRequest]; decide)⟩
  · refine (hqs q hq).elim (fun hQ' => Or.inl ?_) Or.inr
    obtain ⟨q1, q2, q3, q4⟩ := hQ'
    refine ⟨q1, q2, q3, ?_⟩
    rcases q4 with ⟨e, ⟨a1, a2, a, ha, h1, h2, h3, h4, h5⟩ | hv⟩ | hpv
    · exact .inl ⟨e, .inl ⟨a1, a2, a, stripU_self ha h2, h1, h2, h3, h4, h5⟩⟩
    · exact .inl ⟨e, .inr hv⟩
    · exact .inr hpv

/-- And back. -/
theorem nodeOkD_unstripU {R : RunCfg} {dec : CCDec} {S : State} {net : List Msg} {n : Fin R.N}
    {v : NodeView} (hb : R.drv.batch = false) (h : NodeOkD R dec (stripU n S) net n v) :
    NodeOkD R dec S net n v := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, hf, hl, hc, hp, -, hx, hqs, rest⟩ := h
  refine ⟨d1, d2, d3, d4, d5, d6, d7, hf, fun hrl => ?_, fun hrc => ?_, hp,
    fun hb' => (by rw [hb] at hb'; cases hb'), hx, fun q hq => ?_, rest⟩
  · obtain ⟨l1, l2, l3, l4, l5⟩ := hl hrl
    have tr : ∀ {j : Fin R.N} {t k : Int}, AckInX (stripU n S) n j t k → AckInX S n j t k :=
      fun ⟨a, ha, h1, h2, h3, h4, h5, h6⟩ => ⟨a, stripU_sub ha, h1, h2, h3, h4, h5, h6⟩
    exact ⟨l1, l2, fun j k hk ht => tr (l3 j k hk ht), fun j hj => (l4 j hj).imp_right tr, l5⟩
  · obtain ⟨c1, c2⟩ := hc hrc
    exact ⟨fun j hj => by rw [← stripU_granted (n := n)]; exact c1 j hj, fun hd => stripU_sub (c2 hd)⟩
  · refine (hqs q hq).elim (fun hQ' => Or.inl ?_) Or.inr
    obtain ⟨q1, q2, q3, q4⟩ := hQ'
    refine ⟨q1, q2, q3, ?_⟩
    rcases q4 with ⟨e, ⟨a1, a2, a, ha, h1, h2, h3, h4, h5⟩ | hv⟩ | hpv
    · exact .inl ⟨e, .inl ⟨a1, a2, a, stripU_sub ha, h1, h2, h3, h4, h5⟩⟩
    · exact .inl ⟨e, .inr hv⟩
    · exact .inr hpv

/-- A sync, unbatched node part whose disk is raft's state, no write queued, an announced write not
made, is the node part of the run with the driver modes off. -/
theorem nodeOkD_syncOff {R : RunCfg} {dec : CCDec} {S : State} {net : List Msg} {n : Fin R.N}
    {v : NodeView} (ha : R.md.async = false) (hb : R.drv.batch = false) (hm : v.mems = [])
    (hp0 : v.parts = []) (hd : v.dur = durOf v.r) (hu : v.undo ≠ none → v.made = false)
    (h : NodeOkD R dec S net n v) : NodeOk R.syncOff dec S net n v := by
  obtain ⟨d1, d2, -, d4, d5, d6, d7, hf, hl, hc, hp, -, hx, hqs, ht, hca, hxc, hlo, hvs, -⟩ := h
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, -⟩ := hf
  have f6' := f6 ha
  rw [hm, hp0] at f6'
  refine ⟨d1, d2, fun _ _ _ _ => ⟨hm, hd, hu⟩, d4, d5, d6, d7,
    ⟨f1 hb, f2, f3, f4, f5, f6', f7, f8, f9, f10, f11, f12, f13, f14, f15⟩,
    fun hrl => ?_, fun hrc => ?_, hp hb, hx, fun q hq => (hqs q hq).resolve_right fun hw => hw.2.2.2.2.2.2.1 hm,
    ht, hca, hxc, hlo, hvs⟩
  · obtain ⟨l1, l2, l3, l4, l5⟩ := hl hrl
    obtain ⟨l3, l4⟩ := leaderPartD_acks l3 l4
    refine ⟨l1, l2, l3, l4, ?_⟩
    have hlog : v.dur.log = v.r.full := by rw [hd]; rfl
    obtain ⟨c1, c2⟩ := l5 (.inl hlog)
    exact ⟨c1, by rw [← hlog]; exact c2⟩
  · obtain ⟨c1, c2⟩ := hc hrc
    exact ⟨c1, c2 (by rw [hd]; rfl)⟩

/-- **The in-memory commit is recorded** when it is the disk's (sync, between writes): C3's commit
facts for the node (`BindingOk`). -/
theorem memCommitOk_of_disk {R : RunCfg} {dec : CCDec} {S : State} {n : Fin R.N} {v : NodeView}
    (hb : BindingOkM R dec S) (hd : DiskIs S n v) (hdur : v.dur = durOf v.r) : MemCommitOk S v := by
  intro _
  obtain ⟨d1, -, d3, d4⟩ := hd
  have ec : v.dur.commit = v.ps.commit := by rw [hdur]; rfl
  have et : v.dur.term = v.ps.term := by rw [hdur]; rfl
  have el : v.dur.log = v.r.full := by rw [hdur]; rfl
  rw [ec] at d4; rw [et] at d1; rw [el] at d3
  obtain ⟨c1, c2⟩ := hb.2.2.1 n
  rw [d4, d3] at c2; rw [d4] at c1
  have hnat : (uint.Z v.ps.commit).toNat = uint.nat v.ps.commit := by word
  rw [hnat] at c2
  refine ⟨c1, c2, ?_⟩
  rcases hb.2.2.2.1 n with h | ⟨p, hp, hp1, hp2⟩
  · rw [d4] at h; exact .inl (by word)
  · rw [d4] at hp2; rw [d1] at hp1; exact .inr ⟨p, hp, hp1, hp2⟩

/-- Back: the node part of the run with the driver modes off is the B2 node part of a `-parallel`
run, given the B2 bookkeeping of the view before (`w`: the same disk, undo record, queues). -/
theorem nodeOk_syncOffD {R : RunCfg} {dec : CCDec} {S0 : State} {net : List Msg} {n : Fin R.N}
    {v w : NodeView} (ha : R.md.async = false) (hb : R.drv.batch = false)
    (hpar : R.drv.parallel = true) (hm : v.mems = []) (hdu : v.dur = w.dur) (hun : v.undo = w.undo)
    (hp0 : v.parts = []) (hj : v.jobs = []) (haj : v.ajobs = []) (huf : UndoFacts R w) (hbo : BindingOkM R dec S0)
    (hcl : CandLt v.ps)
    (h : NodeOk R.syncOff dec (stripU n S0) net n v) : NodeOkD R dec (stripU n S0) net n v := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, hf, hl, hc, hp, hx, hqs, ht, hca, hxc, hlo, hvs⟩ := h
  have hd : v.dur = durOf v.r := (d3 ha rfl rfl rfl).2.1
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15⟩ := hf
  refine ⟨d1, d2, fun _ _ _ hp0 => (by rw [hpar] at hp0; cases hp0), d4, d5, d6, d7,
    ⟨fun _ => f1, f2, f3, f4, f5, fun _ => by rw [hm, hp0]; exact f6, f7, f8, f9, f10, f11, f12, f13, f14,
      f15, hcl⟩, fun hrl => ?_, fun hrc => ?_, fun _ => hp,
    fun hb' => (by rw [hb] at hb'; cases hb'), hx, fun q hq => .inl (hqs q hq), ht, hca, hxc, hlo, hvs, ?_, ?_, ?_, ?_,
    fun _ _ => (d3 ha rfl rfl rfl).2.2, (memCommitOk_of_disk (S := S0) hbo d1 hd :)⟩
  · obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hl hrl
    refine ⟨l1, l2, fun j k hk ht => ackX_stripX (stripU_ackX (l3 j k hk ht)),
      fun j hj => (l4 j hj).imp_right fun h => ackX_stripX (stripU_ackX h), fun _ => ⟨l5, ?_⟩⟩
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
    hjo, hac, hum, hmc⟩ := h
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := hf
  obtain ⟨j1, j2, j3, j4, j5, j6⟩ := hjo
  exact ⟨d1, d2, d3, d4, d5, d6, d7, ⟨f1, f2, f3, f4, f5, f6, fun q hq => f7 q ((hp q).mp hq), f8⟩, hl, hc,
    fun hb q hq => hpo hb q ((hp q).mp hq), fun hb hm q hq => hpb hb hm q ((hp q).mp hq), hx, hqs, ht,
    hca, hxc, hlo, hvs, huf, hdf, ⟨j1, j2, j3, j4, j5, fun ha q hq => j6 ha q ((hp q).mp hq)⟩, hac, hum,
    hmc⟩

/-- **A `-parallel` leader's `Ready` the harness does not report** (no write, the same role;
`QuietIn.silentReady`'s step over `AntSimD`): the drain phase, its requests (appends and heartbeats)
pending first, in their order, then the others in theirs. The node has no queued write and no split
write in progress (what the harness knows at a leader's `Ready`: its last `-parallel` write was made
and `wrote`). Other nodes may have announced commits not yet written: the B1 lemma reads them at
`liftC`. -/
theorem antSim_quietP_in (msk : SimMask) (hmsk : msk ≤ mskB2) :
    ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView)
      (net : List Msg) (xnet : List XMsg) (G : RaftFacts) (n : Fin R.N) (r₁ : RState)
      (rd : ReadyD) (Adm : List EntryM → CCState → Prop),
      InMask msk R net xnet → AntSimD R dec S V net xnet → RaftLaws G →
      GlobalOk R S net G →
      R.md.async = false → R.drv.batch = false → R.drv.parallel = true →
      (V n).mems = [] → (V n).parts = [] →
      ReachIn msk R dec Adm net xnet n (V n) r₁ → ReadyOutP R n (V n) r₁ rd →
      rd.role = .leader → rd.snap = none → ¬ Reported (V n) rd →
      ReadyFacts G (nodeId n) r₁ →
      AntSimD R dec S
        (setV V n { ((V n).drainOf r₁ rd) with
          pend := rd.msgs.filter isReqM ++ rd.msgs.filter (fun q => !isReqM q) })
        net xnet := by
  intro R dec S V net xnet G n r₁ rd Adm hin hs _ _ ha hb hpar hm hparts hr hrop hrl _ hrep _
  obtain ⟨hsh, hbd, hn, hxn, hno⟩ := hs
  have hv := hno n
  have hu : (V n).undo ≠ none → (V n).made = false :=
    hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ha hb
  have hqn : S.queue[n.val]! = [] := by
    have hqi : QueueIs S n (V n) := hv.2.2.2.2.1
    unfold QueueIs at hqi; rw [hqi, hm]; rfl
  have hd : (V n).dur = durOf (V n).r := by
    have := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hparts
    rw [hm] at this; exact this
  have hjo := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have huf := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hqn' : (stripU n S).queue[n.val]! = [] := hqn
  have hv' := nodeOk_liftC (R := R.syncOff) hqn' (nodeOkD_syncOff ha hb hm hparts hd hu (nodeOkD_stripU hb hv))
  have hq : QuietIn msk.b1Of R.syncOff dec Adm net xnet n (V n) ((V n).drainOf r₁ rd) :=
    .silentReady _ r₁ rd hr.syncOff hrop hrep
  have h1 := nodeOk_unliftC (R := R.syncOff) hqn'
    (nodeOk_quiet (SimMask.b1Of_le hmsk) hin.syncOff hsh.1
      (netOkD_toB1L ha hsh.2.2.2.2.2.1 (netOkD_stripU n hn)) hv' hq)
  have h2 : NodeOkD R dec S net n ((V n).drainOf r₁ rd) := nodeOkD_unstripU hb
    (nodeOk_syncOffD ha hb hpar hm rfl rfl hparts ((hjo.1 ha).1) ((hjo.1 ha).2) huf hbd.1
      (fun hc => by
        have hc' : r₁.p.role = .candidate := hc
        rw [hrop.1, hc'] at hrl; cases hrl) h1)
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
