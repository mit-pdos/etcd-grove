/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: `antSim_ready` (#33 S4, the invariant phase; parity B1)

A reported `Ready` (`notes/antithesis-rawnode-design.md` §3.3, "`antSim_ready`, guard by guard";
`notes/antithesis-parity-design.md` §3.5), for the runs a mask below `mskS4` admits: `antSim_gc` to
`S1`; the protocol readings (`ReachP`, `ReadyOutO`, `ReportedO`) and the old disk facts of the node
collected in `RdCtx` (`rdCtx_of`); the kind-independent fields of the new view (`AfterOk`); the
`Ready`'s kind (`ready_kind`); per kind, `InMemory` and `OnDisk` of its `ready` report evaluated
(`ReadyEval`, `ReadyLeader`, `ReadyOD`, `ReadyOD2`) to `readyS`, its side conditions `ReadyOk`
(`ReadyRel.lean`), then `ready_rel` and `Prefix.snoc`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.ReadyRel
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.ReadyKind
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.ReadyLeader
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.ReadySafe
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Quiet
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.GC
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Send

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open AntCheck go_etcd_io.raft.v3

section ready
variable [GooseExts]
variable {cf : CfgM} {N : Nat} {kk : NodeK}

/-! ## From `Ready`'s result to the next prefix -/

/-- `Step` of a `ready` report whose `Ready` is `rdS (odS …) r`: `readyS`. -/
theorem ready_step {R : RunCfg} {S : State} {n : Fin R.N} (hc : S.cfg = R.cfg) {b rr : Str}
    {t v c : w64} {es : List EntryM} {t1 : Int} {vo : Option Str} {L1 : List Entry} {c1 : Int}
    {ro : List Str} {cf : Confirmed} {M : List Fact} {Vs : List VoteRec} {ld : List LeaderRec}
    {ll : TermFn (List Entry)} {p : Pre} {ch : List Entry} {tl : TermFn Int} {vi : SSet}
    {r : MemResult}
    (h : S.ready n.val (evReady (nodeId n) b rr t v c es) =
      .ok (some (rdS (odS S n.val t1 vo L1 c1 ro cf M Vs ld ll p ch tl vi) r))) :
    S.step (evReady (nodeId n) b rr t v c es) =
      .ok (some (readyS S n.val t1 vo L1 c1 ro cf M Vs ld ll p ch tl vi r)) := by
  rw [step_evReady n hc, h]; rfl

/-- **The last step of each kind**: `Ready` evaluated at `S1` (after `GC`) to `rdS (odS …) r`, its
side conditions met: the next prefix, the relation and `GlobalOk` at the new state. -/
theorem ready_finish {R : RunCfg} {dec : CCDec} {xnet : List XMsg} {S S1 : State}
    {V : Fin R.N → NodeView} {net : List Msg} {evs : List Event}
    {G : RaftFacts} {n : Fin R.N} {w : NodeView} {b rr : Str} {t v c : w64}
    {es : List EntryM} {t1 : Int} {vo : Option Str} {L1 : List Entry} {c1 : Int} {ro : List Str}
    {cf : Confirmed} {M : List Fact} {Vs : List VoteRec} {ld : List LeaderRec}
    {ll : TermFn (List Entry)} {p : Pre} {ch : List Entry} {tl : TermFn Int} {vi : SSet}
    {r : MemResult}
    (hp : Prefix R.cfg evs S) (hgc : gcLoop (gcFuel S) S = .ok (S1, none))
    (hs1 : AntSim R dec S1 V net xnet) (hgo1 : GlobalOk R S1 net G) (hl : RaftLaws G)
    (h : S1.ready n.val (evReady (nodeId n) b rr t v c es) =
      .ok (some (rdS (odS S1 n.val t1 vo L1 c1 ro cf M Vs ld ll p ch tl vi) r)))
    (hok : ReadyOk R dec S1 V net G n w t1 vo L1 c1 ro cf M Vs ld ll p ch tl vi r) :
    SimStep R dec evs G (evReady (nodeId n) b rr t v c es) (setV V n w) net xnet := by
  obtain ⟨h1, h2, h3⟩ := ready_rel hs1 hgo1 hl hok
  exact ⟨_, Prefix.snoc hp hgc (ready_step hs1.1.1 h) h3, h1, h2⟩

/-! ## The view after a `Ready` -/

/-- **The kind-independent fields of `ReadyOk`** for the view `w` after a `Ready` at node `n`: the
handed-out entries kept, the disk raft's state with no ghost prefix, the announced write the old
disk, not made, the queue, reads and configuration kept, `ConfLag`, raft's facts, the pending
messages' and transfer messages' facts, the drain's cause kept, the leader hint. -/
structure AfterOk (R : RunCfg) (dec : CCDec) (V : Fin R.N → NodeView) (n : Fin R.N) (w : NodeView) :
    Prop where
  hdel : w.delivered = (V n).delivered
  hfp : w.r.fp = []
  hdur : w.dur = durOf w.r
  hundo : w.undo = some (V n).dur
  hmade : w.made = false
  hmems : w.mems = (V n).mems
  hreads : w.reads = (V n).reads
  hcfg : w.conf = (V n).conf ∧ w.confAt = (V n).confAt
  confLag : ConfLag dec R w
  facts : NodeFacts R n w
  hpend : ∀ q ∈ w.pend, PendOk R.N (nodeId n) w q
  hxpend : ∀ x ∈ w.xpend, XPendOk R.N (nodeId n) x
  drain : w.told = (V n).told ∧ w.cause = (V n).cause ∧ w.xcause = (V n).xcause
  hlead : LeadOk n w

/-- **`AfterOk` of a `Ready`'s view** below `mskS4` (`nodeOk_quiet`'s `silentReady` for any `Ready`):
the configuration, ghost prefix and snapshot flag kept along `Reach` (`reach_keep`), the new full
log normal (`msgShape_core`), the `Ready`'s messages under the mask (`MShape` and no snapshot),
`PendOk` (`pendOk_of_reach`), no transfer message, the leader hint (`reach_leadOk`) and a leader's
empty read-only queue (`reach_roOk`); a reported pre-candidate a follower at a pre-vote node
(`ReadyOutP`). -/
theorem afterOk_of {msk : SimMask} (hmsk : msk ≤ mskS4) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {S : State} {V : Fin R.N → NodeView} {net : List Msg}
    {xnet : List XMsg} {n : Fin R.N} {r₁ : RState} {xs : List XMsg} {rd : ReadyD}
    (hin : InMask msk R net xnet) (hs : AntSim R dec S V net xnet)
    (hr : ReachIn msk R dec Adm net xnet n (V n) r₁ xs) (hro : ReadyOutP R n (V n) r₁ xs rd) :
    AfterOk R dec V n ((V n).afterReady r₁ rd) := by
  obtain ⟨hmd, -, -, -, -, -, -, -⟩ := hin.s4 hmsk
  have hnet := hs.2.2.1
  have hv := hs.2.2.2.2 n
  have hcc : R.md.confChanges = false := by rw [hmd]
  have hsn : R.md.snapshots = false := by rw [hmd]
  have hfn : EntsNormal (V n).r.full := (hv.facts.conf0 hcc).2.1
  have hsnap0 := hv.facts.snap0 hsn
  have hconf : (V n).conf = (V n).r.cfg ∧ (V n).confAt = lastConfIdx (V n).r.full (V n).r.cidx := by
    rcases hv.confLag with h | ⟨h, -⟩
    · exact h
    · rw [hsnap0.2.2] at h; cases h
  obtain ⟨⟨hcfg, hfp, hsnap⟩, hxs, -, -⟩ := reach_keep hmsk hin hv hr
  have hro' := hro
  obtain ⟨hR, hpre, -, -, -, -, -, -, hsync, -, hxm, hpfx, hlen, -, hsnapC, hidx, -⟩ := hro
  obtain ⟨hb0, -, hnosnap⟩ := hsnapC hsn
  have hmsg := (hsync (by rw [hmd])).2
  have hcm : ∀ m, (V n).cause = some m → m.ty = .app ∨ m.ty = .propose → EntsNormal m.entries :=
    fun m hm => (hnet.2.2.2.2 m (hv.cause m hm).1).1 hcc
  obtain ⟨hfl, hms⟩ := msgShape_core hmsk hin hnet hv hr hmsg hfn (hv.facts.roPend (by rw [hmd])) hcm
  have f3 := hv.facts.conf0
  have hroOk := reach_roOk hmsk hin hv hr
  refine {
    hdel := rfl
    hfp := hfp.trans hsnap0.2.1
    hdur := rfl
    hundo := rfl
    hmade := rfl
    hmems := rfl
    hreads := rfl
    hcfg := ⟨rfl, rfl⟩
    confLag := .inl ⟨by show (V n).conf = r₁.cfg; rw [hcfg]; exact hconf.1, by
      show (V n).confAt = lastConfIdx r₁.full r₁.cidx
      rw [hconf.2, lastConfIdx_normal hfn, lastConfIdx_normal hfl]⟩
    facts := ⟨rfl, fun _ => ⟨hb0, hfp.trans hsnap0.2.1, hsnap.trans hsnap0.2.2⟩,
      fun h => ⟨by show r₁.cfg.cfg = _; rw [hcfg]; exact (f3 h).1, hfl, hfl⟩, hidx, hpfx, hlen,
      fun q hq => ?_, Int.le_refl _,
      (fun h => by change rd.pre = true at h; show r₁.p.role = .follower; rw [← hR]; exact (hpre h).1),
      (fun _ => hroOk), (fun h => (hpre h).2)⟩
    hpend := by have h := pendOk_of_reach hmsk hin hnet hv hr hro'; exact h
    hxpend := fun x hx => by have hx' : x ∈ rd.xmsgs := hx; rw [hxm, hxs] at hx'; cases hx'
    drain := ⟨rfl, rfl, rfl⟩
    hlead := by have h := reach_leadOk hmsk hin hnet hv hr; exact h }
  obtain ⟨-, h2', h3', -, -⟩ := hms q hq
  have hqo : q ∈ r₁.p.outbox := (List.mem_filter.mp ((hmsg.mem_iff).mp hq)).1
  exact ⟨fun _ _ => h3', fun _ => hnosnap q hqo, h2'⟩

/-! ## The drain's `by` and the campaign -/

theorem reach_byE {id : w64} {net : List Msg} {v : NodeView} {ps₁ : PState} {rd : ReadyD}
    (hr : ReachP kk cf id net v ps₁) (hro : ReadyOutO N id v ps₁ rd) (hrep : ReportedO v rd) :
    DrainBy v.byE := by
  cases hr with
  | stay _ => exact absurd hrep (stay_quiet hro)
  | recv m _ _ hbe => exact .inr ⟨.recv m, hbe⟩
  | tick _ _ hbe => exact .inr ⟨.tick, hbe⟩
  | propose d _ _ hbe => exact .inr ⟨.propose d, hbe⟩
  | advance _ _ _ hb _ => exact hb

/-- A campaign's tally is empty (`pbecomeCandidate`) and the node a voter of its configuration: the
campaign is `TickEnd`'s (an `Advance` keeps the term, a leader's tick its role). -/
theorem camp_votes {id : w64} {net : List Msg} {v : NodeView} {ps₁ : PState}
    (hr : ReachP kk cf id net v ps₁) (hX : v.ps.outbox = []) (hqs : ∀ q ∈ v.qs, SelfMsg id v.ps.term q)
    (hbe : v.byE = go!"tick") (ht : ps₁.term = v.ps.term + W64 1) (hc : ps₁.role = .candidate) :
    ps₁.votes = ∅ ∧ id ∈ cf.voters := by
  cases hr with
  | stay _ => exact absurd ht.symm (w64_succ_ne _)
  | recv m _ _ hbe' => rw [hbe] at hbe'; exact absurd hbe' (by decide)
  | propose d _ _ hbe' => rw [hbe] at hbe'; exact absurd hbe' (by decide)
  | tick _ _ _ hs =>
    rcases hs with rfl | ⟨-, hvo, peers, cl, -, rfl⟩ | ⟨hl, ms, -, rfl⟩
    · exact absurd ht.symm (w64_succ_ne _)
    · exact ⟨rfl, hvo⟩
    · rw [psendMsgs_role, hl] at hc; cases hc
  | advance _ _ _ _ ha =>
    have hinv : AdvInv id v.ps.term v.ps.commit ps₁ :=
      adv_run ha hqs (advInv_nil rfl (Int.le_refl _) hX)
    rw [hinv.1] at ht
    exact absurd ht.symm (w64_succ_ne _)

/-- A voter of the run's initial configuration is in the binding's view of it. -/
theorem cin_has_voter {R : RunCfg} (n : Fin R.N) (h : nodeId n ∈ R.voters0) {cs : CCState}
    (hcs : cs.cfg = CfgM.simple R.voters0 ∅) :
    ((confView R.N cs).cin.has (nameOf (nodeId n)) || (confView R.N cs).cout.has (nameOf (nodeId n))) =
      true := by
  have hk : n.val < R.K := (mem_voters0 R n.isLt).mp h
  have e : (confView R.N cs).cin = idsView R.N R.voters0 := by
    unfold confView; rw [hcs]; rfl
  rw [e, idsView_voters0, R.initVoters_eq]
  have := server_has (⟨n.val, hk⟩ : Fin R.K)
  rw [Bool.or_eq_true]; exact .inl this

theorem roleOf_leader_iff (r : Role) : roleOf r = leader ↔ r = .leader := by
  cases r <;> decide

theorem roleOf_follower_iff (r : Role) : roleOf r = follower ↔ r = .follower := by
  cases r <;> decide

/-! ## The context of a reported `Ready` below `mskS4` -/

/-- **What a reported `Ready` at node `n` starts from** (below `mskS4`), after `GC` to `S1`: the
checker's prefix and steps, the relation and `GlobalOk` at `S1`; the node's old disk facts on its
protocol state (`v.ps`: the disk is raft's own state with no ghost prefix); its configuration the
initial one; no write queued, no pre-candidate reported before or now, no snapshot; the new state's
full log its protocol log, `ReadyFacts`; the protocol readings of `Reach`, `ReadyOutP`, `Reported`;
the messages sent `InMsg`, the queued self-messages, the new outbox's self-addressed messages; a
non-follower's vote its own before and after; the new view's kind-independent fields; the kind. -/
structure RdCtx (R : RunCfg) (dec : CCDec) (S : State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (evs : List Event) (G : RaftFacts) (n : Fin R.N) (r₁ : RState) (rd : ReadyD)
    (S1 : State) : Prop where
  hp : Prefix R.cfg evs S
  hgc : gcLoop (gcFuel S) S = .ok (S1, none)
  hs1 : AntSim R dec S1 V net xnet
  hgo1 : GlobalOk R S1 net G
  hl : RaftLaws G
  hdk : ∀ k : Fin R.N, (V k).dur = durOf (V k).r
  hc : S1.cfg = R.cfg
  hn3 : n.val < S1.role.length
  hct3 : n.val < S1.currentTerm.length
  hlg3 : n.val < S1.log.length
  d1 : S1.currentTerm[n.val]! = uint.Z (V n).ps.term
  d2 : S1.vote n.val = nameOf (V n).ps.vote
  d3 : S1.log[n.val]! = logOf (V n).ps.log
  d4 : S1.commitIndex[n.val]! = uint.Z (V n).ps.commit
  d5 : S1.role[n.val]! = roleOf (V n).ps.role
  d7 : (V n).ps.outbox = []
  d8 : (V n).ps.base = base0
  d9 : LogIdx (V n).ps.log
  hconf : S1.config[n.val]! = confView R.N (V n).r.cfg
  hcf : (V n).r.cfg.cfg = CfgM.simple R.voters0 ∅
  hcc : R.md.confChanges = false
  hq0 : S1.queue[n.val]! = []
  hvp : (V n).pre = false
  hpf : rd.pre = false
  hsn : rd.snap = none
  hfl : r₁.full = r₁.p.log
  hrf : ReadyFacts G (nodeId n) r₁
  hr : ReachP {} (CfgM.simple R.voters0 ∅) (nodeId n) net (V n) r₁.p
  hro : ReadyOutO R.N (nodeId n) (V n) r₁.p rd
  hrep : ReportedO (V n) rd
  htold : (V n).byE = go!"recv" → (V n).told = true
  htb : uint.Z (V n).ps.term + 1 < 2 ^ 64
  hin : ∀ m ∈ net, InMsg m
  hqs : ∀ q ∈ (V n).qs, SelfMsg (nodeId n) (V n).ps.term q
  hso : SelfOut (nodeId n) r₁.p
  hvs : (V n).ps.role ≠ .follower → (V n).ps.vote = nodeId n
  hvs1 : r₁.p.role ≠ .follower → r₁.p.vote = nodeId n
  ha : AfterOk R dec V n ((V n).afterReady r₁ rd)
  hk : ReadyKind (CfgM.simple R.voters0 ∅) (nodeId n) net (V n) r₁.p rd

/-- **`RdCtx` from `antSim_ready`'s premises** below `mskS4`. -/
theorem rdCtx_of {msk : SimMask} (hmsk : msk ≤ mskS4) {R : RunCfg} {dec : CCDec} {S : State}
    {V : Fin R.N → NodeView} {net : List Msg} {xnet : List XMsg} {evs : List Event} {G : RaftFacts}
    {n : Fin R.N} {r₁ : RState} {xs : List XMsg} {rd : ReadyD}
    (hin : InMask msk R net xnet) (hpre : SimPre R dec S V net xnet evs G)
    (hr : ReachIn msk R dec (admOf G) net xnet n (V n) r₁ xs) (hro : ReadyOutP R n (V n) r₁ xs rd)
    (hrep : Reported (V n) rd) (htold : Told (V n)) (hrf : ReadyFacts G (nodeId n) r₁)
    (htb : TermRoom (V n)) :
    ∃ S1, RdCtx R dec S V net xnet evs G n r₁ rd S1 := by
  obtain ⟨hp, hs, hl, hgo⟩ := hpre
  obtain ⟨hmd, hk, hbt, hpar, hspl, _, _, hty⟩ := hin.s4 hmsk
  have ha := afterOk_of hmsk hin hs hr hro
  have hfp : r₁.fp = [] := ha.hfp
  obtain ⟨S1, hgc, hs1, hgo1⟩ := antSim_gc R dec S V net xnet G hs hl hgo
  have hv := hs1.2.2.2.2 n
  have hnet := hs1.2.2.1
  have hsh := hs1.1
  have hsy := hv.sync (by rw [hmd]) hbt hspl hpar
  have hsn0 := hv.facts.snap0 (by rw [hmd])
  have hfp0 : (V n).r.fp = [] := hsn0.2.1
  have hdur : (V n).dur = durOf (V n).r := hsy.2.1
  have hdl : (V n).dur.log = (V n).ps.log := by
    rw [hdur]; show (V n).r.fp ++ (V n).r.p.log = _; rw [hfp0]; rfl
  have hfl : r₁.full = r₁.p.log := by unfold RState.full; rw [hfp]; rfl
  have hvp : (V n).pre = false := by
    cases h : (V n).pre
    · rfl
    · have := hv.facts.preVote h; rw [hk n] at this; cases this
  have hro' := hro
  obtain ⟨-, hpre', -, -, -, -, -, -, -, -, -, -, -, -, hsnapC, -, -⟩ := hro'
  have hpf : rd.pre = false := by
    cases h : rd.pre
    · rfl
    · have := (hpre' h).2; rw [hk n] at this; cases this
  have hsnr : rd.snap = none := (hsnapC (by rw [hmd])).2.1
  have hroO := readyOutO_of hro (by rw [hmd]) (by rw [hmd]) hdl hfp
  have hrepO := reportedO_of hrep hdur hsnr hpf hvp
  have hcf : (V n).r.cfg.cfg = CfgM.simple R.voters0 ∅ := (hv.facts.conf0 (by rw [hmd])).1
  have hrP := ReachIn.toP hmsk hr
  rw [hk n, hcf] at hrP
  obtain ⟨e1, e2, e3, e4⟩ := hv.disk
  obtain ⟨m1, -, m3, -⟩ := hv.mem
  have hcv : (V n).conf = (V n).r.cfg := by
    rcases hv.confLag with h | ⟨h, -⟩
    · exact h.1
    · rw [hsn0.2.2] at h; cases h
  have d7 : (V n).ps.outbox = [] := hv.facts.outbox
  have d8 : (V n).ps.base = base0 := hsn0.1
  have hin' : ∀ m ∈ net, InMsg m := fun m hm => ⟨ty7_of_s4 (hty m hm), hnet.2.2.1 m hm⟩
  have hqs : ∀ q ∈ (V n).qs, SelfMsg (nodeId n) (V n).ps.term q := fun q hq => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hv.qs q hq
    exact ⟨h1, h2, h3, h4, h5.imp (fun h => h.1) (fun h => h.1)⟩
  have hkd := ready_kind hrP hroO hrepO d8 (nodeId_ne_zero n) hv.voteSelf hin' hqs d7
  refine ⟨S1, {
    hp := hp, hgc := hgc, hs1 := hs1, hgo1 := hgo1, hl := hl, hc := hsh.1
    hdk := fun k => ((hs1.2.2.2.2 k).sync (by rw [hmd]) hbt hspl hpar).2.1
    hn3 := by rw [hsh.2.2.2.2.2.2.1]; exact n.isLt
    hct3 := by rw [hsh.2.1]; exact n.isLt
    hlg3 := by rw [hsh.2.2.2.2.1]; exact n.isLt
    d1 := by rw [e1, hdur]; rfl
    d2 := by rw [e2, hdur]; rfl
    d3 := by rw [e3, hdl]
    d4 := by rw [e4, hdur]; rfl
    d5 := by rw [m1]; unfold roleS roleStr; rw [hvp]; rfl
    d7 := d7, d8 := d8
    d9 := hdl ▸ hv.facts.logIdx
    hconf := by rw [m3, hcv]
    hcf := hcf
    hcc := by rw [hmd]
    hq0 := by rw [hv.queue, hsy.1]; rfl
    hvp := hvp, hpf := hpf, hsn := hsnr, hfl := hfl, hrf := hrf, hr := hrP, hro := hroO
    hrep := hrepO, htold := htold, htb := htb, hin := hin', hqs := hqs
    hso := selfOut_reach hrP d7 hv.leadOk.1 hin' hqs
    hvs := hv.voteSelf
    hvs1 := voteSelf_kind hkd hv.voteSelf
    ha := ha, hk := hkd }⟩

/-- `ready_finish` from the context. -/
theorem RdCtx.finish {R : RunCfg} {dec : CCDec} {S : State} {V : Fin R.N → NodeView} {net : List Msg}
    {xnet : List XMsg} {evs : List Event} {G : RaftFacts} {n : Fin R.N} {r₁ : RState} {rd : ReadyD}
    {S1 : State} (hx : RdCtx R dec S V net xnet evs G n r₁ rd S1) {w : NodeView} {b rr : Str}
    {t v c : w64} {es : List EntryM} {t1 : Int} {vo : Option Str} {L1 : List Entry} {c1 : Int}
    {ro : List Str} {cf : Confirmed} {M : List Fact} {Vs : List VoteRec} {ld : List LeaderRec}
    {ll : TermFn (List Entry)} {p : Pre} {ch : List Entry} {tl : TermFn Int} {vi : SSet}
    {r : MemResult}
    (h : S1.ready n.val (evReady (nodeId n) b rr t v c es) =
      .ok (some (rdS (odS S1 n.val t1 vo L1 c1 ro cf M Vs ld ll p ch tl vi) r)))
    (hok : ReadyOk R dec S1 V net G n w t1 vo L1 c1 ro cf M Vs ld ll p ch tl vi r) :
    SimStep R dec evs G (evReady (nodeId n) b rr t v c es) (setV V n w) net xnet :=
  ready_finish hx.hp hx.hgc hx.hs1 hx.hgo1 hx.hl h hok

/-- What `antSim_ready` concludes, the `Ready`'s fields read off its state (`ReadyOutO`). -/
def ReadyGoal (R : RunCfg) (dec : CCDec) (V : Fin R.N → NodeView) (net : List Msg) (xnet : List XMsg)
    (evs : List Event) (G : RaftFacts) (n : Fin R.N) (r₁ : RState) (rd : ReadyD) : Prop :=
  SimStep R dec evs G (evReady (nodeId n) (V n).byE (roleOf r₁.p.role) r₁.p.term r₁.p.vote r₁.p.commit rd.ents)
    (setV V n ((V n).afterReady r₁ rd)) net xnet

/-! ## The terms' recorded commits (C3's `TermLenOk`, C4's `LeadCommitMsgOk`) -/

theorem tlOld_cons (q : Int × Int) (qs : TermFn Int) (t : Int) :
    tlOld (q :: qs) t = if q.1 = t then q.2 else tlOld qs t := by
  unfold tlOld; simp only [List.find?_cons]; by_cases h : q.1 = t
  · simp [h]
  · have hb : (q.1 == t) = false := beq_false_of_ne h
    simp [hb, h]

theorem tlOld_with (f : TermFn Int) (t v t' : Int) :
    tlOld (f.with t v) t' = if t' = t then v else tlOld f t' := by
  induction f with
  | nil =>
    simp only [TermFn.with, tlOld_cons]
    by_cases h : t' = t
    · rw [if_pos h.symm, if_pos h]
    · rw [if_neg (Ne.symm h), if_neg h]
  | cons q qs ih =>
    unfold TermFn.with
    split
    · rw [tlOld_cons]
      by_cases h : t' = t
      · rw [if_pos h.symm, if_pos h]
      · rw [if_neg (Ne.symm h), if_neg h]
        split
        · rename_i he; rw [tlOld_cons, if_neg (by rw [he]; exact Ne.symm h)]
        · rfl
    · rename_i hlt
      rw [tlOld_cons, tlOld_cons, ih]
      by_cases h : t' = t <;> by_cases h2 : q.1 = t' <;> simp only [h, h2, if_true, if_false] <;> omega

/-- A sendable append is from a leader of its term. -/
theorem sendable_led {S : State} {f : AppendFact} (h : S.sendable f = .ok true) :
    S.leaders.contains { server := f.src, term := f.term } = true := by
  unfold State.sendable sendableIn at h
  cases h1 : S.leaders.contains { server := f.src, term := f.term } <;>
    simp only [h1, Bool.not_false, Bool.not_true, ite_true, Bool.false_eq_true, ite_false] at h
  · cases h
  · rfl


/-! ## A commit's `chain` and `termLen` -/

theorem rd_with_mem {α : Type} {f : TermFn α} {t : Int} {v : α} {q : Int × α} (h : q ∈ f.with t v) :
    q ∈ f ∨ q = (t, v) := by
  induction f with
  | nil => simp [TermFn.with] at h; exact .inr h
  | cons p ps ih =>
    unfold TermFn.with at h
    split at h
    · rcases List.mem_cons.mp h with h | h
      · exact .inr h
      · split at h
        · exact .inl (List.mem_cons_of_mem _ h)
        · exact .inl h
    · rcases List.mem_cons.mp h with h | h
      · exact .inl (h ▸ List.mem_cons_self ..)
      · rcases ih h with h | h
        · exact .inl (List.mem_cons_of_mem _ h)
        · exact .inr h

theorem rd_with_self {α : Type} (f : TermFn α) (t : Int) (v : α) : (t, v) ∈ f.with t v := by
  induction f with
  | nil => simp [TermFn.with]
  | cons p ps ih =>
    unfold TermFn.with
    split
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ ih

theorem rd_with_dom (f : TermFn Int) (t v : Int) (hv : tlOld f t ≤ v) :
    ∀ q ∈ f, ∃ q' ∈ f.with t v, q'.1 = q.1 ∧ q.2 ≤ q'.2 := by
  induction f with
  | nil => intro q hq; cases hq
  | cons p ps ih =>
    intro q hq
    unfold TermFn.with
    split
    · rename_i hle
      by_cases hpt : p.1 = t
      · rw [if_pos hpt]
        rcases List.mem_cons.mp hq with rfl | hq
        · refine ⟨(t, v), List.mem_cons_self .., hpt.symm, ?_⟩
          have : tlOld (q :: ps) t = q.2 := by
            unfold tlOld; simp [hpt]
          rw [this] at hv; exact hv
        · exact ⟨q, List.mem_cons_of_mem _ hq, rfl, Int.le_refl _⟩
      · rw [if_neg hpt]
        exact ⟨q, List.mem_cons_of_mem _ hq, rfl, Int.le_refl _⟩
    · rename_i hlt
      have hpt : p.1 ≠ t := by omega
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨q, List.mem_cons_self .., rfl, Int.le_refl _⟩
      · have hold : tlOld (p :: ps) t = tlOld ps t := by
          unfold tlOld; simp [hpt]
        rw [hold] at hv
        obtain ⟨q', hq', h1, h2⟩ := ih hv q hq
        exact ⟨q', List.mem_cons_of_mem _ hq', h1, h2⟩

/-- `TermFn.with` keeps a function sorted by term (C3's `TlSorted`). -/
theorem with_sorted {α : Type} {f : TermFn α} (t : Int) (v : α) (h : f.Pairwise (fun a b => a.1 < b.1)) :
    (f.with t v).Pairwise (fun a b => a.1 < b.1) := by
  induction f with
  | nil => exact List.pairwise_singleton _ _
  | cons p ps ih =>
    rw [List.pairwise_cons] at h
    unfold TermFn.with
    split
    · rename_i hle
      split
      · rename_i he
        refine List.pairwise_cons.mpr ⟨fun q hq => ?_, h.2⟩
        have := h.1 q hq; omega
      · rename_i he
        refine List.pairwise_cons.mpr ⟨fun q hq => ?_, List.pairwise_cons.mpr h⟩
        rcases List.mem_cons.mp hq with rfl | hq
        · omega
        · have := h.1 q hq; omega
    · rename_i hlt
      refine List.pairwise_cons.mpr ⟨fun q hq => ?_, ih h.2⟩
      rcases rd_with_mem hq with hq | rfl
      · exact h.1 q hq
      · show p.1 < t; omega

/-- In a sorted `termLen`, a term's entry is what `tlOld` finds. -/
theorem tlOld_mem {tl : TermFn Int} (hs : tl.Pairwise (fun a b => a.1 < b.1)) {q : Int × Int}
    (hq : q ∈ tl) : tlOld tl q.1 = q.2 := by
  induction tl with
  | nil => cases hq
  | cons p ps ih =>
    rw [List.pairwise_cons] at hs
    rw [tlOld_cons]
    rcases List.mem_cons.mp hq with rfl | hq'
    · rw [if_pos rfl]
    · have := hs.1 q hq'
      rw [if_neg (by omega)]; exact ih hs.2 hq'

theorem tlOld_cases (tl : TermFn Int) (t : Int) :
    tlOld tl t = 0 ∨ ∃ q ∈ tl, q.1 = t ∧ q.2 = tlOld tl t := by
  unfold tlOld
  cases h : tl.find? (fun p => p.1 == t) with
  | none => exact .inl rfl
  | some q =>
    have hm := List.mem_of_find?_eq_some h
    have hq := List.find?_some h
    exact .inr ⟨q, hm, by simpa using hq, rfl⟩

theorem logOf_take_len (l : List EntryM) (k : Nat) : (logOf (l.take k)).length = min k l.length := by
  rw [logOf_length, List.length_take]


theorem plog_take_append {l ents : List EntryM} {j : Nat} (hj : j ≤ l.length) {k : w64}
    (hk1 : 1 ≤ uint.Z k) :
    plogTermAt base0 (l.take j ++ ents) k =
      if uint.Z k ≤ j then plogTermAt base0 l k
      else (fun e : EntryM => e.Term') <$> ents[(uint.Z k - j - 1).toNat]? := by
  have hb : uint.Z (base0 : go_etcd_io.raft.v3.entryID).index' = 0 := rfl
  unfold plogTermAt
  rw [hb, if_neg (by omega), if_neg (by omega)]
  split
  · rename_i hkj
    rw [if_neg (by omega), if_neg (by omega), List.getElem?_append_left (by rw [List.length_take]; omega),
      List.getElem?_take_of_lt (by omega)]
  · rename_i hkj
    rw [List.getElem?_append_right (by rw [List.length_take]; omega), List.length_take,
      Nat.min_eq_left hj]
    congr 2; omega


/-! ## `readyS`'s fields -/

section fields
variable (S : State) (n : Nat) (t1 : Int) (vo : Option Str) (L1 : List Entry) (c : Int)
  (ro : List Str) (cf : Confirmed) (M : List Fact) (Vs : List VoteRec) (ld : List LeaderRec)
  (ll : TermFn (List Entry)) (p : Pre) (ch : List Entry) (tl : TermFn Int) (vi : SSet) (r : MemResult)
theorem rS_ct : (readyS S n t1 vo L1 c ro cf M Vs ld ll p ch tl vi r).currentTerm = S.currentTerm.set n t1 := rfl
theorem rS_msgs : (readyS S n t1 vo L1 c ro cf M Vs ld ll p ch tl vi r).msgs = M := rfl
theorem rS_votes : (readyS S n t1 vo L1 c ro cf M Vs ld ll p ch tl vi r).votes = Vs := rfl
theorem rS_log : (readyS S n t1 vo L1 c ro cf M Vs ld ll p ch tl vi r).log = S.log.set n L1 := rfl
theorem rS_cfg : (readyS S n t1 vo L1 c ro cf M Vs ld ll p ch tl vi r).cfg = S.cfg := rfl
end fields

theorem plog_pos {l : List EntryM} {k : w64} (hk1 : 1 ≤ uint.Z k) :
    plogTermAt base0 l k = (fun e : EntryM => e.Term') <$> l[(uint.Z k - 1).toNat]? := by
  have hb : uint.Z (base0 : go_etcd_io.raft.v3.entryID).index' = 0 := rfl
  unfold plogTermAt
  rw [hb, if_neg (by omega), if_neg (by omega)]
  congr 2


/-! ## A commit -/

/-- **A commit to `cc` at term `T`** (`OnDisk`'s `ch1` and `termLen` when the commit moves, B 422-423):
`chain` extended to the new committed prefix where it is longer, `termLen[T]` raised to it; what
`ReadyOk` needs of them, from `chain` and the new prefix both prefixes of the committed log (C5,
`ReadyFacts`). -/
theorem commit_fields {R : RunCfg} {dec : CCDec} {S : State} {net : List Msg} {G : RaftFacts} {n : Fin R.N}
    {l : List EntryM} {cc T : w64} (hb : BindingOk R dec S) (hgo : GlobalOk R S net G)
    (hcL : uint.Z cc ≤ l.length) (hcG : l.take (uint.nat cc) = G.committed.take (uint.nat cc))
    (hcGl : uint.nat cc ≤ G.committed.length) (hcm : (T, uint.nat cc) ∈ G.commits)
    (hold : S.commitIndex[n.val]! < uint.Z cc) :
    S.chain <+: (if S.commitIndex[n.val]! < uint.Z cc ∧ (S.chain.length : Int) < uint.Z cc then
        (logOf l).take (uint.Z cc).toNat else S.chain) ∧
    (uint.Z cc ≤ (if S.commitIndex[n.val]! < uint.Z cc ∧ (S.chain.length : Int) < uint.Z cc then
        (logOf l).take (uint.Z cc).toNat else S.chain).length ∧
      (if S.commitIndex[n.val]! < uint.Z cc ∧ (S.chain.length : Int) < uint.Z cc then
        (logOf l).take (uint.Z cc).toNat else S.chain).take (uint.Z cc).toNat =
        (logOf l).take (uint.Z cc).toNat) ∧
    (∀ q ∈ S.termLen.with (uint.Z T) (imax (tlOld S.termLen (uint.Z T)) (uint.Z cc)),
      q.2 ≤ (if S.commitIndex[n.val]! < uint.Z cc ∧ (S.chain.length : Int) < uint.Z cc then
        (logOf l).take (uint.Z cc).toNat else S.chain).length) ∧
    (uint.Z cc = 0 ∨ ∃ q ∈ S.termLen.with (uint.Z T) (imax (tlOld S.termLen (uint.Z T)) (uint.Z cc)),
      q.1 ≤ uint.Z T ∧ uint.Z cc ≤ q.2) ∧
    (∀ q ∈ S.termLen, ∃ q' ∈ S.termLen.with (uint.Z T) (imax (tlOld S.termLen (uint.Z T)) (uint.Z cc)),
      q'.1 = q.1 ∧ q.2 ≤ q'.2) ∧
    (∃ c' ≤ G.committed.length, (if S.commitIndex[n.val]! < uint.Z cc ∧ (S.chain.length : Int) < uint.Z cc
        then (logOf l).take (uint.Z cc).toNat else S.chain) = logOf (G.committed.take c')) ∧
    (∀ q ∈ S.termLen.with (uint.Z T) (imax (tlOld S.termLen (uint.Z T)) (uint.Z cc)),
      0 ≤ q.2 ∧ ∃ x, uint.Z x = q.1 ∧ (x, q.2.toNat) ∈ G.commits) := by
  obtain ⟨c', hc', hch⟩ := hgo.2.2.2.2.1
  have hb4 := hb.2.1
  have hnc : (uint.Z cc).toNat = uint.nat cc := uZ_toNat_nat cc
  have hnew : (logOf l).take (uint.Z cc).toNat = logOf (G.committed.take (uint.nat cc)) := by
    rw [hnc, logOf_take, hcG]
  have hchl : (S.chain.length : Int) = c' := by
    rw [hch, logOf_take_len]; omega
  have hcz : (uint.nat cc : Int) = uint.Z cc := by word
  -- the new chain
  have hP : S.chain <+: (if S.commitIndex[n.val]! < uint.Z cc ∧ (S.chain.length : Int) < uint.Z cc then
        (logOf l).take (uint.Z cc).toNat else S.chain) ∧
      (uint.Z cc ≤ (if S.commitIndex[n.val]! < uint.Z cc ∧ (S.chain.length : Int) < uint.Z cc then
        (logOf l).take (uint.Z cc).toNat else S.chain).length ∧
      (if S.commitIndex[n.val]! < uint.Z cc ∧ (S.chain.length : Int) < uint.Z cc then
        (logOf l).take (uint.Z cc).toNat else S.chain).take (uint.Z cc).toNat =
        (logOf l).take (uint.Z cc).toNat) ∧
      (∃ c' ≤ G.committed.length, (if S.commitIndex[n.val]! < uint.Z cc ∧ (S.chain.length : Int) < uint.Z cc
        then (logOf l).take (uint.Z cc).toNat else S.chain) = logOf (G.committed.take c')) := by
    by_cases h : S.commitIndex[n.val]! < uint.Z cc ∧ (S.chain.length : Int) < uint.Z cc
    · rw [if_pos h, hnew, hch]
      refine ⟨?_, ⟨?_, ?_⟩, uint.nat cc, hcGl, rfl⟩
      · apply List.IsPrefix.map
        have : c' ≤ uint.nat cc := by omega
        have e : G.committed.take c' = (G.committed.take (uint.nat cc)).take c' := by
          rw [List.take_take]; congr 1; omega
        rw [e]; exact List.take_prefix _ _
      · rw [logOf_take_len]; omega
      · rw [hnc, List.take_of_length_le (by rw [logOf_take_len]; omega)]
    · rw [if_neg h]
      have hge : uint.Z cc ≤ S.chain.length := by omega
      refine ⟨List.prefix_refl _, ⟨hge, ?_⟩, c', hc', hch⟩
      rw [hnew, hch, hnc, logOf_take, List.take_take]; congr 2; omega
  obtain ⟨hP1, hP2, hP3⟩ := hP
  have hlen : (S.chain.length : Int) ≤ (if S.commitIndex[n.val]! < uint.Z cc ∧ (S.chain.length : Int) < uint.Z cc
        then (logOf l).take (uint.Z cc).toNat else S.chain).length := by
    have := hP1.length_le; omega
  have hold0 : 0 ≤ tlOld S.termLen (uint.Z T) ∧ tlOld S.termLen (uint.Z T) ≤ S.chain.length ∧
      (tlOld S.termLen (uint.Z T) = 0 ∨ (T, (tlOld S.termLen (uint.Z T)).toNat) ∈ G.commits) := by
    rcases tlOld_cases S.termLen (uint.Z T) with h | ⟨q, hq, h1, h2⟩
    · rw [h]; exact ⟨Int.le_refl _, by omega, .inl rfl⟩
    · obtain ⟨g0, x, hx, hxg⟩ := hgo.2.2.2.2.2.1 q hq
      have hxT : x = T := uZ_inj (by rw [hx, h1])
      rw [← h2]
      exact ⟨g0, hb4 q hq, .inr (by rw [← hxT]; exact hxg)⟩
  have hcz0 : 0 ≤ uint.Z cc := by word
  refine ⟨hP1, hP2, ?_, .inr ⟨_, rd_with_self _ _ _, Int.le_refl _, by unfold imax; split <;> omega⟩,
    rd_with_dom _ _ _ (by unfold imax; split <;> omega), hP3, ?_⟩
  · intro q hq
    rcases rd_with_mem hq with hq | rfl
    · have := hb4 q hq; omega
    · show imax _ _ ≤ _
      have := hP2.1
      unfold imax; split <;> omega
  · intro q hq
    rcases rd_with_mem hq with hq | rfl
    · exact hgo.2.2.2.2.2.1 q hq
    · refine ⟨by unfold imax; split <;> omega, T, rfl, ?_⟩
      show (T, (imax _ _).toNat) ∈ G.commits
      unfold imax
      split
      · rcases hold0.2.2 with h0 | h0
        · rename_i hge
          have : uint.Z cc = 0 := by omega
          rw [h0]; rw [this] at hnc; rw [← hnc] at hcm; exact hcm
        · exact h0
      · rw [hnc]; exact hcm

theorem nat_commit_le {G : RaftFacts} {id : w64} {r : RState} (hrf : ReadyFacts G id r) :
    uint.Z r.p.commit ≤ r.full.length := by
  have h1 := hrf.2.1
  have h2 := congrArg List.length hrf.2.2.1
  rw [List.length_take, List.length_take] at h2
  have : uint.nat r.p.commit ≤ r.full.length := by omega
  word


end ready

end AntSim
end EtcdGrove
end Perennial
