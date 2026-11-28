/-
Lean-first (no Rocq counterpart). #33 parity B1, driver group E (`node.drain`): **the drain's
per-report Sim steps**, in the shape `HarnessReport.report_upd` takes (`hstep`), over the Sim's
`_in` theorems at `mskB1` (S4's `DrainSteps`, over `Fin R.N`, `xnet` and `SimStep`):
- `inMask_b1_of`, `rnLe_scopeMd_b1`: a run of B1's off bits is within `mskB1` (`InMask`), from its
  relation (`AntSim`: every message sent under the run's mask);
- `FactsLe`, `globalOk_mono`: raft's facts grown, which keeps `GlobalOk` (new leaders past the boot
  term in a bootstrapped run, the acknowledgements unchanged);
- `readyHstep` (`antSim_ready_in`, over the `.loop` phase's `Reach` through `reachIn_b1`),
  `sendHstep` (`antSim_send_in`), `sendXHstep` (`antSim_sendX_in`), `applyHstep`
  (`antSim_apply_in`), `readHstep` (`antSim_read_in`).
`antSim_readyA.law`: `antSim_ready_in`'s statement at any `Adm` (the `.loop` phase's `Reach` is at
`AdmFold`; the Sim's proof reads `Adm` nowhere: `rdCtx_of` goes through `ReachIn.toP`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainBridge
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.ReadyAll
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Send
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.XMsgs
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Apply
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Reads

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

/-! ## The run within `mskB1` -/

theorem mskB1_le : AntSim.mskB1 ≤ AntSim.mskB1 := by
  simp [LE.le, AntSim.SimMask.Le, AntSim.RnMode.Le, AntSim.NodeK.Le, AntSim.BLe]

/-- The mask of a scope without forwarding, async storage, snapshots and conf changes is within
`mskB1`'s. -/
theorem rnLe_scopeMd_b1 (s : H.Scope) (m : H.Mode) (hfw : s.Forwarding' = false)
    (has : m.Async' = false) (hsn : s.Snapshots' = false) (hcc : s.ConfChanges' = false) :
    AntSim.RnMode.Le (scopeMd s m) AntSim.mskB1.md := by
  simp [AntSim.RnMode.Le, AntSim.BLe, scopeMd, AntSim.mskB1, hfw, has, hsn, hcc]

/-- **A run of B1's off bits is within `mskB1`**: its features `mskB1`'s, no driver mode, and every
message sent under the run's mask (`NetOk`'s `MsgMask`). -/
theorem inMask_b1_of {R : AntSim.RunCfg} {dec : CCDec} {S : AntCheck.State}
    {V : Fin R.N → AntSim.NodeView} {net : List Msg} {xnet : List XMsg}
    (hmd : AntSim.RnMode.Le R.md AntSim.mskB1.md) (hb : R.drv.batch = false)
    (hp : R.drv.parallel = false) (hs : R.drv.split = 0) (hr : R.drv.restarts = false)
    (hA : AntSim.AntSim R dec S V net xnet) : AntSim.InMask AntSim.mskB1 R net xnet := by
  obtain ⟨-, -, hn, -, -⟩ := hA
  have hmm : ∀ m ∈ net, AntSim.MsgMask R m := hn.2.2.2.2.1
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hmd
  refine ⟨⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩, fun _ => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [AntSim.NodeK.Le, AntSim.BLe, AntSim.mskB1]
  · simp [AntSim.BLe, hb]
  · simp [AntSim.BLe, hp]
  · intro h; exact absurd hs h
  · simp [AntSim.BLe, hr]
  · intro m hm
    obtain ⟨-, -, h3, -⟩ := hmm m hm
    rcases h3 with h | h
    · left
      simp only [AntSim.NetTy] at h ⊢
      rcases h with h | h | h | h | h | h | ⟨hpv, h⟩ | ⟨hrd, h⟩ | ⟨hsn, h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h⟩)))))))
      · exact absurd (m6 hsn) (by simp [AntSim.mskB1])
    · exact Or.inr h
  · intro h; simp [AntSim.mskB1] at h

/-! ## Raft's facts grown -/

/-- **Raft's facts `G'` extend `G`** (S4's `RaftFacts.Le` at `R`): every list grown, the committed
log extended, a new leader past the boot term in a bootstrapped run. -/
def FactsLe (R : AntSim.RunCfg) (G G' : AntSim.RaftFacts) : Prop :=
  (∀ x ∈ G.leaders, x ∈ G'.leaders) ∧
  (∀ x ∈ G'.leaders, x ∉ G.leaders → R.boot = true → 2 ≤ uint.Z x.2) ∧
  (∀ x ∈ G.votes, x ∈ G'.votes) ∧ (∀ x ∈ G.logs, x ∈ G'.logs) ∧ (∀ x ∈ G.camps, x ∈ G'.camps) ∧
  G.committed <+: G'.committed ∧ (∀ x ∈ G.commits, x ∈ G'.commits)

theorem FactsLe.refl (R : AntSim.RunCfg) (G : AntSim.RaftFacts) : FactsLe R G G :=
  ⟨fun _ h => h, fun _ h h' => absurd h h', fun _ h => h, fun _ h => h, fun _ h => h,
    List.prefix_refl _, fun _ h => h⟩

/-- **`GlobalOk` is kept by larger facts** (S4's `globalOk_mono`). -/
theorem globalOk_mono {R : AntSim.RunCfg} {S : AntCheck.State} {net : List Msg}
    {G G' : AntSim.RaftFacts} (hG : AntSim.GlobalOk R S net G) (hle : FactsLe R G G') :
    AntSim.GlobalOk R S net G' := by
  obtain ⟨hl, hv, hlog, hled, ⟨c, hc, hch⟩, htl, happ, ⟨hbl, hbt⟩⟩ := hG
  obtain ⟨hL, hLn, hV, hLg, hC, hP, hCs⟩ := hle
  refine ⟨?_, ?_, ?_, ?_, ⟨c, ?_, ?_⟩, ?_, ?_, ⟨hLg _ hbl, ?_⟩⟩
  · intro l h
    rcases hl l h with h0 | ⟨j, t, hm, h1, h2⟩
    · exact Or.inl h0
    · exact Or.inr ⟨j, t, hL _ hm, h1, h2⟩
  · intro x h
    obtain ⟨a, t, c, hm, h1, h2, h3⟩ := hv x h
    exact ⟨a, t, c, hV _ hm, h1, h2, h3⟩
  · intro n
    obtain ⟨l, hm, h1⟩ := hlog n
    exact ⟨l, hLg _ hm, h1⟩
  · intro p h
    rcases hled p h with h0 | ⟨l, hm, h1, t, l0, h2, h3, h4⟩
    · exact Or.inl h0
    · exact Or.inr ⟨l, hLg _ hm, h1, t, l0, h2, hC _ h3, h4⟩
  · exact Nat.le_trans hc hP.length_le
  · rw [hch]
    obtain ⟨d, hd⟩ := hP
    rw [← hd, List.take_append_of_le_length hc]
  · intro p h
    obtain ⟨h0, x, h1, h2⟩ := htl p h
    exact ⟨h0, x, h1, hCs _ h2⟩
  · intro m hm hty
    obtain ⟨l, hl', h1⟩ := happ m hm hty
    exact ⟨l, hLg _ hl', h1⟩
  · intro hb j t hjt
    by_cases hin : (j, t) ∈ G.leaders
    · exact hbt hb j t hin
    · exact hLn (j, t) hjt hin hb

/-- Node `j`'s view replaced by one with a certified full log keeps every view's certified. -/
theorem setV_logs {R : AntSim.RunCfg} {V : Fin R.N → AntSim.NodeView} {j : Fin R.N}
    {v' : AntSim.NodeView} {G0 G : AntSim.RaftFacts}
    (hlogs : ∀ i : Fin R.N, (V i).r.full ∈ G0.logs) (hle : ∀ x ∈ G0.logs, x ∈ G.logs)
    (hv' : v'.r.full ∈ G.logs) : ∀ i : Fin R.N, (AntSim.setV V j v' i).r.full ∈ G.logs := by
  intro i
  unfold AntSim.setV
  split
  · exact hv'
  · exact hle _ (hlogs i)

/-! ## The reports' steps -/

/-- The view after a `send` report of its next pending message (`rest` left). -/
abbrev sendView (v : AntSim.NodeView) (rest : List Msg) : AntSim.NodeView :=
  { v with pend := rest, undo := none, made := true }

/-- The view after a transfer message's `send` report. -/
abbrev sendXView (v : AntSim.NodeView) (rest : List XMsg) : AntSim.NodeView :=
  { v with xpend := rest, undo := none, made := true }

/-- The view after the `apply` report. -/
abbrev applyView (v : AntSim.NodeView) : AntSim.NodeView :=
  { v with delivered := v.delivered ++ v.ce, ce := [], undo := none, made := true }

/-- The view after a `read` report of its next read state `rs` (`rest` left). -/
abbrev readView (v : AntSim.NodeView) (rs : ReadStateM) (rest : List ReadStateM) : AntSim.NodeView :=
  { v with rpend := rest, reads := v.reads.filter (fun p => decide (p.1 ≠ rs.RequestCtx')) }

/-- **`antSim_ready_in`'s statement at any admissibility `Adm`** (the Sim's theorem is at
`admOf G`; its proof reads the `Reach` only through `ReachIn.toP`, which is at any `Adm`). -/
abbrev antSim_readyA.law : Prop :=
  ∀ (R : AntSim.RunCfg) (dec : CCDec) (S : AntCheck.State)
    (V : Fin R.N → AntSim.NodeView) (net : List Msg) (xnet : List XMsg)
    (evs : List AntCheck.Event) (G : AntSim.RaftFacts) (n : Fin R.N) (r₁ : RState)
    (rd : AntSim.ReadyD) {Adm : List EntryM → CCState → Prop},
    AntSim.InMask AntSim.mskB1 R net xnet →
    AntSim.SimPre R dec S V net xnet evs G → R.md.async = false →
    AntSim.ReachIn AntSim.mskB1 R dec Adm net xnet n (V n) r₁ → AntSim.ReadyOutP R n (V n) r₁ rd →
    AntSim.Reported (V n) rd → AntSim.Told (V n) → AntSim.ReadyFacts G (AntSim.nodeId n) r₁ →
    AntSim.TermRoom (V n) →
    AntSim.SimStep R dec evs G
      (AntSim.evReady (AntSim.nodeId n) (V n).byE (AntSim.roleStr rd.pre rd.role) rd.term rd.vote
        rd.commit rd.ents rd.snap)
      (AntSim.setV V n ((V n).afterReady r₁ rd)) net xnet

/-- **The `ready` report's step** (`report_upd`'s `hstep`): at a loop head of the `.loop` phase
(`Reach` over the lower bounds `net₀`, `xnet₀` at the `.loop`'s admissibility `Adm`), a reported
`Ready`'s `ReadyOutP` (`readyOutP_of`); raft's facts grown by the `Ready`'s (`FactsLe`, lawful, with
`ReadyFacts`). -/
theorem readyHstep (h_ready : antSim_readyA.law) {R : AntSim.RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} (j : Fin R.N) (v : AntSim.NodeView) (r₁ : RState)
    (rd : AntSim.ReadyD) (net₀ : List Msg) (xnet₀ : List XMsg)
    (hinm : ∀ S V net xnet, AntSim.AntSim R dec S V net xnet → AntSim.InMask AntSim.mskB1 R net xnet)
    (hasync : R.md.async = false) (hcc : R.md.confChanges = false) (hby : ByOk v.byE)
    (hreach : AntSim.Reach R dec Adm net₀ xnet₀ j v r₁) (hout : AntSim.ReadyOutP R j v r₁ rd)
    (hrep : AntSim.Reported v rd) (htold : AntSim.Told v) (hterm : AntSim.TermRoom v) :
    ∀ (evs : List AntCheck.Event) (S : AntCheck.State) (V : Fin R.N → AntSim.NodeView)
      (net : List Msg) (xnet : List XMsg) (G0 G : AntSim.RaftFacts),
      AntSim.SimPre R dec S V net xnet evs G0 → (∀ i : Fin R.N, (V i).r.full ∈ G0.logs) →
      (FactsLe R G0 G ∧ AntSim.RaftLaws G ∧ AntSim.ReadyFacts G (AntSim.nodeId j) r₁) →
      V j = v → net₀ <+: net → xnet₀ <+: xnet →
      AntSim.SimStep R dec evs G
          (AntSim.evReady (AntSim.nodeId j) v.byE (AntSim.roleStr rd.pre rd.role) rd.term rd.vote
            rd.commit rd.ents rd.snap)
          (AntSim.setV V j (v.afterReady r₁ rd)) (net ++ []) (xnet ++ []) ∧
        AntSim.RaftLaws G ∧ ∀ i : Fin R.N, (AntSim.setV V j (v.afterReady r₁ rd) i).r.full ∈ G.logs := by
  intro evs S V net xnet G0 G hpre hlogs ⟨hle, hL, hrf⟩ hVj hn hx
  subst hVj
  have hpre' : AntSim.SimPre R dec S V net xnet evs G :=
    ⟨hpre.1, hpre.2.1, hL, globalOk_mono hpre.2.2.2 hle⟩
  have hr := reachIn_b1 hcc hby hreach hn hx
  refine ⟨?_, hL, setV_logs hlogs hle.2.2.2.1 hrf.1⟩
  simp only [List.append_nil]
  exact h_ready R dec S V net xnet evs G j r₁ rd (hinm S V net xnet hpre.2.1) hpre' hasync hr
    hout hrep htold hrf hterm

/-- **A `send` report's step** (the next pending message `q`; raft's facts grown by the message's,
`MsgFacts`; a read request's answer's numbers within `2 ^ 61`, `NetOk`'s). -/
theorem sendHstep {R : AntSim.RunCfg} {dec : CCDec} (j : Fin R.N) (v : AntSim.NodeView) (q : Msg)
    (rest : List Msg) (net₀ : List Msg) (xnet₀ : List XMsg)
    (hinm : ∀ S V net xnet, AntSim.AntSim R dec S V net xnet → AntSim.InMask AntSim.mskB1 R net xnet)
    (hasync : R.md.async = false) (hpend : v.pend = q :: rest) (htold : AntSim.Told v)
    (hnum : q.ty = .readIndexResp → AntSim.MsgNums (2 ^ 61) q) :
    ∀ (evs : List AntCheck.Event) (S : AntCheck.State) (V : Fin R.N → AntSim.NodeView)
      (net : List Msg) (xnet : List XMsg) (G0 G : AntSim.RaftFacts),
      AntSim.SimPre R dec S V net xnet evs G0 → (∀ i : Fin R.N, (V i).r.full ∈ G0.logs) →
      (FactsLe R G0 G ∧ AntSim.RaftLaws G ∧ AntSim.MsgFacts G q) →
      V j = v → net₀ <+: net → xnet₀ <+: xnet →
      AntSim.SimStep R dec evs G (AntSim.evSend (AntSim.nodeId j) v.byE q)
          (AntSim.setV V j (sendView v rest)) (net ++ [q])
          (xnet ++ []) ∧
        AntSim.RaftLaws G ∧
        ∀ i : Fin R.N, (AntSim.setV V j (sendView v rest) i).r.full ∈ G.logs := by
  intro evs S V net xnet G0 G hpre hlogs ⟨hle, hL, hmf⟩ hVj _ _
  subst hVj
  have hpre' : AntSim.SimPre R dec S V net xnet evs G :=
    ⟨hpre.1, hpre.2.1, hL, globalOk_mono hpre.2.2.2 hle⟩
  refine ⟨?_, hL, setV_logs hlogs hle.2.2.2.1 (hle.2.2.2.1 _ (hlogs j))⟩
  simp only [List.append_nil]
  exact AntSim.antSim_send_in AntSim.mskB1 mskB1_le R dec S V net xnet evs G j q rest
    (hinm S V net xnet hpre.2.1) hpre' hasync hpend htold hmf hnum

/-- **A transfer message's `send` report's step** (the next pending transfer message `x`; nothing
grown). -/
theorem sendXHstep {R : AntSim.RunCfg} {dec : CCDec} (j : Fin R.N) (v : AntSim.NodeView) (x : XMsg)
    (rest : List XMsg) (net₀ : List Msg) (xnet₀ : List XMsg)
    (hinm : ∀ S V net xnet, AntSim.AntSim R dec S V net xnet → AntSim.InMask AntSim.mskB1 R net xnet)
    (hasync : R.md.async = false) (hxp : v.xpend = x :: rest) (htold : AntSim.Told v) :
    ∀ (evs : List AntCheck.Event) (S : AntCheck.State) (V : Fin R.N → AntSim.NodeView)
      (net : List Msg) (xnet : List XMsg) (G0 G : AntSim.RaftFacts),
      AntSim.SimPre R dec S V net xnet evs G0 → (∀ i : Fin R.N, (V i).r.full ∈ G0.logs) →
      G = G0 →
      V j = v → net₀ <+: net → xnet₀ <+: xnet →
      AntSim.SimStep R dec evs G (AntSim.evSendX (AntSim.nodeId j) v.byE x)
          (AntSim.setV V j (sendXView v rest)) (net ++ [])
          (xnet ++ [x]) ∧
        AntSim.RaftLaws G ∧
        ∀ i : Fin R.N, (AntSim.setV V j (sendXView v rest) i).r.full ∈ G.logs := by
  intro evs S V net xnet G0 G hpre hlogs hG hVj _ _
  subst hVj; subst hG
  refine ⟨?_, hpre.2.2.1, setV_logs hlogs (fun _ h => h) (hlogs j)⟩
  simp only [List.append_nil]
  exact AntSim.antSim_sendX_in AntSim.mskB1 mskB1_le R dec S V net xnet evs _ j x rest
    (hinm S V net xnet hpre.2.1) hpre hasync hxp htold

/-- **The `apply` report's step** (nothing grown). -/
theorem applyHstep {R : AntSim.RunCfg} {dec : CCDec} (j : Fin R.N) (v : AntSim.NodeView)
    (net₀ : List Msg) (xnet₀ : List XMsg)
    (hinm : ∀ S V net xnet, AntSim.AntSim R dec S V net xnet → AntSim.InMask AntSim.mskB1 R net xnet)
    (hasync : R.md.async = false) (hce : v.ce ≠ []) (htold : AntSim.Told v) :
    ∀ (evs : List AntCheck.Event) (S : AntCheck.State) (V : Fin R.N → AntSim.NodeView)
      (net : List Msg) (xnet : List XMsg) (G0 G : AntSim.RaftFacts),
      AntSim.SimPre R dec S V net xnet evs G0 → (∀ i : Fin R.N, (V i).r.full ∈ G0.logs) →
      G = G0 → V j = v → net₀ <+: net → xnet₀ <+: xnet →
      AntSim.SimStep R dec evs G (AntSim.evApply (AntSim.nodeId j) v.byE v.ce)
          (AntSim.setV V j (applyView v)) (net ++ []) (xnet ++ []) ∧
        AntSim.RaftLaws G ∧
        ∀ i : Fin R.N, (AntSim.setV V j (applyView v) i).r.full ∈ G.logs := by
  intro evs S V net xnet G0 G hpre hlogs hG hVj _ _
  subst hVj; subst hG
  refine ⟨?_, hpre.2.2.1, setV_logs hlogs (fun _ h => h) (hlogs j)⟩
  simp only [List.append_nil]
  exact AntSim.antSim_apply_in AntSim.mskB1 mskB1_le R dec S V net xnet evs _ j
    (hinm S V net xnet hpre.2.1) hpre hasync hce htold

/-- **A `read` report's step** (the next pending read state `rs`, at an index past every committed
length its context was asked at; nothing grown). -/
theorem readHstep {R : AntSim.RunCfg} {dec : CCDec} (j : Fin R.N) (v : AntSim.NodeView)
    (rs : ReadStateM) (rest : List ReadStateM) (net₀ : List Msg) (xnet₀ : List XMsg)
    (hinm : ∀ S V net xnet, AntSim.AntSim R dec S V net xnet → AntSim.InMask AntSim.mskB1 R net xnet)
    (hrp : v.rpend = rs :: rest) (htold : AntSim.Told v)
    (hfl : ∀ f, (rs.RequestCtx', f) ∈ v.reads → f ≤ uint.nat rs.Index') :
    ∀ (evs : List AntCheck.Event) (S : AntCheck.State) (V : Fin R.N → AntSim.NodeView)
      (net : List Msg) (xnet : List XMsg) (G0 G : AntSim.RaftFacts),
      AntSim.SimPre R dec S V net xnet evs G0 → (∀ i : Fin R.N, (V i).r.full ∈ G0.logs) →
      G = G0 → V j = v → net₀ <+: net → xnet₀ <+: xnet →
      AntSim.SimStep R dec evs G (AntSim.evRead (AntSim.nodeId j) rs.RequestCtx' rs.Index')
          (AntSim.setV V j (readView v rs rest)) (net ++ [])
          (xnet ++ []) ∧
        AntSim.RaftLaws G ∧
        ∀ i : Fin R.N, (AntSim.setV V j (readView v rs rest) i).r.full ∈ G.logs := by
  intro evs S V net xnet G0 G hpre hlogs hG hVj _ _
  subst hVj; subst hG
  refine ⟨?_, hpre.2.2.1, setV_logs hlogs (fun _ h => h) (hlogs j)⟩
  simp only [List.append_nil]
  exact AntSim.antSim_read_in AntSim.mskB1 mskB1_le R dec S V net xnet evs _ j rs rest
    (hinm S V net xnet hpre.2.1) hpre hrp htold hfl

/-! ### A transfer message's destination -/

/-- **A `Ready`'s transfer message is to a server**: its certificates' maps (`isRaftMsg_xdst`: a
`MsgTimeoutNow`'s destination has an acknowledgement map, a stamped `MsgTransferLeader`'s a winners
map) and `antCluster`'s names facts (those maps named for the run's servers only); a
`MsgTransferLeader` stamped (`XReadyOk`). `xPendOk_of`'s `htn`/`htr`. -/
theorem xdst_server {R : AntSim.RunCfg} {γr : RaftNames} {st : MsgSt} {x : XMsg}
    (hx : xmsgOf st = some x)
    (hcert : (st.msg.Type' = MsgTimeoutNow → (γr.reAcks !! st.msg.To').isSome) ∧
      (st.msg.Type' = MsgTransferLeader → st.msg.Term' ≠ W64 0 → (γr.reWins !! st.msg.To').isSome))
    (hacks : ∀ a : w64, (γr.reAcks !! a).isSome → ∃ j : Fin R.N, a = AntSim.nodeId j)
    (hwins : ∀ a : w64, (γr.reWins !! a).isSome → ∃ j : Fin R.N, a = AntSim.nodeId j)
    (htl : x.ty = .transferLeader → x.term ≠ W64 0) :
    ∃ j : Fin R.N, x.dst = AntSim.nodeId j := by
  unfold xmsgOf at hx
  by_cases h1 : st.msg.Type' = MsgTimeoutNow
  · rw [if_pos h1] at hx; cases hx; exact hacks _ (hcert.1 h1)
  · rw [if_neg h1] at hx
    by_cases h2 : st.msg.Type' = MsgTransferLeader
    · rw [if_pos h2] at hx; cases hx; exact hwins _ (hcert.2 h2 (htl rfl))
    · rw [if_neg h2] at hx; cases hx

end pure

end AntHarness
end EtcdGrove
end Perennial
