/-
Lean-first (no Rocq counterpart). **`raft.Step`'s traced bundle on `MsgProp` at a leader**
(2026-11-11, trace-check Q8 stage 1 slice 24a, `notes/decisions.md`, "Q8 stage 1 (slice 24a)").

A leader's proposal runs `appendEntry`'s two gates and `bcastAppend`'s (`leaderGates`' `"Hgprep"`,
`"Hgpack"`, `"#Hgpapp"`); the caller's resources are three families:

- before the lines (`G0`, `G1`, at the outbox of `s` only): a local path's family at `s` (`lineF`);
- after the `Replicate` lines (`Gp1`): raft's ghost state at the proposed state (`ghost_stepProp`, run
  inside `"Hgprep"` with what `Step` lends it, `propLend`), the capability pinned after the last line
  (`RepPin`, `TracedRaftStepPropRep.lean`);
- after the self-acknowledgement (`Gp2`, at an outbox longer than `s`'s): raft's ghost state at the
  proposed state, the traced family at the idle server of the appended state (`propF`).

The close tells the two outcomes apart by the outbox's length (`StepEnd`'s `LeaderProposeResult`):
dropped, the ghost state back at `s` (`CloseAt`: the batch not appended); appended, at the proposed state
(`CloseMid`).

**What the path premises** beyond `stepBundle_traced.on`'s (`PropLead`, a path reading the cluster's
names and the batch: `stepBundle_traced.onG`): a non-empty batch of normal entries (the traced node
proposes no configuration change, and the specification's `ClientRequest` is one `Replicate` line per
entry), and a cluster with a bootstrap log (a leader's term is then `≥ 2`, its log past the bootstrap
entries). The node API supplies them (`raft.Step`'s own premises have the first, `Hp3`; the second is
`stepBundle_traced.on`'s premise for `MsgHeartbeat`/`MsgApp`); they become premises of
`stepBundle_traced.on` when the paths are assembled.
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStepPropRep
public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvUTResp

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A leader's last entry is of its term, and its term `≥ 2` in a cluster with a bootstrap log**
(raft's campaign record, `campOwn`: the full log extends the campaign log by an entry of the term;
`isCamp_boot`), at an uncompacted log. -/
theorem ownStepGhost_leadLast (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState)
    (hr : s.role = .leader) (hb : s.logst.prev = base0) :
    ownStepGhost (GF := GF) γ md c id s ⊢
      ⌜(∃ x, (toPState s).log.getLast? = some x ∧ x.Term' = s.term) ∧
        (γ.reBoot ≠ [] → 2 ≤ uint.Z s.term)⌝ ∗ ownStepGhost γ md c id s := by
  apply persistent_entails_right
  iintro H
  iunfold ownStepGhost at H
  icases H with ⟨Hg, -⟩
  unfold ownRaftGhost
  icases Hg with ⟨%γs, %V, %πc, %kl, H⟩
  iNamed H
  unfold ownLogGhost
  icases Hlg with ⟨%γm, %terms, %fp, %γw, %wins, Hlg⟩
  iNamed Hlg
  have hrole : (toPState s).role = .leader := by rw [toPState_role, hr]; rfl
  have hco : ∀ (camps : GMap w64 (List EntryM × w64)) (F : List EntryM),
      campOwn (GF := GF) γ id camps (toPState s) F =
        iprop(∃ F0, isCamp γ id (toPState s).term F0 ∗
          ⌜F0 <+: F ∧ plogLastIndexZ base0 F0 < plogLastIndexZ base0 F ∧
            (plogLast base0 F).term' = (toPState s).term⌝) := by
    intro camps F; unfold campOwn; rw [hrole]
  rw [hco]
  icases Hcown with ⟨%F0, #Hc0, %HF0⟩
  icases isCamp_boot γ id (toPState s).term F0 $$ Hc0 with %Hbt
  ipureintro
  obtain ⟨Hfo, -, -⟩ := Hfull
  have hfp : fp = [] := by
    have h := Hfo.1
    have hb' : (toPState s).base = base0 := hb
    rw [hb', base0_index] at h; exact List.eq_nil_of_length_eq_zero (by omega)
  subst hfp
  obtain ⟨-, hlt, hlast⟩ := HF0
  simp only [List.nil_append] at hlt hlast
  refine ⟨?_, Hbt.2⟩
  cases hl : (toPState s).log.getLast? with
  | none =>
    exfalso
    rw [List.getLast?_eq_none_iff] at hl
    rw [hl] at hlt
    simp only [plogLastIndexZ, List.length_nil] at hlt
    have := plogLastIndexZ_nonneg base0 F0
    unfold plogLastIndexZ at this
    omega
  | some x =>
    refine ⟨x, rfl, ?_⟩
    unfold plogLast at hlast
    rw [hl] at hlast
    exact hlast

end ghost

section pure
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- **`MsgProp` at a leader**, a non-empty batch of normal entries, in a cluster with a bootstrap log
(see the header). -/
def PropLead (γ : RaftNames) (ents : List EntryM) (s : NState) (m : MessageM) : Prop :=
  m.Type' = MsgProp ∧ s.role = .leader ∧ ents ≠ [] ∧ (∀ e ∈ ents, e.Type' = EntryNormal) ∧ γ.reBoot ≠ []

theorem normalCount_all (ents : List EntryM) (h : ∀ e ∈ ents, e.Type' = EntryNormal) :
    normalCount ents = ents.length := by
  unfold normalCount
  rw [List.filter_eq_self.2 (fun e he => decide_eq_true (h e he))]

theorem noConf_of_normal (ents : List EntryM) (h : ∀ e ∈ ents, e.Type' = EntryNormal) :
    ∀ e ∈ ents, ¬ IsConfEnt e := by
  intro e he hc
  have := h e he
  unfold IsConfEnt at hc
  rw [this] at hc
  simp only [EntryNormal] at hc
  rcases hc with hc | hc
  · have : (W32 0 : w32) ≠ W32 1 := by simp only [ne_eq]; exact of_decide_eq_true rfl
    exact this hc
  · have : (W32 0 : w32) ≠ W32 2 := by simp only [ne_eq]; exact of_decide_eq_true rfl
    exact this hc

theorem propK_zero (s : NState) (es : List EntryM) : propK s es 0 = s := by
  simp [propK, propAppended, logAppend]

theorem propK_full (s : NState) (es : List EntryM) : propK s es es.length = propAppended s es := by
  simp [propK]

/-- The proposed state's log is past `s`'s (`raft__Step/MsgProp.lean`'s `proposed_logst_ne`). -/
theorem proposed_logst_ne' (id : w64) (s : NState) (ents : List EntryM) (hne : ents ≠ []) :
    (proposed id s ents).logst ≠ s.logst := by
  intro h
  have h1 := congrArg (fun l => l.uents.length) h
  simp only [proposed, sendMsgs, logAppend, List.length_append, List.length_mapIdx] at h1
  exact hne (List.eq_nil_of_length_eq_zero (by omega))

theorem msgProp_ne_hup : MsgProp ≠ MsgHup := by simp only [MsgProp, MsgHup, ne_eq]; exact of_decide_eq_true rfl
theorem msgProp_ne_vote : MsgProp ≠ MsgVote := by simp only [MsgProp, MsgVote, ne_eq]; exact of_decide_eq_true rfl

/-- **The end state of a `PropLead` path** (`StepEnd`, traced): dropped, the log and the outbox `s`'s
(only `pendingConfIndex` may move, which the idle relation does not read); appended, the proposed
state's broadcast, the `Match` values unchanged. -/
theorem propLead_end {γ : RaftNames} {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hp : PropLead γ ents s m) (hT0 : m.Term' = W64 0)
    (h : StepEnd c id m ents ctx s s') :
    (s'.logst = s.logst ∧ s'.outbox = s.outbox ∧ ∀ C, SimIdleS C s = SimIdleS C s') ∨
    (∃ (ms : List Msg) (pvs : GMap w64 Progress), s' = { sendMsgs (proposed id s ents) ms with prvals := pvs } ∧
      prvalsMatch pvs = prvalsMatch s.prvals) := by
  obtain ⟨hty, hlead, hne, hnorm, -⟩ := hp
  have hnc := noConf_of_normal ents hnorm
  have hnbf : ¬ PreBF m s := by
    unfold PreBF; rw [hT0]; intro h; have := h.1; simp at this
  have hpre : ∀ pvs, preState s m pvs = s := fun pvs => by simp [preState, hnbf]
  have hns : ¬ StaleMsg s m := fun h => h.1 hT0
  have hte : StepEndTy m.Type' := by unfold StepEndTy; simp [hty]
  obtain ⟨pvs, hfn⟩ := (h hte).2.2.2 hns (by rw [hty]; exact msgProp_ne_hup) (by rw [hty]; exact msgProp_ne_vote)
  rw [hpre pvs] at hfn
  obtain ⟨d, hres⟩ := hfn.2.2 hlead
  unfold LeaderStepResultC at hres
  rw [if_pos hty] at hres
  obtain ⟨cs, hct, -, hres⟩ := hres
  have hlp : leaderPropConf s ents cs c.joint = (ents, s.pci) := propConf_noConf' _ _ _ _ ents cs hct hnc
  rw [hlp] at hres
  simp only at hres
  cases d with
  | true =>
    simp only [↓reduceIte, or_self] at hres
    subst hres
    exact .inl ⟨rfl, rfl, fun _ => rfl⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hres
    obtain ⟨ms, pvs', hs', -, hm⟩ := hres
    exact .inr ⟨ms, pvs', hs', hm⟩

end pure

section families
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The family after the self-acknowledgement**: raft's ghost state at the proposed state, the traced
family at the idle server of the appended state, the outbox's new messages' numbers. -/
def propF (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState) (ents : List EntryM)
    (Λ : Option TraceEv → Prop) (o : List Msg) : IProp GF :=
  iprop(ownStepGhost γ md c id (proposed id s ents) ∗
    (∃ b : Bool, trFam s.gh.tr γ r id c b (fun C => SimIdleS C (propAppended s ents)) Λ o) ∗ ⌜OutOk s o⌝)

/-- `PropLead`'s resources (see the header). -/
def propR (bt : Bool) (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (ents : List EntryM) (Λ : Option TraceEv → Prop) : StepG GF where
  G := trCapB s.gh.tr γ r id c bt (fun C => SimIdle C s) Λ
  G0 := fun o => iprop(⌜o = s.outbox⌝ ∗ lineF γ md c r id s (fun C => SimIdleS C s) (stepLastEv Λ) o)
  G1 := fun o => iprop(⌜o = s.outbox⌝ ∗ lineF γ md c r id s (fun C => SimIdleS C s) (stepLastEv Λ) o)
  GE := fun _ => iprop(⌜False⌝)
  Gf := iprop(⌜False⌝)
  Gb1 := iprop(⌜False⌝)
  Gb2 := iprop(⌜False⌝)
  Gp1 := iprop(∃ (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg), ⌜id ∈ C0⌝ ∗
    ownStepGhost γ md c id (proposed id s ents) ∗
    trCapB s.gh.tr γ r id c true (RepPin s ents s.outbox C0 cs0 P0 ents.length) (stepLastEv Λ))
  Gp2 := fun o => iprop(⌜s.outbox.length < o.length⌝ ∗ propF γ md c r id s ents (stepLastEv Λ) o)
  Gc := fun _ _ _ => iprop(⌜False⌝)

/-- `HookGateN` under an update. -/
theorem hookGateN_fupd (tr : Option GName) (r : Loc) (E : TraceEv → Prop) (n : Nat) (Q : IProp GF) :
    iprop(|={⊤}=> HookGateN tr r E n Q) ⊢ HookGateN tr r E n Q := by
  iintro H
  iunfold HookGateN at H
  iunfold HookGateN
  imod H with H
  iexact H

/-- The `Replicate` lines' chained facts (`fxPres_replicate`, no resource). -/
theorem repChain (γd : GName) (γ : RaftNames) (id : w64) (E : TraceEv → Prop) (s : NState) (ents : List EntryM)
    (o : List Msg) (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg) (hidC : id ∈ C0)
    (hlead : s.role = .leader)
    (hlast : ∃ x, (toPState s).log.getLast? = some x ∧ x.Term' = s.term) (hT2 : 2 ≤ uint.Z s.term)
    (hbnd : plogLastIndexZ (toPState s).base (toPState s).log + ents.length < 2 ^ 63) :
    ⊢ [∗list] k ∈ List.range ents.length, (iprop(emp) -∗
        FxPresUT (GF := GF) (some γd) γ id E (RepPin s ents o C0 cs0 P0 k) (RepPin s ents o C0 cs0 P0 (k + 1))
          iprop(emp)) := by
  apply BigSepL.bigSepL_intro
  intro k x hx
  have hk : x < ents.length := List.mem_range.1 (List.mem_of_getElem? hx)
  iintro - -
  simp only [FxPresUT]
  iapply fxPres_upd
  iapply fxPres_replicate γ id E s ents o C0 cs0 P0 hidC x hk hlead hlast hT2 hbnd

/-- **The `Replicate` gate on `PropLead`'s family** (`leaderGates`' `"Hgprep"`): raft's ghost state moved
to the proposed state with what `Step` lends (`ghost_stepProp`, `propLend`), the share pinned
(`trFam_pin`), the lines fired (`trCapB_hookGateN`: `phaseStepB_replicate`, `fxPres_replicate`). -/
theorem propGate_rep (γd : GName) (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (ents : List EntryM) (Λ : Option TraceEv → Prop) (bt : Bool) (cs : List (Option ConfChangeIM))
    (htr : s.gh.tr = some γd) (hlead : s.role = .leader) (hne : ents ≠ [])
    (hnorm : ∀ e ∈ ents, e.Type' = EntryNormal) (hboot : γ.reBoot ≠ [])
    (hT : uint.Z s.term + 1 < traceNumBound) (hfit : receiptBound GF + γ.reBoot.length ≤ traceNumBound) :
    (ccEntsOk ents cs ∗ propLend γ s ents ∗
        lineF γ md c r id s (fun C => SimIdleS C s) (stepLastEv Λ) s.outbox : IProp GF) ⊢
      HookGateN s.gh.tr r (NodeEvOf (W64 5) id s c) (normalCount (leaderPropConf s ents cs c.joint).1)
        (propR (GF := GF) bt γ md c r id s ents Λ).Gp1 := by
  have hnc := noConf_of_normal ents hnorm
  iintro ⟨#Hcc, HTp, Hlf⟩
  icases ccEntsOk_types ents cs $$ Hcc with %hct
  have hlp : leaderPropConf s ents cs c.joint = (ents, s.pci) := propConf_noConf' _ _ _ _ ents cs hct hnc
  rw [hlp, normalCount_all ents hnorm]
  dsimp only [propR]
  unfold propLend lineF
  rw [htr]
  simp only [Option.isSome_some, ↓reduceIte]
  icases HTp with ⟨Hd, Htk, #Hrc⟩
  iapply hookGateN_fupd
  icases Hlf with ⟨Hgh, ⟨%b, Hf⟩, %Hok⟩
  imod ownStepGhost_traceBound (GF := GF) γ md c id s hfit $$ Hgh with ⟨%Hb, Hgh⟩
  icases trFam_pin γd γ r id c b _ (stepLastEv Λ) s.outbox $$ Hf with ⟨%C0, %cs0, %P0, %Hph, Hf⟩
  obtain ⟨⟨⟨a0, -, -, hs0, -⟩, -⟩, hidC⟩ := Hph
  have hb0 : s.logst.prev = base0 := hs0.1
  icases ownStepGhost_leadLast γ md c id s hlead hb0 $$ Hgh with ⟨%HL, Hgh⟩
  imod ghost_stepProp γ md c id s ents cs hlead hct hnc hT hfit $$ [$Hd $Htk $Hrc $Hgh] with ⟨%hB, Hgh⟩
  icases trCapB_logger γd γ r id c b _ _ $$ Hf with ⟨%tl, #Htl, Hf⟩
  ihave Hf := trCapB_mono (some γd) γ r id c b _ (RepPin s ents s.outbox C0 cs0 P0 0) (stepLastEv Λ)
    (fun C cs P h => by simp only [RepPin, propK_zero, repCN]; exact h) $$ Hf
  have hT2 : 2 ≤ uint.Z s.term := HL.2 hboot
  have hb : traceNumBound = 2 ^ 61 := rfl
  have hbnd : plogLastIndexZ (toPState s).base (toPState s).log + ents.length < 2 ^ 63 := by omega
  have hn0 : ents.length ≠ 0 := fun h => hne (List.eq_nil_of_length_eq_zero h)
  imodintro
  iapply hookGateN_mono (some γd) r _ _
    iprop(trCapB (some γd) γ r id c (if ents.length = 0 then b else true)
      (RepPin s ents s.outbox C0 cs0 P0 ents.length)
      (if ents.length = 0 then stepLastEv Λ else stepLastEv Λ) ∗ emp)
  isplitl [Hgh]
  · iintro ⟨Hc, -⟩
    simp only [hn0, ↓reduceIte]
    iexists C0, cs0, P0
    iframe Hgh Hc
    ipureintro; exact hidC
  ihave Hch := repChain (GF := GF) γd γ id (NodeEvOf (W64 5) id s c) s ents s.outbox C0 cs0 P0 hidC hlead HL.1 hT2
    hbnd
  iapply trCapB_hookGateN (some γd) γ r id c tl _ b (RepPin s ents s.outbox C0 cs0 P0) (stepLastEv Λ)
    (stepLastEv Λ) (fun _ => iprop(emp)) ents.length
    (fun k hk => by
      obtain ⟨e, he⟩ : ∃ e, ents[k]? = some e := ⟨_, List.getElem?_eq_getElem hk⟩
      exact phaseStepB_replicate id c s ents s.outbox C0 cs0 P0 k e he hlead HL.1 hT2 hbnd)
    (fun e he => nodeEvOf_notBoot he (by decide) (by decide) (by decide))
    (fun e _ => .inr rfl)
    (fun _ e he => nodeEvOf_ok (W64 5) id s c e _ he (by decide)
      (by have := Hb; word) (by have := Hb.1; word) (by have := Hb.2; word) (Nat.le_refl _))
    (fun h => by cases h)
  iframe Htl Hf Hch

omit [GooseSemantics] [GooseInterp] go_gctx [StorageModel GF] sem package_sem in
theorem logLast_eq_plastIndex (s : NState) : logLast s.logst = plastIndex (toPState s) := by
  simp only [plastIndex, plogLastIndexZ, logLast, toPState, List.length_append]
  congr 1; push_cast; omega

/-- **The self-acknowledgement's gate on `PropLead`'s family** (`leaderGates`' `"Hgpack"`): the pinned
share after the `Replicate` lines is the idle server's of the appended state (`propK_full`); the
`SendAppendEntriesResponse` line fired (`phaseStepB_selfAck`, `fxPres_selfAck`), the share unpinned at
the outbox with the acknowledgement. -/
theorem propGate_ack (γd : GName) (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (ents : List EntryM) (Λ : Option TraceEv → Prop) (bt : Bool) (cs : List (Option ConfChangeIM))
    (htr : s.gh.tr = some γd) (hlead : s.role = .leader)
    (hnorm : ∀ e ∈ ents, e.Type' = EntryNormal)
    (hT : uint.Z s.term + 1 < traceNumBound) (hfit : receiptBound GF + γ.reBoot.length ≤ traceNumBound) :
    (ccEntsOk ents cs ∗ (propR (GF := GF) bt γ md c r id s ents Λ).Gp1 : IProp GF) ⊢
      HookGateOpt s.gh.tr r
        (sendOutGate id (propAppended s (leaderPropConf s ents cs c.joint).1) c MsgAppResp
          [selfAck id (propAppended s (leaderPropConf s ents cs c.joint).1)])
        ((propR (GF := GF) bt γ md c r id s ents Λ).Gp2
          (s.outbox ++ [selfAck id (propAppended s (leaderPropConf s ents cs c.joint).1)])) := by
  have hnc := noConf_of_normal ents hnorm
  iintro ⟨#Hcc, Hp1⟩
  icases ccEntsOk_types ents cs $$ Hcc with %hct
  have hlp : leaderPropConf s ents cs c.joint = (ents, s.pci) := propConf_noConf' _ _ _ _ ents cs hct hnc
  rw [hlp, sendOutGate_selfAck]
  dsimp only [propR]
  unfold propF
  rw [htr]
  icases Hp1 with ⟨%C0, %cs0, %P0, %hidC, Hgh, Hc⟩
  iapply hookGateOpt_fupd
  imod ownStepGhost_traceBound (GF := GF) γ md c id (proposed id s ents) hfit $$ Hgh with ⟨%Hb, Hgh⟩
  icases trCapB_logger γd γ r id c true _ _ $$ Hc with ⟨%tl, #Htl, Hc⟩
  have hrole1 : (propAppended s ents).role = .leader := hlead
  have hpl : plastIndex (toPState (propAppended s ents)) = plastIndex (toPState (proposed id s ents)) := rfl
  have hcm : (propAppended s ents).logst.committed = (proposed id s ents).logst.committed := rfl
  have hTn : uint.nat (propAppended s ents).term < traceNumBound := by
    show uint.nat s.term < traceNumBound; word
  have hcn : uint.nat (propAppended s ents).logst.committed < traceNumBound := by rw [hcm]; exact Hb.1
  have hln : uint.nat (plastIndex (toPState (propAppended s ents))) < traceNumBound := by rw [hpl]; exact Hb.2
  have hok : (selfAck id (propAppended s ents)).TrOk :=
    selfAck_trOk id _ (by word) (by rw [logLast_eq_plastIndex]; word)
  obtain ⟨ma0, hma⟩ : ∃ ma0, TraceSim.msgAbs C0 C0.length (selfAck id (propAppended s ents)) = some ma0 :=
    ⟨_, rfl⟩
  ihave Hc := trCapB_mono (some γd) γ r id c true _
    (PinAt (propAppended s ents) C0 (repCN cs0 ents.length) P0 s.outbox) (stepLastEv Λ)
    (fun C cs P h => by simp only [RepPin, propK_full] at h; exact h) $$ Hc
  ihave #Hfx := fxPres_selfAck (GF := GF) γ id
    (SendEvOf (W64 11) id (propAppended s ents) c (selfAck id (propAppended s ents))) (propAppended s ents)
    (PinAt (propAppended s ents) C0 (repCN cs0 ents.length) P0 s.outbox)
    (PinAt (propAppended s ents) C0 (repCN cs0 ents.length) (P0 ++ [ma0]) (s.outbox ++ [selfAck id (propAppended s ents)]))
    C0 ma0 hma hrole1 (fun C cs P h => ⟨h.1, h.1 ▸ hidC, h.2.2.2.1⟩)
    (pinAt_step (propAppended s ents) C0 (repCN cs0 ents.length) P0 s.outbox _ ma0)
  ihave Hfx := fxPres_upd γ id _ _ _ $$ Hfx
  imodintro
  iapply hookGateOpt_mono (some γd) r _
    iprop(trCapB (some γd) γ r id c true (PinAt (propAppended s ents) C0 (repCN cs0 ents.length) (P0 ++ [ma0])
      (s.outbox ++ [selfAck id (propAppended s ents)])) (stepLastEv Λ) ∗ emp)
  isplitl [Hgh]
  · iintro ⟨Hc, -⟩
    isplitr
    · ipureintro; simp
    iframe Hgh
    isplitl [Hc]
    · iexists true
      iapply trFam_unpin (some γd) γ r id c true _ (stepLastEv Λ) C0 (repCN cs0 ents.length) (P0 ++ [ma0])
      iexact Hc
    ipureintro
    exact outOk_snoc (outOk_self s) hok
  iapply trCapB_hookGateOpt (some γd) γ r id c tl _ true
    (PinAt (propAppended s ents) C0 (repCN cs0 ents.length) P0 s.outbox) _ (stepLastEv Λ) (stepLastEv Λ)
    iprop(emp) (phaseStepB_selfAck id c (propAppended s ents) s.outbox C0 (repCN cs0 ents.length) P0 ma0 hma hrole1)
    (fun e he => sendEvOf_notBoot he (by decide) (by decide) (by decide))
    (fun e _ => .inr rfl)
    (fun _ e he => sendEvOf_ok (W64 11) id _ c _ e _ he (by decide) hTn hcn hln (hok rfl).1 (Nat.le_refl _))
    (fun h => by cases h)
  simp only [FxPresUT]
  iframe Htl Hc Hfx

/-- **A leader's append request's phase step, pinned** (`phaseStepB_msgApp` at `PinAt`, through
`phaseStepB_send_pin`). -/
theorem phaseStepB_msgApp_pin (id : w64) (c : CfgM) (s : NState) (o : List Msg) (mm : Msg)
    (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg) (ma0 : Etcdraft.Msg)
    (hma : TraceSim.msgAbs C0 C0.length mm = some ma0)
    (hlead : s.role = .leader) (hto : mm.dst ∈ elements c.incoming)
    (happ : AppOk id (toPState s) mm) (hcommit : mm.commit = (toPState s).commit)
    (hmatch : uint.Z ((prvalsMatch s.prvals !! mm.dst).getD (W64 0)) ≤ uint.Z mm.index)
    (blt : uint.Z mm.logterm < 2 ^ 63) :
    PhaseStepB id c (SendEvOf (W64 9) id s c mm)
      (PinAt s C0 cs0 P0 o) (PinAt s C0 cs0 (P0 ++ [ma0]) (o ++ [mm])) := by
  have hsrc : mm.src = id := happ.2.1
  apply phaseStepB_send_pin id c s _ o _ C0 cs0 P0 ma0 hma hsrc
    (fun e he => ⟨he.2.1, sendEvOf_notBoot he (by decide) (by decide) (by decide)⟩)
  intro C e a he hin hout hC hR hs bt bc bl
  have hty : mm.ty = .app := happ.1
  refine ⟨(TraceSim.msgAbs C C.length mm).get (by simp [TraceSim.msgAbs, hty]), (Option.some_get _).symm, ?_⟩
  have hmo : matchOf (toPState s) mm.dst = (prvalsMatch s.prvals !! mm.dst).getD (W64 0) := by
    simp [matchOf, toPState, hlead]
  have hlen : ((toPState s).log.length : Int) < 2 ^ 63 := by
    have := plastIndex_length _ _ hs; omega
  obtain ⟨hpk, hents⟩ := appOk_slice id (toPState s) mm happ (by rw [hs.1]; rfl) hlen
  exact lineEffect_msgApp C e id s c mm a _ he hin hout hC (hin.mem_iff.1 hto) hR hs hlead hty hsrc
    happ.2.2.2.1 happ.2.2.1 hpk happ.2.2.2.2.1 hents hcommit (by rw [hmo]; exact hmatch)
    bt bc bl (by have := hpk; have : (uint.nat mm.index : Int) = uint.Z mm.index := by word
                 omega) blt

/-- **Raft's facts of a leader's log for its append requests**: its leadership of its term, its log's
records, its terms at most its term (uncompacted). -/
theorem ownStepGhost_appFacts (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState)
    (hr : s.role = .leader) (hb : (toPState s).base = base0) :
    ownStepGhost (GF := GF) γ md c id s ⊢
      (isLeader γ id s.term ∗ logRecs γ base0 (toPState s).log ∗
        ⌜∀ j x, plogTermAt (toPState s).base (toPState s).log j = some x → uint.Z x ≤ uint.Z s.term⌝) ∗
      ownStepGhost γ md c id s := by
  apply persistent_entails_right
  iintro H
  iunfold ownStepGhost at H
  icases H with ⟨Hg, -⟩
  icases ownRaftGhost_terms_le γ id (toPState s) $$ Hg with ⟨%ht, Hg⟩
  icases ownRaftGhost_logFacts γ id (toPState s) hb $$ Hg with ⟨Hg, ⟨#Hr, -, -⟩, -⟩
  ihave #Hl := ownRaftGhost_isLeader γ id (toPState s) (by rw [toPState_role, hr]; rfl) $$ Hg
  rw [show (toPState s).term = s.term from rfl]
  iframe Hl Hr
  ipureintro; exact ht

/-- **An append's gate on `PropLead`'s family** (`leaderGates`' `"#Hgpapp"`): the share pinned, the
`SendAppendEntriesRequest` line fired (`phaseStepB_msgApp_pin`, `fxPres_app` with `app_lead` and the
request's facts from raft's ghost state at the proposed state, `msgFacts_app_of_log`), the share
unpinned at the outbox with the request. -/
theorem propGate_app (γd : GName) (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (ents : List EntryM) (Λ : Option TraceEv → Prop) (bt : Bool) (cs : List (Option ConfChangeIM)) (to : w64) (mm : Msg)
    (o : List Msg) (htr : s.gh.tr = some γd) (hlead : s.role = .leader)
    (hnorm : ∀ e ∈ ents, e.Type' = EntryNormal) (hlrn : c.learners = ∅)
    (hT : uint.Z s.term + 1 < traceNumBound) (hfit : receiptBound GF + γ.reBoot.length ≤ traceNumBound)
    (hdom : to ∈ c.voters ∪ c.learners)
    (happ : AppOk id (toPState (propAppended s ents)) mm ∧ mm.commit = s.logst.committed ∧ mm.dst = to ∧
      uint.Z ((prvalsMatch s.prvals !! to).getD (W64 0)) ≤ uint.Z mm.index ∧ mm.rejecthint = W64 0) :
    (ccEntsOk ents cs ∗ (propR (GF := GF) bt γ md c r id s ents Λ).Gp2 o : IProp GF) ⊢
      HookGateOpt s.gh.tr r
        (sendOutGate id (propAppended s (leaderPropConf s ents cs c.joint).1) c MsgApp [mm])
        ((propR (GF := GF) bt γ md c r id s ents Λ).Gp2 (o ++ [mm])) := by
  have hnc := noConf_of_normal ents hnorm
  obtain ⟨hok, hcm, hdst, hmatch, hrh⟩ := happ
  iintro ⟨#Hcc, Hp2⟩
  icases ccEntsOk_types ents cs $$ Hcc with %hct
  have hlp : leaderPropConf s ents cs c.joint = (ents, s.pci) := propConf_noConf' _ _ _ _ ents cs hct hnc
  rw [hlp, sendOutGate_one id _ c MsgApp mm (W64 9) rfl]
  dsimp only [propR]
  unfold propF trFam
  rw [htr]
  icases Hp2 with ⟨%Hlen, Hgh, ⟨%b, Hf⟩, %Hok⟩
  iapply hookGateOpt_fupd
  imod ownStepGhost_traceBound (GF := GF) γ md c id (proposed id s ents) hfit $$ Hgh with ⟨%Hb, Hgh⟩
  icases trCapB_out γd γ r id c b _ _ $$ Hf with ⟨%Hout, Hf⟩
  icases trCapB_pinMem γd γ r id c b _ _ $$ Hf with ⟨%C0, %cs0, %P0, %HΦ0, Hf⟩
  icases trCapB_logger γd γ r id c b _ _ $$ Hf with ⟨%tl, #Htl, Hf⟩
  icases trCapB_pinPerm γd γ r id c b _ _ C0 (fun _ _ _ h => h.1) $$ Hf with ⟨%hperm0, Hf⟩
  obtain ⟨⟨⟨a0, -, -, hs0, -, -, bl0⟩, -⟩, hidC⟩ := HΦ0
  have hb0 : (toPState (proposed id s ents)).base = base0 := hs0.1
  have hrole1 : (propAppended s ents).role = .leader := hlead
  have hrole2 : (proposed id s ents).role = .leader := hlead
  icases ownStepGhost_appFacts γ md c id (proposed id s ents) hrole2 hb0 $$ Hgh with ⟨⟨#Hil, #Hrc, %Htle⟩, Hgh⟩
  have hlogeq : (toPState (proposed id s ents)).log = (toPState (propAppended s ents)).log := rfl
  have hbeq : (toPState (proposed id s ents)).base = (toPState (propAppended s ents)).base := rfl
  have htm : (proposed id s ents).term = s.term := rfl
  have hb : traceNumBound = 2 ^ 61 := rfl
  have hloglen : ((toPState (propAppended s ents)).log.length : Int) < 2 ^ 63 := by
    have := plastIndex_length _ _ hs0; omega
  obtain ⟨hpk, hents⟩ := appOk_slice id (toPState (propAppended s ents)) mm hok (by rw [hs0.1]; rfl) hloglen
  have hlt := hok.2.2.2.2.1
  have hlogterm : uint.Z mm.logterm ≤ uint.Z s.term := by
    rw [← htm]; exact Htle _ _ (by rw [hlogeq, hbeq]; exact hlt)
  have hpl : plastIndex (toPState (propAppended s ents)) = plastIndex (toPState (proposed id s ents)) := rfl
  have hTn : uint.nat (propAppended s ents).term < traceNumBound := by
    show uint.nat s.term < traceNumBound; word
  have hcn : uint.nat (propAppended s ents).logst.committed < traceNumBound := Hb.1
  have hln : uint.nat (plastIndex (toPState (propAppended s ents))) < traceNumBound := by rw [hpl]; exact Hb.2
  have hbI : (traceNumBound : Int) = 2 ^ 61 := by rw [hb]; exact Int.natCast_pow 2 61
  have hlenL : (toPState (propAppended s ents)).log.length < traceNumBound := by
    have h2 := Hb.2
    rw [← hpl] at h2
    have h3 := plastIndex_length _ _ hs0
    have : uint.Z (plastIndex (toPState (propAppended s ents))) < traceNumBound := by word
    omega
  have hnums : mm.NumsBelow traceNumBound := by
    refine ⟨?_, by omega, ?_, ?_, ?_, ?_⟩
    · rw [hok.2.2.1]; show uint.nat s.term < traceNumBound; word
    · have : uint.Z mm.logterm < traceNumBound := by omega
      word
    · have : uint.nat mm.index ≤ (toPState (propAppended s ents)).log.length := by omega
      omega
    · rw [hcm]; exact Hb.1
    · rw [hrh]; show 0 < traceNumBound; rw [hb]; omega
  have htrok : mm.TrOk := Msg.trOk_of_nums (by rw [hok.1]; decide) (by rw [hok.1]; decide) (fun _ => hnums)
  obtain ⟨ma0, hma⟩ : ∃ ma0, TraceSim.msgAbs C0 C0.length mm = some ma0 := by
    simp [TraceSim.msgAbs, hok.1]
  have hto : mm.dst ∈ elements c.incoming := by rw [hdst]; exact mem_incoming_of c to hlrn Hout hdom
  have hpt : ma0.type = .appendEntriesRequest := by simp [TraceSim.msgAbs, hok.1] at hma; rw [← hma]
  have hps : ma0.subtype = "app" := by simp [TraceSim.msgAbs, hok.1] at hma; rw [← hma]
  have hsrc : ma0.source = idAbs id := by
    simp [TraceSim.msgAbs, hok.1] at hma; rw [← hma]; simp [hok.2.1]
  ihave Hfx := fxPres_app (GF := GF) γ id (SendEvOf (W64 9) id (propAppended s ents) c mm)
    (PinAt (propAppended s ents) C0 cs0 P0 o) (PinAt (propAppended s ents) C0 cs0 (P0 ++ [ma0]) (o ++ [mm]))
    ma0 (msgAbs_canon C0 C0.length mm ma0 hma) hpt hps hsrc
    (fun C cs P h => h.1 ▸ hidC)
    (fun C _ _ h => by rw [msgAbs_dest hma, h.1]; exact (mem_confAbs C0 mm.dst).2 (hperm0.mem_iff.1 hto))
    (app_lead (propAppended s ents) C0 cs0 P0 o id mm ma0 hma hrole1 hok hcm)
    (pinAt_step (propAppended s ents) C0 cs0 P0 o mm ma0) $$ []
  · imodintro
    iintro %C %cs %P %h
    obtain ⟨rfl, -⟩ := h
    iapply msgFacts_app_of_log γ C id (toPState (propAppended s ents)) mm ma0 hma hok hs0.1
      (by have := hs0.2.1; rw [hs0.1] at this; exact this) hloglen
    rw [← hlogeq, show (toPState (propAppended s ents)).term = (proposed id s ents).term from rfl]
    iframe Hil Hrc
  ihave Hfx := fxPres_upd γ id _ _ _ $$ Hfx
  imodintro
  iapply hookGateOpt_mono (some γd) r _
    iprop(trCapB (some γd) γ r id c true (PinAt (propAppended s ents) C0 cs0 (P0 ++ [ma0]) (o ++ [mm]))
      (stepLastEv Λ) ∗ emp)
  isplitl [Hgh]
  · iintro ⟨Hc, -⟩
    isplitr
    · ipureintro; simp only [List.length_append, List.length_singleton]; omega
    iframe Hgh
    isplitl [Hc]
    · iexists true
      iapply trCapB_mono (some γd) γ r id c true _ _ _ (fun _ _ _ h => h.2.2.2) $$ Hc
    ipureintro
    exact outOk_snoc Hok htrok
  iapply trCapB_hookGateOpt (some γd) γ r id c tl _ b (PinAt (propAppended s ents) C0 cs0 P0 o) _
    (stepLastEv Λ) (stepLastEv Λ) iprop(emp)
    (phaseStepB_msgApp_pin id c (propAppended s ents) o mm C0 cs0 P0 ma0 hma hrole1 hto hok hcm
      (by rw [hdst]; exact hmatch) (by omega))
    (fun e he => sendEvOf_notBoot he (by decide) (by decide) (by decide))
    (fun e _ => .inr rfl)
    (fun _ e he => sendEvOf_ok (W64 9) id _ c _ e _ he (by decide) hTn hcn hln hnums (Nat.le_refl _))
    (fun h => by cases h)
  simp only [FxPresUT]
  iframe Htl Hf Hfx

/-- **`PropLead`'s close**: by the outbox's length (`G0`/`G1` at `s`'s, `Gp2` at a longer one) against
`StepEnd`'s two outcomes (`propLead_end`): dropped, raft's ghost state back at `s` (`CloseAt`: the batch
not appended, `proposed_logst_ne'`) and the idle capability at the end state (`lineF_close`); appended,
the ghost state at the proposed state (`CloseMid`) and the capability from the appended state's family
(`trFam_idle`: the idle relation reads neither the outbox nor the `Progress` values beyond `Match`). -/
theorem propClose (γd : GName) (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (m : MessageM) (ents : List EntryM) (ctx : List w8) (Λ : Option TraceEv → Prop) (bt : Bool)
    (htr : s.gh.tr = some γd) (hp : PropLead γ ents s m) (hT0 : m.Term' = W64 0) :
    ⊢ stepClose (GF := GF) γ md c id m ents ctx s (propR bt γ md c r id s ents Λ)
        (fun s' => iprop(∃ bt' : Bool, trCapB s.gh.tr γ r id c bt' (fun C => SimIdle C s') (stepLastEv Λ))) := by
  iunfold stepClose
  iintro %s' %B %recv %_ %hend %_ Hout
  have hE := propLead_end (c := c) (id := id) (ctx := ctx) hp hT0 (hend (by rw [htr]; rfl))
  have hlong : ∀ (ms : List Msg) (pvs : GMap w64 Progress),
      s.outbox.length < ({ sendMsgs (proposed id s ents) ms with prvals := pvs } : NState).outbox.length := by
    intro ms pvs; simp [proposed, sendMsgs]
  ihave Hout := stepOutG_stepOut c m s _ $$ Hout
  unfold stepOut
  dsimp only [propR]
  icases Hout with (⟨%ho, H⟩ | ⟨%ho, H⟩ | %hf | ⟨%hlen, H⟩ | ⟨%b, %N, %hf⟩)
  · rcases hE with ⟨hl, -, hS⟩ | ⟨ms, pvs, rfl, -⟩
    · imod lineF_close γ md c r id s s' (stepLastEv Λ) hS $$ H with ⟨Hgh, Hc, %Hot⟩
      imodintro
      isplitl [Hgh]
      · ileft; iframe Hgh; ipureintro; intro _ _ _ _; rw [hl]; exact proposed_logst_ne' id s ents hp.2.2.1
      iframe Hc; ipureintro; exact Hot
    · exfalso; have := hlong ms pvs; rw [ho] at this; omega
  · rcases hE with ⟨hl, -, hS⟩ | ⟨ms, pvs, rfl, -⟩
    · imod lineF_close γ md c r id s s' (stepLastEv Λ) hS $$ H with ⟨Hgh, Hc, %Hot⟩
      imodintro
      isplitl [Hgh]
      · ileft; iframe Hgh; ipureintro; intro _ _ _ _; rw [hl]; exact proposed_logst_ne' id s ents hp.2.2.1
      iframe Hc; ipureintro; exact Hot
    · exfalso; have := hlong ms pvs; rw [ho] at this; omega
  · exact hf.elim
  · rcases hE with ⟨-, hob, -⟩ | ⟨ms, pvs, rfl, hm⟩
    · exfalso; rw [hob] at hlen; omega
    · unfold propF
      icases H with ⟨Hgh, ⟨%b, Hf⟩, %Hok⟩
      have hS : ∀ C, SimIdleS C (propAppended s ents) =
          SimIdleS C ({ sendMsgs (proposed id s ents) ms with prvals := pvs } : NState) := fun C =>
        (simIdleS_prvals C (proposed id s ents) ms pvs hm).symm
      imod trFam_idle s.gh.tr γ r id c b (propAppended s ents) _ (stepLastEv Λ) hS $$ Hf with Hc
      imodintro
      isplitl [Hgh]
      · iright
        iexists proposed id s ents
        iframe Hgh
        ipureintro
        exact CloseMid.prop ⟨hp.1, hp.2.1, noConf_of_normal ents hp.2.2.2.1, rfl, rfl⟩
      isplitl [Hc]
      · iexists b; iexact Hc
      ipureintro; exact outTrStep_of_outOk Hok
  · exact hf.elim

end families

section bundle
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **`stepBundle_traced.on` with a path that reads the cluster's names and the batch** (`PropLead`'s:
a batch of normal entries, a cluster with a bootstrap log). The premises and the conclusion are
`stepBundle_traced.on`'s verbatim (as `stepBundle_traced.onC`'s). -/
abbrev stepBundle_traced.onG (Path : RaftNames → List EntryM → NState → MessageM → Prop) : Prop :=
  ∀ (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState) (m : MessageM)
    (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc) (γd : GName)
    (Λ : Option TraceEv → Prop) (bt : Bool),
  Path γ ents s m →
  s.gh.tr = some γd →
  s.prevote = false → s.cq = false → StepEndTy m.Type' → NStateWf s →
  (m.Type' = MsgHup ∨ m.Type' = MsgBeat ∨ m.Type' = MsgProp → m.Term' = W64 0) →
  (m.Type' = MsgHup → s.role ≠ .leader) →
  (∀ ty, mtypeOf m.Type' = some ty → ty.traced = true → m.To' = id) →
  uint.Z s.term + 1 < traceNumBound → uint.Z m.Term' < traceNumBound →
  (∀ ty, mtypeOf m.Type' = some ty → MsgTrOk γ (absMsg ty m ents ctx)) →
  receiptBound GF + γ.reBoot.length ≤ traceNumBound →
  c.learners = ∅ → domSet s.progress ⊆ c.voters ∪ c.learners →
  s.role ≠ .preCandidate → TrRecvShape m ents →
  (m.Type' = MsgHeartbeat ∨ m.Type' = MsgApp → γ.reBoot ≠ []) →
  (trCapB s.gh.tr γ r id c bt (fun C => SimIdle C s) Λ ∗
      (recvTokOf γd m ents ctx ∗
        □ (∀ ty : MsgType, ⌜mtypeOf m.Type' = some ty ∧ ty.traced = true⌝ -∗
          isMessageC γ (absMsg ty m ents ctx))) ∗
      TrNoSnap s.gh.tr s.logst : IProp GF) ⊢
    |={⊤}=> ∃ R : StepG GF, R.G ∗ stepGates c r id s m ents sn ctx rs (ghostIn γ md c id s R) ∗
      stepClose γ md c id m ents ctx s R
        (fun s' => iprop(∃ bt' : Bool, trCapB s.gh.tr γ r id c bt' (fun C => SimIdle C s') (stepLastEv Λ)))

/-- A path that reads neither the names nor the batch. -/
theorem stepBundle_traced.on_of_onG {Path : NState → MessageM → Prop}
    (h : stepBundle_traced.onG (GF := GF) (hG := hG) (fun _ _ => Path)) :
    stepBundle_traced.on (GF := GF) (hG := hG) Path := h

/-- **`raft.Step`'s traced bundle on `MsgProp` at a leader** (see the header). -/
theorem stepBundle_traced_prop : stepBundle_traced.onG (GF := GF) (hG := hG) PropLead := by
  intro γ md c r id s m ents sn ctx rs γd Λ bt hp htr hpv hcq hty hwf hloc hhup hto hT hmT hok hfit hlrn hsub _ _ _
  have hT0 : m.Term' = W64 0 := hloc (.inr (.inr hp.1))
  have hnbf : ¬ PreBF m s := by
    unfold PreBF; rw [hT0]; intro h; have := h.1; simp at this
  have hpre : ∀ pvs, preState s m pvs = s := fun pvs => by simp [preState, hnbf]
  have hsome : s.gh.tr ≠ none := by rw [htr]; simp
  have nB : m.Type' ≠ MsgBeat := by rw [hp.1]; simp only [MsgProp, MsgBeat, ne_eq]; exact of_decide_eq_true rfl
  have nRI : m.Type' ≠ MsgReadIndex := by
    rw [hp.1]; simp only [MsgProp, MsgReadIndex, ne_eq]; exact of_decide_eq_true rfl
  have nTL : m.Type' ≠ MsgTransferLeader := by
    rw [hp.1]; simp only [MsgProp, MsgTransferLeader, ne_eq]; exact of_decide_eq_true rfl
  have nCQ : m.Type' ≠ MsgCheckQuorum := by
    rw [hp.1]; simp only [MsgProp, MsgCheckQuorum, ne_eq]; exact of_decide_eq_true rfl
  have nHR : m.Type' ≠ MsgHeartbeatResp := by
    rw [hp.1]; simp only [MsgProp, MsgHeartbeatResp, ne_eq]; exact of_decide_eq_true rfl
  have nAR : m.Type' ≠ MsgAppResp := by
    rw [hp.1]; simp only [MsgProp, MsgAppResp, ne_eq]; exact of_decide_eq_true rfl
  have nH : m.Type' ≠ MsgHup := by rw [hp.1]; exact msgProp_ne_hup
  have nV : m.Type' ≠ MsgVote := by rw [hp.1]; exact msgProp_ne_vote
  have nPV : m.Type' ≠ MsgPreVote := by
    rw [hp.1]; simp only [MsgProp, MsgPreVote, ne_eq]; exact of_decide_eq_true rfl
  iintro ⟨Hcap, -, #Hnosnap⟩
  imodintro
  iexists propR bt γ md c r id s ents Λ
  isplitl [Hcap]
  · dsimp only [propR]; iexact Hcap
  isplitr
  · iunfold stepGates
    dsimp only [ghostIn, propR]
    isplitr
    · -- the receive hook: no line for `MsgProp`
      iintro ⟨Hgh, Hc⟩
      have hrg : recvGate id s c ⟨m, ents, sn, ctx, rs⟩ = none := by
        apply recvGate_none_of
        intro ty hty'
        have hm2 : mtypeOf MsgProp = some .propose := rfl
        simp only [hp.1, hm2] at hty'
        cases hty'; rfl
      rw [hrg]
      iapply hookGateOpt_mono s.gh.tr r none
        (lineF γ md c r id s (fun C => SimIdleS C s) (stepLastEv Λ) s.outbox)
      isplitr
      · iintro H; iframe H; ipureintro; rfl
      iapply lineF_recv γd γ md c r id s Λ bt htr
      iframe Hgh Hc
    isplitr
    · unfold preGate
      iintro %_ HG0
      rw [if_neg hnbf]
      imodintro
      iexact HG0
    isplitr
    · iintro %h; exact (h.1 hT0).elim
    isplitr
    · iintro %h
      exact (h.elim nV nPV).elim
    isplitr
    · iintro %h; exact (nH h).elim
    isplitr
    · unfold stepFnGates
      iintro %pvs
      rw [hpre pvs]
      dsimp only
      isplit
      · iintro %hr; rw [hp.2.1] at hr; cases hr
      isplit
      · iintro %hr; rcases hr with hr | hr <;> rw [hp.2.1] at hr <;> cases hr
      · iintro %_
        unfold leaderGates
        isplitr
        · imodintro; iintro %h; exact (nB h).elim
        isplitr
        · iintro %h; exact (nRI h).elim
        isplitr
        · imodintro; iintro %h; exact (nRI h).elim
        isplitr
        · iintro %h; exact (nTL h).elim
        isplitr
        · iintro %h; exact (nTL h).elim
        isplitr
        · iexact Hnosnap
        isplitr
        · iintro %h; exact (nCQ h).elim
        isplitr
        · -- the `Replicate` lines
          iintro %_ %cs #Hcc HTp ⟨%_, Hlf⟩
          have h := propGate_rep (GF := GF) γd γ md c r id s ents Λ bt cs htr hp.2.1 hp.2.2.1 hp.2.2.2.1
            hp.2.2.2.2 hT hfit
          dsimp only [propR] at h
          iapply h
          iframe Hcc HTp Hlf
        isplitr
        · -- the self-acknowledgement
          iintro %_ %cs #Hcc HG
          have h := propGate_ack (GF := GF) γd γ md c r id s ents Λ bt cs htr hp.2.1 hp.2.2.2.1 hT hfit
          dsimp only [propR] at h
          dsimp only
          iapply h
          iframe Hcc HG
        isplitr
        · -- the appends
          imodintro
          iintro %_ %cs %to %mm %o #Hcc %Hto %Happ HG
          icases ccEntsOk_types ents cs $$ Hcc with %hct
          have hlp : leaderPropConf s ents cs c.joint = (ents, s.pci) :=
            propConf_noConf' _ _ _ _ ents cs hct (noConf_of_normal ents hp.2.2.2.1)
          rw [hlp] at Happ
          have h := propGate_app (GF := GF) γd γ md c r id s ents Λ bt cs to mm o htr hp.2.1 hp.2.2.2.1 hlrn
            hT hfit ((GMap.elem_of_subseteq _ _).1 hsub _ Hto.2) Happ
          dsimp only [propR] at h
          dsimp only
          iapply h
          iframe Hcc HG
        isplitr
        · iintro %h; exact (h.elim nHR (fun h => nAR h.1)).elim
        isplitr
        · imodintro; iintro %h; exact (nHR h).elim
        isplitr
        · iintro %h; exact (nAR h.1).elim
        isplitr
        · imodintro; iintro %h; exact (nAR h.1).elim
        isplitr
        · imodintro; iintro %h; exact (nAR h.1).elim
        isplitr
        · imodintro; iintro %h; exact (nAR h.1).elim
        · imodintro; iintro %h; exact (nAR h.1).elim
    · ipureintro
      exact ⟨PermInv.const _, IdxFree.of_some _ hsome, IdxFree.of_some _ hsome,
        IdxFree.of_some _ hsome, fun _ _ => IdxFree.of_some _ hsome⟩
  · iapply propClose γd γ md c r id s m ents ctx Λ bt htr hp hT0

end bundle

end EtcdGrove
end Perennial
