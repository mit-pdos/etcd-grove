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
variable [GooseExts]

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
    (ents : List EntryM) (Λ : Option TraceEv → Prop) (cs : List (Option ConfChangeIM))
    (htr : s.gh.tr = some γd) (hlead : s.role = .leader) (hne : ents ≠ [])
    (hnorm : ∀ e ∈ ents, e.Type' = EntryNormal) (hboot : γ.reBoot ≠ [])
    (hT : uint.Z s.term + 1 < traceNumBound) (hfit : receiptBound GF + γ.reBoot.length ≤ traceNumBound) :
    (ccEntsOk ents cs ∗ propLend γ s ents ∗
        lineF γ md c r id s (fun C => SimIdleS C s) (stepLastEv Λ) s.outbox : IProp GF) ⊢
      HookGateN s.gh.tr r (NodeEvOf (W64 5) id s c) (normalCount (leaderPropConf s ents cs c.joint).1)
        (propR (GF := GF) true γ md c r id s ents Λ).Gp1 := by
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
    (ents : List EntryM) (Λ : Option TraceEv → Prop) (cs : List (Option ConfChangeIM))
    (htr : s.gh.tr = some γd) (hlead : s.role = .leader)
    (hnorm : ∀ e ∈ ents, e.Type' = EntryNormal)
    (hT : uint.Z s.term + 1 < traceNumBound) (hfit : receiptBound GF + γ.reBoot.length ≤ traceNumBound) :
    (ccEntsOk ents cs ∗ (propR (GF := GF) true γ md c r id s ents Λ).Gp1 : IProp GF) ⊢
      HookGateOpt s.gh.tr r
        (sendOutGate id (propAppended s (leaderPropConf s ents cs c.joint).1) c MsgAppResp
          [selfAck id (propAppended s (leaderPropConf s ents cs c.joint).1)])
        ((propR (GF := GF) true γ md c r id s ents Λ).Gp2
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

end families

end EtcdGrove
end Perennial
