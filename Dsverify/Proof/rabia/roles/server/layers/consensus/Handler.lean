/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/layers/consensus/Handler.lean`, run `rabia-r1wake-1`.)

The proof of the message handler (`MsgHandler`, `binConMsgHandling`): the handler's state between
messages, its witnesses of the messages it processed (the per-sender order), and the counting.
-/
module

public import Dsverify.Proof.rabia.roles.server.layers.consensus.HandlerSlot
public import Dsverify.Proof.rabia.roles.server.layers.consensus.Helpers

@[expose] public section

noncomputable section

namespace Perennial.rabia.roles.server.layers.consensus

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model NetConn Dsv rabia.internal.message
  rabia.internal.config rabia.internal.ledger rabia rabia.internal.queue

set_option linter.unusedSectionVars false

/-- Discharge the bounds check of an `IndexRef`. -/
local macro "slice_index_if" : tactic =>
  `(tactic| (rw [ite_eq_left_of_eq_true _ _ (eq_true (by constructor <;> word))]))

set_option hygiene false in
/-- Load `c.Ledger[slot]` (the binConMsgHandling proof's names). -/
local macro "ledger_load" : tactic =>
  `(tactic| ((try wp_auto); (try rw [hmod]); rw [if_pos (show 0 ≤ sint.Z (W64 (uint.Z ov.SvrSeq')) ∧ sint.Z (W64 (uint.Z ov.SvrSeq')) < sint.Z ledger.len by constructor <;> word)]; wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z ov.SvrSeq'))) _ _ e.loc (by word) $$ [Hsl]; (iframe Hsl; ipureintro; rw [show (sint.Z (W64 (uint.Z ov.SvrSeq'))).toNat = o.svrSeq.toNat by rw [hof.2.2.1]; word]; simp [he]); iintro -; wp_auto))


section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable {cf : RCfg}
variable [package_sem : rabia.roles.server.layers.consensus.Assumptions]

theorem bmsgOk_obj (γ : Names) (X : Nat) (m : MsgV)
    (hty : m.ty = tyProposal ∨ m.ty = tyState ∨ m.ty = tyVote ∨ m.ty = tyDecision) :
    bmsgOk (GF := GF) γ cf X m ⊢ ⌜∃ o, m.obj = some o⌝ := by
  unfold bmsgOk
  rcases hty with h|h|h|h
  · simp only [h, show tyProposal ≠ tyClientRequest by decide, ↓reduceIte]
    iintro ⟨%o, %h1, -⟩; ipureintro; exact ⟨o, h1.1⟩
  · simp only [h, show tyState ≠ tyClientRequest by decide, show tyState ≠ tyProposal by decide,
      ↓reduceIte]
    iintro ⟨%o, %h1, -⟩; ipureintro; exact ⟨o, h1.1⟩
  · simp only [h, show tyVote ≠ tyClientRequest by decide, show tyVote ≠ tyProposal by decide,
      show tyVote ≠ tyState by decide, ↓reduceIte]
    iintro ⟨%o, %h1, -⟩; ipureintro; exact ⟨o, h1.1⟩
  · simp only [h, show tyDecision ≠ tyClientRequest by decide,
      show tyDecision ≠ tyProposal by decide, show tyDecision ≠ tyState by decide,
      show tyDecision ≠ tyVote by decide, show tyDecision ≠ tyProposalRequest by decide, ↓reduceIte]
    iintro ⟨%o, %d, %h1, -⟩; ipureintro; exact ⟨o, h1⟩

theorem msgWit_big (γl : SrvNames) (γc : ConsNames) (X : Nat) (m : MsgV) (o : ObjV)
    (ho : m.obj = some o) (hb : ¬ o.svrSeq.toNat < lenLedger) :
    ⊢ msgWit (GF := GF) γl γc X m := by
  unfold msgWit msgRound
  rw [ho]
  cases roundOf m with
  | none => simp only [Option.map_none]; iintro; itrivial
  | some r => simp only [Option.map_some, Option.getD_some, hb, ↓reduceIte]; iintro; itrivial

/-- `prevWit` once the slot is known not done. -/
def prevC (γl : SrvNames) (γc : ConsNames) (X : Nat) (m : MsgV) : IProp GF :=
  match msgRound m with
  | some (s, ρ + 1) => if s < lenLedger then iprop(counted γl γc s ρ X ∨ notified γc s ρ)
      else iprop(True)
  | _ => iprop(True)

instance prevC_persistent (γl : SrvNames) (γc : ConsNames) (X : Nat) (m : MsgV) :
    Persistent (prevC (GF := GF) γl γc X m) := by
  unfold prevC; split
  · split <;> infer_instance
  · infer_instance

/-- `GetIsDone`'s step for the handler's message `m` of slot `s`. -/
theorem hstep_isDone (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (s : Nat)
    (X : Nat) (m : MsgV) (hm : ∀ s' r, msgRound m = some (s', r) → s' = s) (st : SlotSt) :
    prevWit (GF := GF) γl γc X m ∗ slotGhost γ cf k γl γc s st ⊢
      |==> (slotGhost γ cf k γl γc s st ∗
        (if st.isDone then doneW γl γc s else prevC γl γc X m)) := by
  iintro ⟨#Hp, Hg⟩
  imod gs_isDone γ k γl γc s st $$ Hg with ⟨Hg, Hw⟩
  cases hd : st.isDone with
  | true => simp only [hd, ↓reduceIte]; imodintro; iframe
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold prevWit prevC doneOr
    cases hr : msgRound m with
    | none => imodintro; iframe
    | some sr =>
      obtain ⟨s', r⟩ := sr
      have := hm s' r hr; subst this
      cases r with
      | zero => imodintro; iframe
      | succ ρ =>
        simp only
        split
        · icases Hp with (#H | #H | #H)
          · imodintro; iframe; ileft; iexact H
          · imodintro; iframe; iright; iexact H
          · iexfalso; iapply gs_notDone γ k γl γc s' st hd $$ [Hg]; iframe; iexact H
        · imodintro; iframe

theorem msgWit_doneW (γl : SrvNames) (γc : ConsNames) (X : Nat) (m : MsgV) (s : Nat)
    (hm : ∀ s' r, msgRound m = some (s', r) → s' = s) :
    doneW (GF := GF) γl γc s ⊢ msgWit γl γc X m := by
  iintro #H
  unfold msgWit
  cases hr : msgRound m with
  | none => itrivial
  | some sr =>
    obtain ⟨s', r⟩ := sr
    have := hm s' r hr; subst this
    simp only
    split
    · unfold doneOr; iright; iright; iexact H
    · itrivial

/-- A step that only reads the agreement of the halves. -/
theorem hstep_agree (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (s : Nat)
    (ents : List Ent) (ql : List (Option Nat)) (p : Option (Option Nat)) (E : CoPset) (st : SlotSt) :
    ⊢ slotGhost (GF := GF) γ cf k γl γc s st -∗ hHalves γl γc s ents ql p ={E}=∗
      slotGhost γ cf k γl γc s st ∗ (hHalves γl γc s ents ql p ∗
        ⌜∃ exd dl rl, SlotOk cf s st ents ql p exd dl rl⌝) := by
  iintro Hg Hh
  ihave ⟨%h, Hg, Hh⟩ := gs_agree γ k γl γc s st ents ql p $$ [Hg Hh]
  · iframe
  imodintro
  iframe
  ipureintro; exact h

theorem cf_n_le {cf : RCfg} (hc : cf.Ok) : cf.n ≤ maxS := by
  unfold RCfg.Ok at hc; unfold maxS; omega

theorem cf_q_pos {cf : RCfg} (hc : cf.Ok) : 0 < cf.q ∧ cf.q ≤ cf.n := by
  unfold RCfg.Ok at hc; unfold RCfg.q; omega

theorem pure_before {s : Nat} {st : SlotSt} {ents : List Ent} {ql : List (Option Nat)}
    {exd : Bool} {dl rl : List Unit} (hc : cf.Ok) (h : SlotOk cf s st ents ql none exd dl rl)
    {p r : Nat} (hr : r = 1 ∨ r = 2) :
    (st.total p r ≥ cf.q → some (2 * p + r - 1) ∈ ql) ∧
    (¬ st.total p r ≥ cf.q → (tally ents (2 * p + r - 1)).length < cf.q) ∧
    st.total p r + 1 < 2 ^ 62 := by
  have ht := h.1.total (p := p) hr
  have hle := (h.2.2.1 (2 * p + r - 1)).1
  have hq := cf_q_pos hc
  have hn := cf_n_le hc
  unfold maxS at hn
  refine ⟨fun hge => ?_, fun hlt => by omega, by omega⟩
  have h2 : (tally ents (2 * p + r - 1)).length = cf.q := by omega
  rcases (h.2.2.2.2.1 _).2 h2 with h3 | h3
  · exact h3
  · cases h3

theorem pure_after {s : Nat} {st : SlotSt} {ents : List Ent} {ql : List (Option Nat)}
    {pd : Option (Option Nat)} {exd : Bool} {dl rl : List Unit}
    (h : SlotOk cf s st ents ql pd exd dl rl) {p r : Nat} (hr : r = 1 ∨ r = 2) :
    st.total p r ≥ cf.q ↔ (tally ents (2 * p + r - 1)).length = cf.q := by
  have ht := h.1.total (p := p) hr
  have hle := (h.2.2.1 (2 * p + r - 1)).1
  omega

theorem mk_slotQPx_round (γ : Names) (γc : ConsNames) (s : Nat) (ql : List (Option Nat))
    (ρ : Nat) (v : Msg) (m' : MsgV) (hr : roundOf m' = some ρ)
    (hfm : ql.filterMap id = List.range ρ) (hwf : notifWf v) :
    qLb (GF := GF) γc s (ql ++ [some ρ]) ∗ roundDone γc s ρ ∗ msgRep v m' ⊢
      slotQPx γ cf γc s (ql.length : Int) v := by
  iintro ⟨#Hq, #Hd, #Hm⟩
  unfold slotQPx slotQP
  isplitl
  · iexists m', ql ++ [some ρ], some ρ
    iframe Hm Hq
    isplitr
    · ipureintro; simp
    simp only
    iframe Hd
    ipureintro
    refine ⟨hr, ?_⟩
    simp [hfm]
  · ipureintro; exact hwf

theorem msgWit_of (γl : SrvNames) (γc : ConsNames) (X : Nat) (m : MsgV) (s ρ : Nat)
    (h : msgRound m = some (s, ρ)) (hs : s < lenLedger) :
    doneOr (GF := GF) γl γc s ρ X ⊢ msgWit γl γc X m := by
  unfold msgWit; rw [h]; simp only [hs, ↓reduceIte]; iintro H; iexact H

theorem hslots_restore (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : SlotV)
    (he : γl.slots[s]? = some e) :
    (∀ y, hSlot (GF := GF) γl γc s -∗ [∗list] k ↦ _x ∈ γl.slots.set s y, hSlot γl γc k) ∗
      hSlot γl γc s ⊢ [∗list] k ↦ _x ∈ γl.slots, hSlot γl γc k := by
  iintro ⟨H, Hs⟩
  have hset : γl.slots.set s e = γl.slots := by
    obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp he
    rw [← heq]; exact List.set_getElem_self hlt
  ihave H2 := H $$ %e Hs
  rw [hset]
  iexact H2

theorem valid_st_bit {M : Facts} (hM : Valid M) {X s p : Nat} {v : FVal}
    (h : M (.st X s p) = some v) : ∃ b, v = .bit b ∧ b ≤ 1 := by
  unfold Valid at hM
  split at hM
  · have := hM.2.1 _ _ h
    cases v <;> simp [Justified] at this
    exact ⟨_, rfl, this.2⟩
  · rw [hM] at h; cases h

theorem valid_vt_bit {M : Facts} (hM : Valid M) {X s p : Nat} {v : FVal}
    (h : M (.vt X s p) = some v) : ∃ b, v = .bit b ∧ b ≤ 2 := by
  unfold Valid at hM
  split at hM
  · have := hM.2.1 _ _ h
    cases v <;> simp [Justified] at this
    exact ⟨_, rfl, this.2⟩
  · rw [hM] at h; cases h

theorem bmsg_bound (γ : Names) (X : Nat) (m : MsgV) (hty : m.ty = tyState ∨ m.ty = tyVote) :
    shared (GF := GF) γ ∗ bmsgOk γ cf X m ⊢
      |={⊤}=> ⌜m.value.toNat ≤ 2 ∧ (m.ty = tyState → 1 ≤ m.phase.toNat)⌝ := by
  iintro ⟨#Hsh, #Hok⟩
  unfold shared
  icases Hsh with ⟨#Hr, -, -, -⟩
  unfold bmsgOk
  rcases hty with h | h
  · simp only [h, show tyState ≠ tyClientRequest by decide, show tyState ≠ tyProposal by decide,
      ↓reduceIte]
    icases Hok with ⟨%o', %h1, #Hf⟩
    imod facts_valid γ.rab ⊤ (fun _ _ => CoPset.mem_full)
      [(FKey.st X o'.svrSeq.toNat m.phase.toNat, FVal.bit m.value.toNat)] $$ [Hr Hf] with %hv
    · isplitr
      · iexact Hr
      · iapply (BigSepL.bigSepL_singleton
          (Φ := fun _ (kv : FKey × FVal) => fact (GF := GF) γ.rab kv.1 kv.2)).2
        iexact Hf
    obtain ⟨M, hM, hS⟩ := hv
    obtain ⟨b, hb, hb1⟩ := valid_st_bit hM (hS _ (List.mem_singleton_self _))
    cases hb
    imodintro; ipureintro
    exact ⟨by omega, fun _ => h1.2.1⟩
  · simp only [h, show tyVote ≠ tyClientRequest by decide, show tyVote ≠ tyProposal by decide,
      show tyVote ≠ tyState by decide, ↓reduceIte]
    icases Hok with ⟨%o', %h1, #Hf⟩
    imod facts_valid γ.rab ⊤ (fun _ _ => CoPset.mem_full)
      [(FKey.vt X o'.svrSeq.toNat m.phase.toNat, FVal.bit m.value.toNat)] $$ [Hr Hf] with %hv
    · isplitr
      · iexact Hr
      · iapply (BigSepL.bigSepL_singleton
          (Φ := fun _ (kv : FKey × FVal) => fact (GF := GF) γ.rab kv.1 kv.2)).2
        iexact Hf
    obtain ⟨M, hM, hS⟩ := hv
    obtain ⟨b, hb, hb1⟩ := valid_vt_bit hM (hS _ (List.mem_singleton_self _))
    cases hb
    imodintro; ipureintro
    exact ⟨hb1, fun h' => by simp_all⟩

theorem bmsg_dec (γ : Names) (X : Nat) (m : MsgV) (hty : m.ty = tyDecision) :
    bmsgOk (GF := GF) γ cf X m ⊢ ∃ (o : ObjV) (d : DVal), ⌜m.obj = some o⌝ ∗
      fact γ.rab (.dec o.svrSeq.toNat) (.dval d) ∗ decObjOk γ cf o.svrSeq.toNat d o := by
  unfold bmsgOk
  simp only [hty, show tyDecision ≠ tyClientRequest by decide,
    show tyDecision ≠ tyProposal by decide, show tyDecision ≠ tyState by decide,
    show tyDecision ≠ tyVote by decide, show tyDecision ≠ tyProposalRequest by decide, ↓reduceIte]
  iintro H; iexact H

theorem mk_slotQPx_dec (γ : Names) (γc : ConsNames) (s : Nat) (ql : List (Option Nat))
    (v : Msg) (m : MsgV) (o : ObjV) (d : DVal) (hty : m.ty = tyDecision) (ho : m.obj = some o)
    (hs : o.svrSeq.toNat = s) (hnot : none ∉ ql) (hwf : notifWf v) :
    qLb (GF := GF) γc s (ql ++ [none]) ∗ msgRep v m ∗ fact γ.rab (.dec s) (.dval d) ∗
      decObjOk γ cf s d o ⊢ slotQPx γ cf γc s (ql.length : Int) v := by
  iintro ⟨#Hq, #Hm, #Hf, #Hd⟩
  unfold slotQPx slotQP
  isplitl
  · iexists m, ql ++ [none], none
    iframe Hm Hq
    isplitr
    · ipureintro; simp
    simp only
    iexists o, d
    iframe Hf Hd
    ipureintro
    exact ⟨hty, ho, hs, by simpa using hnot⟩
  · ipureintro; exact hwf

theorem wp_GetIsDone_t (hGID : Slot.GetIsDone.spec (GF := GF)) (γ : Names) (k : Nat)
    (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : SlotV) (he : γl.slots[s]? = some e)
    (R : IProp GF) (Q : SlotSt → IProp GF) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger -∗
        isSlot e.loc e.γ e.q -∗ slotsInv γ cf k γl γc -∗ R -∗
        (∀ st, slotGhost γ cf k γl γc s st -∗ R ={⊤ \ ↑(slotN k s)}=∗
          slotGhost γ cf k γl γc s st ∗ Q st) -∗
        (∀ st, Q st -∗ Φ #st.isDone) -∗
      WP (App (Val (e.loc @!! go.GoType.PointerType Slot.ty @!! go!"GetIsDone")) (Val #())) {{ Φ }} := by
  iintro %Φ #Hp #Hs #Hi HR Hstep HΦ
  iapply wp_GetIsDone_inv hGID γ k γl γc s e he R Q
  iframe
  isplitr
  · iexact Hp
  isplitr
  · iexact Hs
  iexact Hi

theorem wp_HasEnoughMsg_t (hspec : Slot.HasEnoughMsg.spec (GF := GF)) (γ : Names) (k : Nat)
    (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : SlotV) (he : γl.slots[s]? = some e)
    (phase round : w32) (hr : round = 1 ∨ round = 2)
    (R : IProp GF) (Q : SlotSt → IProp GF) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger -∗
        isSlot e.loc e.γ e.q -∗ confRO cf -∗ slotsInv γ cf k γl γc -∗ R -∗
        (∀ st, slotGhost γ cf k γl γc s st -∗ R ={⊤ \ ↑(slotN k s)}=∗
          slotGhost γ cf k γl γc s (st) ∗ Q st) -∗
        (∀ st, Q st -∗ Φ #(decide (st.total phase.toNat round.toNat ≥ cf.q))) -∗
      WP (App (App (Val (e.loc @!! go.GoType.PointerType Slot.ty @!! go!"HasEnoughMsg")) (Val #phase)) (Val #round)) {{ Φ }} := by
  iintro %Φ #Hp #Hs #Hc #Hi HR Hstep HΦ
  iapply wp_HasEnoughMsg_inv hspec γ k γl γc s e he phase round hr R Q
  iframe
  repeat (first | iexact Hp | iexact Hs | iexact Hi | iexact Hc | iexact Hv | isplitr)

theorem wp_GetHasRecvDec_t (hspec : Slot.GetHasRecvDec.spec (GF := GF)) (γ : Names) (k : Nat)
    (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : SlotV) (he : γl.slots[s]? = some e)
    (R : IProp GF) (Q : SlotSt → IProp GF) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger -∗
        isSlot e.loc e.γ e.q -∗ slotsInv γ cf k γl γc -∗ R -∗
        (∀ st, slotGhost γ cf k γl γc s st -∗ R ={⊤ \ ↑(slotN k s)}=∗
          slotGhost γ cf k γl γc s (st) ∗ Q st) -∗
        (∀ st, Q st -∗ Φ #st.hasRecvDec) -∗
      WP (App (Val (e.loc @!! go.GoType.PointerType Slot.ty @!! go!"GetHasRecvDec")) (Val #())) {{ Φ }} := by
  iintro %Φ #Hp #Hs #Hi HR Hstep HΦ
  iapply wp_GetHasRecvDec_inv hspec γ k γl γc s e he R Q
  iframe
  repeat (first | iexact Hp | iexact Hs | iexact Hi | iexact Hc | iexact Hv | isplitr)

theorem wp_SetHasRecvDec_t (hspec : Slot.SetHasRecvDec.spec (GF := GF)) (γ : Names) (k : Nat)
    (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : SlotV) (he : γl.slots[s]? = some e)
    (R : IProp GF) (Q : SlotSt → IProp GF) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger -∗
        isSlot e.loc e.γ e.q -∗ slotsInv γ cf k γl γc -∗ R -∗
        (∀ st, slotGhost γ cf k γl γc s st -∗ R ={⊤ \ ↑(slotN k s)}=∗
          slotGhost γ cf k γl γc s ({ st with hasRecvDec := true }) ∗ Q st) -∗
        (∀ st, Q st -∗ Φ #()) -∗
      WP (App (Val (e.loc @!! go.GoType.PointerType Slot.ty @!! go!"SetHasRecvDec")) (Val #())) {{ Φ }} := by
  iintro %Φ #Hp #Hs #Hi HR Hstep HΦ
  iapply wp_SetHasRecvDec_inv hspec γ k γl γc s e he R Q
  iframe
  repeat (first | iexact Hp | iexact Hs | iexact Hi | iexact Hc | iexact Hv | isplitr)

theorem wp_PutRecvProposals_t (hspec : Slot.PutRecvProposals.spec (GF := GF)) (γ : Names) (k : Nat)
    (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : SlotV) (he : γl.slots[s]? = some e)
    (v : ConsensusObj) (o : ObjV)
    (R : IProp GF) (Q : SlotSt → IProp GF) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger -∗
        isSlot e.loc e.γ e.q -∗ objRep v o -∗ slotsInv γ cf k γl γc -∗ R -∗
        □ (∀ st, slotGhost γ cf k γl γc s st -∗ R -∗
          ⌜st.total 0 1 + 1 < 2 ^ 62⌝ ∗ slotGhost γ cf k γl γc s st ∗ R) -∗
        (∀ st, slotGhost γ cf k γl γc s st -∗ R ={⊤ \ ↑(slotN k s)}=∗
          slotGhost γ cf k γl γc s (st.addProp o) ∗ Q st) -∗
        (∀ st, Q st -∗ Φ #()) -∗
      WP (App (Val (e.loc @!! go.GoType.PointerType Slot.ty @!! go!"PutRecvProposals")) (Val #v)) {{ Φ }} := by
  iintro %Φ #Hp #Hs #Hv #Hi HR #Hpre Hstep HΦ
  iapply wp_PutRecvProposals_inv hspec γ k γl γc s e he v o R Q
  iframe
  iframe Hpre; repeat (first | iexact Hp | iexact Hs | iexact Hi | iexact Hc | iexact Hv | isplitr)

theorem wp_PutRecvBCMsgs_t (hspec : Slot.PutRecvBCMsgs.spec (GF := GF)) (γ : Names) (k : Nat)
    (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : SlotV) (he : γl.slots[s]? = some e)
    (phase round x : w32) (hr : round = 1 ∨ round = 2) (hx : x.toNat ≤ 2) (R : IProp GF)
    (Q : IProp GF) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger -∗
        isSlot e.loc e.γ e.q -∗ slotsInv γ cf k γl γc -∗ R -∗
        □ (∀ st, slotGhost γ cf k γl γc s st -∗ R -∗
          ⌜st.total phase.toNat round.toNat + 1 < 2 ^ 62⌝ ∗ slotGhost γ cf k γl γc s st ∗ R) -∗
        (∀ st, slotGhost γ cf k γl γc s st -∗ R ={⊤ \ ↑(slotN k s)}=∗
          slotGhost γ cf k γl γc s (st.put phase.toNat round.toNat x.toNat) ∗ Q) -∗
        (Q -∗ Φ #()) -∗
      WP (App (App (App (Val (e.loc @!! go.GoType.PointerType Slot.ty @!! go!"PutRecvBCMsgs"))
        (Val #phase)) (Val #round)) (Val #x)) {{ Φ }} := by
  iintro %Φ #Hp #Hs #Hi HR #Hpre Hstep HΦ
  iapply wp_PutRecvBCMsgs_inv hspec γ k γl γc s e he phase round x hr hx R Q
  iframe
  iframe Hpre; repeat (first | iexact Hp | iexact Hs | iexact Hi | isplitr)

theorem wp_binConMsgHandling
    (hGID : Slot.GetIsDone.spec (GF := GF)) (hGRD : Slot.GetHasRecvDec.spec (GF := GF))
    (hSRD : Slot.SetHasRecvDec.spec (GF := GF)) (hHEM : Slot.HasEnoughMsg.spec (GF := GF))
    (hPRP : Slot.PutRecvProposals.spec (GF := GF)) (hPBC : Slot.PutRecvBCMsgs.spec (GF := GF))
    (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames)
    (ch : SrvChans) (c : Loc) (v : Msg) (m : MsgV) (X j : Nat) (l : List MsgV)
    (hX : X < cf.n) (hc : cf.Ok) (hl : l[j]? = some m)
    (hty : m.ty = tyProposal ∨ m.ty = tyState ∨ m.ty = tyVote ∨ m.ty = tyDecision) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.roles.server.layers.consensus ∗ confRO cf ∗
        shared γ ∗ consRO γ cf k γl γc ch c ∗
        (∃ n : w64, structFieldRef Consensus go!"OlderThanTermMsg" c ↦ n) ∗
        frzRes γc ∗ ([∗list] s ↦ _e ∈ γl.slots, hSlot γl γc s) ∗
        msgRep v m ∗ bcastLb γ X l ∗ bmsgOk γ cf X m ∗ rcpt γl X j ∗ prevWit γl γc X m }}
      (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"binConMsgHandling")) (Val #v))
    {{ RET #(); (∃ n : w64, structFieldRef Consensus go!"OlderThanTermMsg" c ↦ n) ∗
        frzRes γc ∗ ([∗list] s ↦ _e ∈ γl.slots, hSlot γl γc s) ∗ msgWit γl γc X m }} := by
  wp_start as ⟨#Hconf, #Hsh, #Hro, Hold, Hfrz, Hslots, #Hm, #Hlb, #Hok, Hrc, #Hprev⟩
  ihave %hob := bmsgOk_obj γ X m hty $$ Hok
  obtain ⟨o, ho⟩ := hob
  ihave ⟨%ov, #Hov, #Hor⟩ := cons_msgRep_obj v m o ho $$ Hm
  ihave %hmf := msgRep_fields v m $$ Hm
  ihave %hof := objRep_fields ov o $$ Hor
  ihave ⟨%ps, #Hc⟩ := confRO_val $$ Hconf
  ihave Hc2 := Hc
  iStructNamed Hc2
  ihave Hov2 := Hov
  iStructNamed Hov2
  wp_auto
  wp_if_destruct
  · iapply HΦ
    iframe
    iapply msgWit_big γl γc X m o ho (by rw [← hof.2.2.1]; unfold lenLedger; word)
  have hs : o.svrSeq.toNat < lenLedger := by rw [← hof.2.2.1]; unfold lenLedger; word
  wp_apply wp_UpdateTermIfNecessary γ k γl γc ch c ov.SvrSeq' false (by rw [hof.2.2.1]; exact hs)
    $$ [$Hconf $Hro]
  unfold consRO
  icases Hro with ⟨%ledger, %qlk, %wg, #HId, #HWg, #HDone, #Hn2h, #Hh2n, #Hn2e, #He2n, #HQL, #HL,
    #HQm, #HSm, #HCh, #HLro, #HSI, #HSC, #HK⟩
  unfold ledgerRO
  icases HLro with ⟨#Hsl, %Hlen, #Hslots0⟩
  obtain ⟨e, he⟩ : ∃ e, γl.slots[o.svrSeq.toNat]? = some e :=
    Option.isSome_iff_exists.mp (by simp [Hlen]; exact hs)
  ihave %Hl := ownSlice_len _ _ _ $$ Hsl
  rw [List.length_map, Hlen] at Hl
  ihave #Hse := (BigSepL.bigSepL_lookup
    (Φ := fun _ e => iprop(isSlot (GF := GF) e.loc e.γ e.q)) he) $$ Hslots0
  wp_auto
  have hmod : ov.SvrSeq' % W32 10000 = ov.SvrSeq' := by
    rw [hof.2.2.1]; unfold lenLedger at hs; word
  rw [hmod]
  slice_index_if
  wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z ov.SvrSeq'))) _ _ e.loc (by word) $$ [Hsl]
    with Hsl2
  · iframe Hsl; ipureintro
    rw [show (sint.Z (W64 (uint.Z ov.SvrSeq'))).toNat = o.svrSeq.toNat by rw [hof.2.2.1]; word]
    simp [he]
  ihave #Hpl : isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger $$ []
  · iPkgInit
  have hmr : ∀ s' r, msgRound m = some (s', r) → s' = o.svrSeq.toNat := by
    intro s' r h; unfold msgRound at h; rw [ho] at h
    cases hr : roundOf m <;> simp [hr] at h; exact h.1.symm
  wp_apply_core wp_GetIsDone_t hGID γ k γl γc o.svrSeq.toNat e he iprop(True)
    (fun st => iprop(if st.isDone then doneW γl γc o.svrSeq.toNat else prevC γl γc X m))
    $$ Hpl Hse HSI []
  · iintro %st Hg -
    iapply hstep_isDone γ k γl γc o.svrSeq.toNat X m hmr st $$ [Hg]
    iframe; iexact Hprev
  iintro %st Hw
  cases hdone : st.isDone with
  | true =>
    simp only [↓reduceIte]
    wp_auto
    iapply HΦ
    iframe
    iapply msgWit_doneW γl γc X m o.svrSeq.toNat hmr $$ Hw
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte]
  ihave #Hpc := Hw
  rcases hty with hty | hty | hty | hty
  · have htv : v.Type' = W32 1 := by rw [hmf.1, hty]; rfl
    ihave ⟨Hhs, Hrest⟩ := (BigSepL.bigSepL_lookup_acc
      (Φ := fun s _ => hSlot (GF := GF) γl γc s) he).1 $$ Hslots
    iunfold hSlot at Hhs
    icases Hhs with ⟨%sent, %ents, %ql, Hprod, %hsl, He, Hq, Hp⟩
    ihave Hh : hHalves γl γc o.svrSeq.toNat ents ql none $$ [He Hq Hp]
    · unfold hHalves; iframe
    wp_auto
    simp only [htv, _root_.decide_true]
    ledger_load
    wp_apply_core wp_HasEnoughMsg_t hHEM γ k γl γc o.svrSeq.toNat e he (W32 0) (W32 1)
      (Or.inl rfl) (hHalves γl γc o.svrSeq.toNat ents ql none)
      (fun st => iprop(hHalves γl γc o.svrSeq.toNat ents ql none ∗
        ⌜∃ exd dl rl, SlotOk cf o.svrSeq.toNat st ents ql none exd dl rl⌝))
      $$ Hpl Hse Hconf HSI Hh
    · iintro %st Hg Hh
      iapply hstep_agree $$ Hg Hh
    iintro %st ⟨Hh, %hok⟩
    obtain ⟨exd, dl, rl, hok⟩ := hok
    have hmr0 : msgRound m = some (o.svrSeq.toNat, 0) := by
      unfold msgRound roundOf; simp [hty, ho]
    have hp := pure_before hc (p := 0) (r := 1) hok (Or.inl rfl)
    simp only [show (W32 0).toNat = 0 from rfl, show (W32 1).toNat = 1 from rfl]
    simp only [Nat.mul_zero, Nat.zero_add, Nat.sub_self] at hp
    by_cases hge : st.total 0 1 ≥ cf.q
    · simp only [hge, _root_.decide_true]
      wp_auto
      ihave #Hql : monoListLbOwn (γc.qlog o.svrSeq.toNat) ql $$ [Hh]
      · unfold hHalves; icases Hh with ⟨-, Hq, -⟩; iapply monoListLbOwn_get _ _ _ $$ Hq
      iapply HΦ
      iframe Hold Hfrz
      isplitl [Hrest Hprod Hh]
      · iapply hslots_restore γl γc o.svrSeq.toNat e he
        iframe Hrest
        iunfold hSlot
        iexists sent, ents, ql
        iunfold hHalves at Hh
        icases Hh with ⟨He, Hq, Hp⟩
        iframe
        ipureintro; exact hsl
      · iapply msgWit_of γl γc X m _ 0 hmr0 hs
        unfold doneOr notified qLb
        iright; ileft
        iexists ql; iframe Hql
        ipureintro; exact hp.1 hge
    simp only [hge, _root_.decide_false]
    ledger_load
    ihave HeR : entRes γ cf γl γc o.svrSeq.toNat (0, X, j, m) $$ [Hrc]
    · unfold entRes; simp only
      iframe Hrc; iframe Hok
      iexists l; iframe Hlb; ipureintro; exact hl
    have hlt := hp.2.1 hge
    wp_apply_core wp_PutRecvProposals_t hPRP γ k γl γc o.svrSeq.toNat e he ov o
      iprop(hHalves γl γc o.svrSeq.toNat ents ql none ∗ entRes γ cf γl γc o.svrSeq.toNat (0, X, j, m))
      (fun _ => iprop(hHalves γl γc o.svrSeq.toNat (ents ++ [(0, X, j, m)]) ql
          (if (tally (ents ++ [(0, X, j, m)]) 0).length = cf.q then some (some 0) else none) ∗
        counted γl γc o.svrSeq.toNat 0 X ∗
        ⌜(tally (ents ++ [(0, X, j, m)]) 0).length = cf.q →
          (0 = 0 ∨ some (0 - 1) ∈ ql) ∧ some 0 ∉ ql⌝))
      $$ Hpl Hse Hor HSI [Hh HeR]
    · iframe
    · iintro !> %st Hg ⟨Hh, HeR⟩
      ihave ⟨%h, Hg, Hh⟩ := gs_agree γ k γl γc o.svrSeq.toNat st ents ql none $$ [Hg Hh]
      · iframe
      obtain ⟨exd', dl', rl', hok'⟩ := h
      iframe
      ipureintro
      exact (pure_before hc (p := 0) (r := 1) hok' (Or.inl rfl)).2.2
    · iintro %st Hg ⟨Hh, HeR⟩
      iapply gs_count γ k γl γc o.svrSeq.toNat st (st.addProp o) ents ql (0, X, j, m)
        (⊤ \ ↑(slotN k o.svrSeq.toNat)) (bcast_slot_sub X k _) hX (Nat.lt_of_lt_of_le hX (cf_n_le hc)) hmr0 hlt
        (fun h => h.addProp _ rfl o ho) rfl rfl $$ [Hg Hh HeR]
      iframe; iexact Hsh
    iintro %st ⟨Hh, #Hcnt, %hpost⟩
    ledger_load
    wp_apply_core wp_HasEnoughMsg_t hHEM γ k γl γc o.svrSeq.toNat e he (W32 0) (W32 1)
      (Or.inl rfl) (hHalves γl γc o.svrSeq.toNat (ents ++ [(0, X, j, m)]) ql
          (if (tally (ents ++ [(0, X, j, m)]) 0).length = cf.q then some (some 0) else none))
      (fun st => iprop(hHalves γl γc o.svrSeq.toNat (ents ++ [(0, X, j, m)]) ql
          (if (tally (ents ++ [(0, X, j, m)]) 0).length = cf.q then some (some 0) else none) ∗
        ⌜∃ exd dl rl, SlotOk cf o.svrSeq.toNat st (ents ++ [(0, X, j, m)]) ql
          (if (tally (ents ++ [(0, X, j, m)]) 0).length = cf.q then some (some 0) else none)
          exd dl rl⌝))
      $$ Hpl Hse Hconf HSI Hh
    · iintro %st Hg Hh
      iapply hstep_agree $$ Hg Hh
    iintro %st2 ⟨Hh, %hok2⟩
    obtain ⟨exd2, dl2, rl2, hok2⟩ := hok2
    have hpa := pure_after (p := 0) (r := 1) hok2 (Or.inl rfl)
    simp only [show (W32 0).toNat = 0 from rfl, show (W32 1).toNat = 1 from rfl]
    simp only [Nat.mul_zero, Nat.zero_add, Nat.sub_self] at hpa
    rcases (Decidable.em ((tally (ents ++ [(0, X, j, m)]) 0).length = cf.q)).symm with hfull | hfull
    · have hng : ¬ st2.total 0 1 ≥ cf.q := fun h => hfull (hpa.1 h)
      simp only [hng, _root_.decide_false, hfull, ↓reduceIte]
      wp_auto
      iapply HΦ
      iframe Hold Hfrz
      isplitl [Hrest Hprod Hh]
      · iapply hslots_restore γl γc o.svrSeq.toNat e he
        iframe Hrest
        iunfold hSlot
        iexists sent, ents ++ [(0, X, j, m)], ql
        iunfold hHalves at Hh
        icases Hh with ⟨He, Hq, Hp⟩
        iframe
        ipureintro; exact hsl
      · iapply msgWit_of γl γc X m _ 0 hmr0 hs
        unfold doneOr
        ileft; iexact Hcnt
    have hge2 : st2.total 0 1 ≥ cf.q := hpa.2 hfull
    simp only [hge2, _root_.decide_true, hfull, ↓reduceIte]
    obtain ⟨-, hnot⟩ := hpost hfull
    imod gs_notify γ k γl γc o.svrSeq.toNat e he _ ql 0 (Or.inl rfl) hnot $$ [HSI Hh]
      with ⟨Hh, #Hqlb, %hfm⟩
    · iframe; iexact HSI
    imod frz_mint γc o.svrSeq.toNat 0 $$ Hfrz with ⟨Hfrz, #Hrd⟩
    ihave ⟨#HQ, #HT⟩ := isSlot_queue e.loc e.γ e.q $$ Hse
    ledger_load
    ihave #Hsc := (BigSepL.bigSepL_lookup
      (Φ := fun s e => iprop(slotChan (GF := GF) γ cf γc s e)) he) $$ HSC
    unfold slotChan
    ihave #Hmo : msgRep { Type' := W32 1, Phase' := W32 0, Value' := ov.SvrSeq', Obj' := null }
        ⟨tyProposal, W32 0, ov.SvrSeq', none⟩ $$ []
    · iapply cons_msgRep_intro _ _ ⟨rfl, rfl, rfl⟩
      ipureintro; rfl
    ihave Hqp := mk_slotQPx_round γ γc o.svrSeq.toNat ql 0
      { Type' := W32 1, Phase' := W32 0, Value' := ov.SvrSeq', Obj' := null } ⟨tyProposal, W32 0, ov.SvrSeq', none⟩
      (by simp [roundOf]) hfm ⟨fun _ => rfl, by intro h; simp [tyState] at h⟩ $$ [Hqlb Hrd Hmo]
    · iframe; iframe Hqlb Hrd; iexact Hmo
    rw [← hsl]
    wp_apply wp_spsc_send (γc.queue o.svrSeq.toNat) e.q (slotQPx γ cf γc o.svrSeq.toNat)
      (fun _ => iprop(False)) sent _ $$ [$Hsc $Hprod $Hqp]
    iintro Hprod
    wp_auto
    iapply HΦ
    iframe Hold Hfrz
    isplitl [Hrest Hprod Hh]
    · iapply hslots_restore γl γc o.svrSeq.toNat e he
      iframe Hrest
      iunfold hSlot
      iexists sent ++ [_], ents ++ [(0, X, j, m)], ql ++ [some 0]
      iunfold hHalves at Hh
      icases Hh with ⟨He, Hq, Hp⟩
      iframe
      ipureintro; simp [hsl]
    · iapply msgWit_of γl γc X m _ 0 hmr0 hs
      unfold doneOr
      ileft; iexact Hcnt
  · have htv : v.Type' = W32 2 := by rw [hmf.1, hty]; rfl
    imod bmsg_bound γ X m (Or.inl hty) $$ [Hsh Hok] with %hbnd
    · iframe; iframe Hsh Hok
    obtain ⟨ρ1, hρ⟩ : ∃ ρ1, 2 * m.phase.toNat + 1 - 1 = ρ1 + 1 := ⟨2 * m.phase.toNat - 1, by have := hbnd.2 hty; omega⟩
    have hmr0 : msgRound m = some (o.svrSeq.toNat, ρ1 + 1) := by
      unfold msgRound roundOf; simp [hty, ho, tyState, tyProposal]; omega
    ihave #Hpw : counted γl γc o.svrSeq.toNat ρ1 X ∨ notified γc o.svrSeq.toNat ρ1 $$ [Hpc]
    · unfold prevC; rw [hmr0]; simp only [hs, ↓reduceIte]; iexact Hpc
    ihave ⟨Hhs, Hrest⟩ := (BigSepL.bigSepL_lookup_acc
      (Φ := fun s _ => hSlot (GF := GF) γl γc s) he).1 $$ Hslots
    iunfold hSlot at Hhs
    icases Hhs with ⟨%sent, %ents, %ql, Hprod, %hsl, He, Hq, Hp⟩
    ihave Hh : hHalves γl γc o.svrSeq.toNat ents ql none $$ [He Hq Hp]
    · unfold hHalves; iframe
    wp_auto
    simp only [htv, _root_.decide_true, _root_.decide_false, show (W32 2 = W32 1) = False by decide,
      show (W32 2 = W32 2) = (2 = 2) by decide, show (W32 2 = W32 3) = (2 = 3) by decide]
    rw [hmf.2.1, hmf.2.2]
    ledger_load
    wp_apply_core wp_HasEnoughMsg_t hHEM γ k γl γc o.svrSeq.toNat e he m.phase (W32 1)
      (Or.inl rfl) (hHalves γl γc o.svrSeq.toNat ents ql none)
      (fun st => iprop(hHalves γl γc o.svrSeq.toNat ents ql none ∗
        ⌜∃ exd dl rl, SlotOk cf o.svrSeq.toNat st ents ql none exd dl rl⌝))
      $$ Hpl Hse Hconf HSI Hh
    · iintro %st Hg Hh
      iapply hstep_agree $$ Hg Hh
    iintro %st ⟨Hh, %hok⟩
    obtain ⟨exd, dl, rl, hok⟩ := hok
    have hp := pure_before hc (p := m.phase.toNat) (r := 1) hok (by decide)
    rw [hρ] at hp
    simp only [show (W32 1).toNat = 1 from rfl]
    by_cases hge : st.total m.phase.toNat 1 ≥ cf.q
    · simp only [hge, _root_.decide_true]
      wp_auto
      ihave #Hql : monoListLbOwn (γc.qlog o.svrSeq.toNat) ql $$ [Hh]
      · unfold hHalves; icases Hh with ⟨-, Hq, -⟩; iapply monoListLbOwn_get _ _ _ $$ Hq
      iapply HΦ
      iframe Hold Hfrz
      isplitl [Hrest Hprod Hh]
      · iapply hslots_restore γl γc o.svrSeq.toNat e he
        iframe Hrest
        iunfold hSlot
        iexists sent, ents, ql
        iunfold hHalves at Hh
        icases Hh with ⟨He, Hq, Hp⟩
        iframe
        ipureintro; exact hsl
      · iapply msgWit_of γl γc X m _ _ hmr0 hs
        unfold doneOr notified qLb
        iright; ileft
        iexists ql; iframe Hql
        ipureintro; exact hp.1 hge
    simp only [hge, _root_.decide_false]
    ledger_load
    ihave HeR : entRes γ cf γl γc o.svrSeq.toNat (ρ1 + 1, X, j, m) $$ [Hrc]
    · unfold entRes; simp only
      iframe Hrc; iframe Hok Hpw
      iexists l; iframe Hlb; ipureintro; exact hl
    have hlt := hp.2.1 hge
    wp_apply_core wp_PutRecvBCMsgs_t hPBC γ k γl γc o.svrSeq.toNat e he m.phase (W32 1) m.value
      (Or.inl rfl) hbnd.1
      iprop(hHalves γl γc o.svrSeq.toNat ents ql none ∗
        entRes γ cf γl γc o.svrSeq.toNat (ρ1 + 1, X, j, m))
      iprop(hHalves γl γc o.svrSeq.toNat (ents ++ [(ρ1 + 1, X, j, m)]) ql
          (if (tally (ents ++ [(ρ1 + 1, X, j, m)]) (ρ1 + 1)).length = cf.q then some (some (ρ1 + 1))
            else none) ∗
        counted γl γc o.svrSeq.toNat (ρ1 + 1) X ∗
        ⌜(tally (ents ++ [(ρ1 + 1, X, j, m)]) (ρ1 + 1)).length = cf.q →
          (ρ1 + 1 = 0 ∨ some (ρ1 + 1 - 1) ∈ ql) ∧ some (ρ1 + 1) ∉ ql⌝)
      $$ Hpl Hse HSI [Hh HeR]
    · iframe
    · iintro !> %st Hg ⟨Hh, HeR⟩
      ihave ⟨%h, Hg, Hh⟩ := gs_agree γ k γl γc o.svrSeq.toNat st ents ql none $$ [Hg Hh]
      · iframe
      obtain ⟨exd', dl', rl', hok'⟩ := h
      iframe
      ipureintro
      exact (pure_before hc (p := m.phase.toNat) (r := 1) hok' (by decide)).2.2
    · iintro %st Hg ⟨Hh, HeR⟩
      iapply gs_count γ k γl γc o.svrSeq.toNat st
        (st.put m.phase.toNat (W32 1).toNat m.value.toNat) ents ql (ρ1 + 1, X, j, m)
        (⊤ \ ↑(slotN k o.svrSeq.toNat)) (bcast_slot_sub X k _) hX (Nat.lt_of_lt_of_le hX (cf_n_le hc)) hmr0 hlt
        (fun (htl : TallyOk st ents) => by exact htl.put (p := m.phase.toNat) (r := 1) (Or.inl ⟨rfl, hbnd.2 hty⟩) (ρ1 + 1, X, j, m) hρ.symm)
        rfl rfl
        $$ [Hg Hh HeR]
      iframe; iexact Hsh
    iintro ⟨Hh, #Hcnt, %hpost⟩
    ledger_load
    wp_apply_core wp_HasEnoughMsg_t hHEM γ k γl γc o.svrSeq.toNat e he m.phase (W32 1)
      (Or.inl rfl) (hHalves γl γc o.svrSeq.toNat (ents ++ [(ρ1 + 1, X, j, m)]) ql
          (if (tally (ents ++ [(ρ1 + 1, X, j, m)]) (ρ1 + 1)).length = cf.q then some (some (ρ1 + 1))
            else none))
      (fun st => iprop(hHalves γl γc o.svrSeq.toNat (ents ++ [(ρ1 + 1, X, j, m)]) ql
          (if (tally (ents ++ [(ρ1 + 1, X, j, m)]) (ρ1 + 1)).length = cf.q then some (some (ρ1 + 1))
            else none) ∗
        ⌜∃ exd dl rl, SlotOk cf o.svrSeq.toNat st (ents ++ [(ρ1 + 1, X, j, m)]) ql
          (if (tally (ents ++ [(ρ1 + 1, X, j, m)]) (ρ1 + 1)).length = cf.q then some (some (ρ1 + 1))
            else none) exd dl rl⌝))
      $$ Hpl Hse Hconf HSI Hh
    · iintro %st Hg Hh
      iapply hstep_agree $$ Hg Hh
    iintro %st2 ⟨Hh, %hok2⟩
    obtain ⟨exd2, dl2, rl2, hok2⟩ := hok2
    have hpa := pure_after (p := m.phase.toNat) (r := 1) hok2 (by decide)
    rw [hρ] at hpa
    simp only [show (W32 1).toNat = 1 from rfl]
    rcases (Decidable.em ((tally (ents ++ [(ρ1 + 1, X, j, m)]) (ρ1 + 1)).length = cf.q)).symm
      with hfull | hfull
    · have hng : ¬ st2.total m.phase.toNat 1 ≥ cf.q := fun h => hfull (hpa.1 h)
      simp only [hng, _root_.decide_false, hfull, ↓reduceIte]
      wp_auto
      iapply HΦ
      iframe Hold Hfrz
      isplitl [Hrest Hprod Hh]
      · iapply hslots_restore γl γc o.svrSeq.toNat e he
        iframe Hrest
        iunfold hSlot
        iexists sent, ents ++ [(ρ1 + 1, X, j, m)], ql
        iunfold hHalves at Hh
        icases Hh with ⟨He, Hq, Hp⟩
        iframe
        ipureintro; exact hsl
      · iapply msgWit_of γl γc X m _ _ hmr0 hs
        unfold doneOr
        ileft; iexact Hcnt
    have hge2 : st2.total m.phase.toNat 1 ≥ cf.q := hpa.2 hfull
    simp only [hge2, _root_.decide_true, hfull, ↓reduceIte]
    obtain ⟨hprev, hnot⟩ := hpost hfull
    imod gs_notify γ k γl γc o.svrSeq.toNat e he _ ql (ρ1 + 1) hprev hnot $$ [HSI Hh]
      with ⟨Hh, #Hqlb, %hfm⟩
    · iframe; iexact HSI
    imod frz_mint γc o.svrSeq.toNat (ρ1 + 1) $$ Hfrz with ⟨Hfrz, #Hrd⟩
    ihave ⟨#HQ, #HT⟩ := isSlot_queue e.loc e.γ e.q $$ Hse
    ledger_load
    ihave #Hsc := (BigSepL.bigSepL_lookup
      (Φ := fun s e => iprop(slotChan (GF := GF) γ cf γc s e)) he) $$ HSC
    unfold slotChan
    ihave #Hmo : msgRep { Type' := W32 2, Phase' := m.phase, Value' := ov.SvrSeq', Obj' := null }
        ⟨tyState, m.phase, ov.SvrSeq', none⟩ $$ []
    · iapply cons_msgRep_intro _ _ ⟨rfl, rfl, rfl⟩
      ipureintro; rfl
    ihave Hqp := mk_slotQPx_round γ γc o.svrSeq.toNat ql (ρ1 + 1)
      { Type' := W32 2, Phase' := m.phase, Value' := ov.SvrSeq', Obj' := null }
      ⟨tyState, m.phase, ov.SvrSeq', none⟩
      (by simp [roundOf, tyState, tyProposal]; omega) hfm
      ⟨by intro h; simp [tyProposal] at h, fun _ => hbnd.2 hty⟩ $$ [Hqlb Hrd Hmo]
    · iframe; iframe Hqlb Hrd; iexact Hmo
    rw [← hsl]
    wp_apply wp_spsc_send (γc.queue o.svrSeq.toNat) e.q (slotQPx γ cf γc o.svrSeq.toNat)
      (fun _ => iprop(False)) sent _ $$ [$Hsc $Hprod $Hqp]
    iintro Hprod
    wp_auto
    iapply HΦ
    iframe Hold Hfrz
    isplitl [Hrest Hprod Hh]
    · iapply hslots_restore γl γc o.svrSeq.toNat e he
      iframe Hrest
      iunfold hSlot
      iexists sent ++ [_], ents ++ [(ρ1 + 1, X, j, m)], ql ++ [some (ρ1 + 1)]
      iunfold hHalves at Hh
      icases Hh with ⟨He, Hq, Hp⟩
      iframe
      ipureintro; simp [hsl]
    · iapply msgWit_of γl γc X m _ _ hmr0 hs
      unfold doneOr
      ileft; iexact Hcnt
  · have htv : v.Type' = W32 3 := by rw [hmf.1, hty]; rfl
    imod bmsg_bound γ X m (Or.inr hty) $$ [Hsh Hok] with %hbnd
    · iframe; iframe Hsh Hok
    obtain ⟨ρ1, hρ⟩ : ∃ ρ1, 2 * m.phase.toNat + 2 - 1 = ρ1 + 1 := ⟨2 * m.phase.toNat, by omega⟩
    have hmr0 : msgRound m = some (o.svrSeq.toNat, ρ1 + 1) := by
      unfold msgRound roundOf; simp [hty, ho, tyVote, tyState, tyProposal]; omega
    ihave #Hpw : counted γl γc o.svrSeq.toNat ρ1 X ∨ notified γc o.svrSeq.toNat ρ1 $$ [Hpc]
    · unfold prevC; rw [hmr0]; simp only [hs, ↓reduceIte]; iexact Hpc
    ihave ⟨Hhs, Hrest⟩ := (BigSepL.bigSepL_lookup_acc
      (Φ := fun s _ => hSlot (GF := GF) γl γc s) he).1 $$ Hslots
    iunfold hSlot at Hhs
    icases Hhs with ⟨%sent, %ents, %ql, Hprod, %hsl, He, Hq, Hp⟩
    ihave Hh : hHalves γl γc o.svrSeq.toNat ents ql none $$ [He Hq Hp]
    · unfold hHalves; iframe
    wp_auto
    simp only [htv, _root_.decide_true, _root_.decide_false, show (W32 3 = W32 1) = False by decide,
      show (W32 3 = W32 2) = (3 = 2) by decide, show (W32 3 = W32 3) = (3 = 3) by decide]
    rw [hmf.2.1, hmf.2.2]
    ledger_load
    wp_apply_core wp_HasEnoughMsg_t hHEM γ k γl γc o.svrSeq.toNat e he m.phase (W32 2)
      (Or.inr rfl) (hHalves γl γc o.svrSeq.toNat ents ql none)
      (fun st => iprop(hHalves γl γc o.svrSeq.toNat ents ql none ∗
        ⌜∃ exd dl rl, SlotOk cf o.svrSeq.toNat st ents ql none exd dl rl⌝))
      $$ Hpl Hse Hconf HSI Hh
    · iintro %st Hg Hh
      iapply hstep_agree $$ Hg Hh
    iintro %st ⟨Hh, %hok⟩
    obtain ⟨exd, dl, rl, hok⟩ := hok
    have hp := pure_before hc (p := m.phase.toNat) (r := 2) hok (by decide)
    rw [hρ] at hp
    simp only [show (W32 2).toNat = 2 from rfl]
    by_cases hge : st.total m.phase.toNat 2 ≥ cf.q
    · simp only [hge, _root_.decide_true]
      wp_auto
      ihave #Hql : monoListLbOwn (γc.qlog o.svrSeq.toNat) ql $$ [Hh]
      · unfold hHalves; icases Hh with ⟨-, Hq, -⟩; iapply monoListLbOwn_get _ _ _ $$ Hq
      iapply HΦ
      iframe Hold Hfrz
      isplitl [Hrest Hprod Hh]
      · iapply hslots_restore γl γc o.svrSeq.toNat e he
        iframe Hrest
        iunfold hSlot
        iexists sent, ents, ql
        iunfold hHalves at Hh
        icases Hh with ⟨He, Hq, Hp⟩
        iframe
        ipureintro; exact hsl
      · iapply msgWit_of γl γc X m _ _ hmr0 hs
        unfold doneOr notified qLb
        iright; ileft
        iexists ql; iframe Hql
        ipureintro; exact hp.1 hge
    simp only [hge, _root_.decide_false]
    ledger_load
    ihave HeR : entRes γ cf γl γc o.svrSeq.toNat (ρ1 + 1, X, j, m) $$ [Hrc]
    · unfold entRes; simp only
      iframe Hrc; iframe Hok Hpw
      iexists l; iframe Hlb; ipureintro; exact hl
    have hlt := hp.2.1 hge
    wp_apply_core wp_PutRecvBCMsgs_t hPBC γ k γl γc o.svrSeq.toNat e he m.phase (W32 2) m.value
      (Or.inr rfl) hbnd.1
      iprop(hHalves γl γc o.svrSeq.toNat ents ql none ∗
        entRes γ cf γl γc o.svrSeq.toNat (ρ1 + 1, X, j, m))
      iprop(hHalves γl γc o.svrSeq.toNat (ents ++ [(ρ1 + 1, X, j, m)]) ql
          (if (tally (ents ++ [(ρ1 + 1, X, j, m)]) (ρ1 + 1)).length = cf.q then some (some (ρ1 + 1))
            else none) ∗
        counted γl γc o.svrSeq.toNat (ρ1 + 1) X ∗
        ⌜(tally (ents ++ [(ρ1 + 1, X, j, m)]) (ρ1 + 1)).length = cf.q →
          (ρ1 + 1 = 0 ∨ some (ρ1 + 1 - 1) ∈ ql) ∧ some (ρ1 + 1) ∉ ql⌝)
      $$ Hpl Hse HSI [Hh HeR]
    · iframe
    · iintro !> %st Hg ⟨Hh, HeR⟩
      ihave ⟨%h, Hg, Hh⟩ := gs_agree γ k γl γc o.svrSeq.toNat st ents ql none $$ [Hg Hh]
      · iframe
      obtain ⟨exd', dl', rl', hok'⟩ := h
      iframe
      ipureintro
      exact (pure_before hc (p := m.phase.toNat) (r := 2) hok' (by decide)).2.2
    · iintro %st Hg ⟨Hh, HeR⟩
      iapply gs_count γ k γl γc o.svrSeq.toNat st
        (st.put m.phase.toNat (W32 2).toNat m.value.toNat) ents ql (ρ1 + 1, X, j, m)
        (⊤ \ ↑(slotN k o.svrSeq.toNat)) (bcast_slot_sub X k _) hX (Nat.lt_of_lt_of_le hX (cf_n_le hc)) hmr0 hlt
        (fun (htl : TallyOk st ents) => by exact htl.put (p := m.phase.toNat) (r := 2) (Or.inr rfl) (ρ1 + 1, X, j, m) hρ.symm)
        rfl rfl
        $$ [Hg Hh HeR]
      iframe; iexact Hsh
    iintro ⟨Hh, #Hcnt, %hpost⟩
    ledger_load
    wp_apply_core wp_HasEnoughMsg_t hHEM γ k γl γc o.svrSeq.toNat e he m.phase (W32 2)
      (Or.inr rfl) (hHalves γl γc o.svrSeq.toNat (ents ++ [(ρ1 + 1, X, j, m)]) ql
          (if (tally (ents ++ [(ρ1 + 1, X, j, m)]) (ρ1 + 1)).length = cf.q then some (some (ρ1 + 1))
            else none))
      (fun st => iprop(hHalves γl γc o.svrSeq.toNat (ents ++ [(ρ1 + 1, X, j, m)]) ql
          (if (tally (ents ++ [(ρ1 + 1, X, j, m)]) (ρ1 + 1)).length = cf.q then some (some (ρ1 + 1))
            else none) ∗
        ⌜∃ exd dl rl, SlotOk cf o.svrSeq.toNat st (ents ++ [(ρ1 + 1, X, j, m)]) ql
          (if (tally (ents ++ [(ρ1 + 1, X, j, m)]) (ρ1 + 1)).length = cf.q then some (some (ρ1 + 1))
            else none) exd dl rl⌝))
      $$ Hpl Hse Hconf HSI Hh
    · iintro %st Hg Hh
      iapply hstep_agree $$ Hg Hh
    iintro %st2 ⟨Hh, %hok2⟩
    obtain ⟨exd2, dl2, rl2, hok2⟩ := hok2
    have hpa := pure_after (p := m.phase.toNat) (r := 2) hok2 (by decide)
    rw [hρ] at hpa
    simp only [show (W32 2).toNat = 2 from rfl]
    rcases (Decidable.em ((tally (ents ++ [(ρ1 + 1, X, j, m)]) (ρ1 + 1)).length = cf.q)).symm
      with hfull | hfull
    · have hng : ¬ st2.total m.phase.toNat 2 ≥ cf.q := fun h => hfull (hpa.1 h)
      simp only [hng, _root_.decide_false, hfull, ↓reduceIte]
      wp_auto
      iapply HΦ
      iframe Hold Hfrz
      isplitl [Hrest Hprod Hh]
      · iapply hslots_restore γl γc o.svrSeq.toNat e he
        iframe Hrest
        iunfold hSlot
        iexists sent, ents ++ [(ρ1 + 1, X, j, m)], ql
        iunfold hHalves at Hh
        icases Hh with ⟨He, Hq, Hp⟩
        iframe
        ipureintro; exact hsl
      · iapply msgWit_of γl γc X m _ _ hmr0 hs
        unfold doneOr
        ileft; iexact Hcnt
    have hge2 : st2.total m.phase.toNat 2 ≥ cf.q := hpa.2 hfull
    simp only [hge2, _root_.decide_true, hfull, ↓reduceIte]
    obtain ⟨hprev, hnot⟩ := hpost hfull
    imod gs_notify γ k γl γc o.svrSeq.toNat e he _ ql (ρ1 + 1) hprev hnot $$ [HSI Hh]
      with ⟨Hh, #Hqlb, %hfm⟩
    · iframe; iexact HSI
    imod frz_mint γc o.svrSeq.toNat (ρ1 + 1) $$ Hfrz with ⟨Hfrz, #Hrd⟩
    ihave ⟨#HQ, #HT⟩ := isSlot_queue e.loc e.γ e.q $$ Hse
    ledger_load
    ihave #Hsc := (BigSepL.bigSepL_lookup
      (Φ := fun s e => iprop(slotChan (GF := GF) γ cf γc s e)) he) $$ HSC
    unfold slotChan
    ihave #Hmo : msgRep { Type' := W32 3, Phase' := m.phase, Value' := ov.SvrSeq', Obj' := null }
        ⟨tyVote, m.phase, ov.SvrSeq', none⟩ $$ []
    · iapply cons_msgRep_intro _ _ ⟨rfl, rfl, rfl⟩
      ipureintro; rfl
    ihave Hqp := mk_slotQPx_round γ γc o.svrSeq.toNat ql (ρ1 + 1)
      { Type' := W32 3, Phase' := m.phase, Value' := ov.SvrSeq', Obj' := null }
      ⟨tyVote, m.phase, ov.SvrSeq', none⟩
      (by simp [roundOf, tyVote, tyState, tyProposal]; omega) hfm
      ⟨by intro h; simp [tyProposal] at h, by intro h; simp [tyState] at h⟩ $$ [Hqlb Hrd Hmo]
    · iframe; iframe Hqlb Hrd; iexact Hmo
    rw [← hsl]
    wp_apply wp_spsc_send (γc.queue o.svrSeq.toNat) e.q (slotQPx γ cf γc o.svrSeq.toNat)
      (fun _ => iprop(False)) sent _ $$ [$Hsc $Hprod $Hqp]
    iintro Hprod
    wp_auto
    iapply HΦ
    iframe Hold Hfrz
    isplitl [Hrest Hprod Hh]
    · iapply hslots_restore γl γc o.svrSeq.toNat e he
      iframe Hrest
      iunfold hSlot
      iexists sent ++ [_], ents ++ [(ρ1 + 1, X, j, m)], ql ++ [some (ρ1 + 1)]
      iunfold hHalves at Hh
      icases Hh with ⟨He, Hq, Hp⟩
      iframe
      ipureintro; simp [hsl]
    · iapply msgWit_of γl γc X m _ _ hmr0 hs
      unfold doneOr
      ileft; iexact Hcnt
  · have htv : v.Type' = W32 6 := by rw [hmf.1, hty]; rfl
    ihave ⟨%o', %d, %ho', #Hfd, #Hdo⟩ := bmsg_dec γ X m hty $$ Hok
    rw [ho] at ho'; cases ho'
    have hmrn : msgRound m = none := by
      unfold msgRound roundOf; simp [hty, tyDecision, tyProposal, tyState, tyVote]
    ihave ⟨Hhs, Hrest⟩ := (BigSepL.bigSepL_lookup_acc
      (Φ := fun s _ => hSlot (GF := GF) γl γc s) he).1 $$ Hslots
    iunfold hSlot at Hhs
    icases Hhs with ⟨%sent, %ents, %ql, Hprod, %hsl, He, Hq, Hp⟩
    ihave Hh : hHalves γl γc o.svrSeq.toNat ents ql none $$ [He Hq Hp]
    · unfold hHalves; iframe
    wp_auto
    simp only [htv, show (W32 6 = W32 1) = False by decide, show (W32 6 = W32 2) = False by decide,
      show (W32 6 = W32 3) = False by decide]
    wp_auto
    ledger_load
    wp_apply_core wp_GetHasRecvDec_t hGRD γ k γl γc o.svrSeq.toNat e he
      (hHalves γl γc o.svrSeq.toNat ents ql none)
      (fun st => iprop(hHalves γl γc o.svrSeq.toNat ents ql none ∗
        ⌜∃ exd dl rl, SlotOk cf o.svrSeq.toNat st ents ql none exd dl rl⌝))
      $$ Hpl Hse HSI Hh
    · iintro %st Hg Hh
      iapply hstep_agree $$ Hg Hh
    iintro %st ⟨Hh, %hok⟩
    obtain ⟨exd, dl, rl, hok⟩ := hok
    have hwit : ⊢ msgWit (GF := GF) γl γc X m := by unfold msgWit; rw [hmrn]; iintro; itrivial
    cases hrd : st.hasRecvDec with
    | true =>
      wp_auto
      iapply HΦ
      iframe Hold Hfrz
      isplitl [Hrest Hprod Hh]
      · iapply hslots_restore γl γc o.svrSeq.toNat e he
        iframe Hrest
        iunfold hSlot
        iexists sent, ents, ql
        iunfold hHalves at Hh
        icases Hh with ⟨He, Hq, Hp⟩
        iframe
        ipureintro; exact hsl
      · iapply hwit
    | false =>
    obtain ⟨hnot, -⟩ := hok.dec_send hrd
    imod gs_decsend γ k γl γc o.svrSeq.toNat e he ents ql hnot $$ [HSI Hh] with ⟨Hh, #Hqlb⟩
    · iframe; iexact HSI
    ihave ⟨#HQ, #HT⟩ := isSlot_queue e.loc e.γ e.q $$ Hse
    wp_auto
    ledger_load
    ihave #Hsc := (BigSepL.bigSepL_lookup
      (Φ := fun s e => iprop(slotChan (GF := GF) γ cf γc s e)) he) $$ HSC
    unfold slotChan
    ihave Hqp := mk_slotQPx_dec γ γc o.svrSeq.toNat ql v m o d hty ho rfl hnot
      ⟨by intro h; rw [htv] at h; exact absurd h (by decide),
       by intro h; rw [htv] at h; exact absurd h (by decide)⟩ $$ [Hqlb Hm Hfd Hdo]
    · iframe; iframe Hqlb Hm Hfd; iexact Hdo
    rw [← hsl]
    wp_apply wp_spsc_send (γc.queue o.svrSeq.toNat) e.q (slotQPx γ cf γc o.svrSeq.toNat)
      (fun _ => iprop(False)) sent v $$ [$Hsc $Hprod $Hqp]
    iintro Hprod
    ledger_load
    wp_apply_core wp_SetHasRecvDec_t hSRD γ k γl γc o.svrSeq.toNat e he
      (hHalves γl γc o.svrSeq.toNat ents (ql ++ [none]) (some none))
      (fun _ => hHalves γl γc o.svrSeq.toNat ents (ql ++ [none]) none)
      $$ Hpl Hse HSI Hh
    · iintro %st Hg Hh
      iapply gs_decset γ k γl γc o.svrSeq.toNat st ents (ql ++ [none]) (by simp) $$ [Hg Hh]
      iframe
    iintro %st Hh
    wp_auto
    iapply HΦ
    iframe Hold Hfrz
    isplitl [Hrest Hprod Hh]
    · iapply hslots_restore γl γc o.svrSeq.toNat e he
      iframe Hrest
      iunfold hSlot
      iexists sent ++ [v], ents, ql ++ [none]
      iunfold hHalves at Hh
      icases Hh with ⟨He, Hq, Hp⟩
      iframe
      ipureintro; simp [hsl]
    · iapply hwit

end proof

end Perennial.rabia.roles.server.layers.consensus
