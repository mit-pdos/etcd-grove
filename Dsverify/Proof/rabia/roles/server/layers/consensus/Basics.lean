/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/layers/consensus/Base.lean`, run `rabia-r1wake-1`.)

The consensus package's internal basics: timelessness of the slots' invariant, and the slot
accesses (each atomic `Slot` method used with the slot's invariant open).
-/
module

public import Dsverify.Proof.rabia.roles.server.layers.consensus.Spec

@[expose] public section

noncomputable section

namespace Perennial.rabia.roles.server.layers.consensus

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model Net rabia.internal.message
  rabia.internal.config rabia.internal.ledger rabia rabia.internal.queue

set_option linter.unusedSectionVars false

section timeless
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable {cf : RCfg}

theorem prefixFacts_timeless (γ : RabiaNames) :
    ∀ (s : Nat) (cmds : List GoString), Timeless (prefixFacts (GF := GF) γ s cmds)
  | 0, cmds => by unfold prefixFacts; infer_instance
  | s + 1, cmds => by
    have := prefixFacts_timeless γ s
    unfold prefixFacts
    refine @exists_timeless _ _ _ _ (fun cmds0 => @exists_timeless _ _ _ _ (fun d => ?_))
    cases d <;> dsimp only <;> infer_instance

instance prefixFacts_timeless_inst (γ : RabiaNames) (s : Nat) (cmds : List GoString) :
    Timeless (prefixFacts (GF := GF) γ s cmds) := prefixFacts_timeless γ s cmds

instance objOk_timeless (γ : Names) (o : ObjV) : Timeless (objOk (GF := GF) γ cf o) := by
  unfold objOk; infer_instance

instance decObjOk_timeless (γ : Names) (s : Nat) (d : DVal) (o : ObjV) :
    Timeless (decObjOk (GF := GF) γ cf s d o) := by
  unfold decObjOk; cases d <;> infer_instance

instance decInfo_timeless (γ : Names) (s : Nat) (st : SlotSt) :
    Timeless (decInfo (GF := GF) γ cf s st) := by
  unfold decInfo; split <;> infer_instance

instance bmsgOk_timeless (γ : Names) (X : Nat) (m : MsgV) : Timeless (bmsgOk (GF := GF) γ cf X m) := by
  unfold bmsgOk; repeat (first | split | infer_instance)

instance bmsgOk_persistent (γ : Names) (X : Nat) (m : MsgV) :
    Persistent (bmsgOk (GF := GF) γ cf X m) := by
  unfold bmsgOk; repeat (first | split | infer_instance)

instance entRes_timeless (γ : Names) (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : Ent) :
    Timeless (entRes (GF := GF) γ cf γl γc s e) := by
  unfold entRes counted notified qLb bcastLb rcpt
  rcases e with ⟨_ | ρ, X, j, m⟩ <;> dsimp only <;> infer_instance

instance slotGhost_timeless (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (s : Nat)
    (st : SlotSt) : Timeless (slotGhost (GF := GF) γ cf k γl γc s st) := by
  unfold slotGhost; infer_instance

instance slotInv_timeless (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (s : Nat)
    (e : SlotV) : Timeless (slotInv (GF := GF) γ cf k γl γc s e) := by
  unfold slotInv slotSt; infer_instance

theorem decInfo_congr (γ : Names) (s : Nat) {st st' : SlotSt} (h1 : st'.isDone = st.isDone)
    (h2 : st'.decision = st.decision) : decInfo (GF := GF) γ cf s st' = decInfo γ cf s st := by
  unfold decInfo; rw [h1, h2]

theorem decInfo_eq (γ : Names) (s : Nat) {st st' : SlotSt} (h1 : st'.isDone = st.isDone)
    (h2 : st'.decision = st.decision) : decInfo (GF := GF) γ cf s st ⊢ decInfo γ cf s st' := by
  rw [decInfo_congr γ s h1 h2]

instance cons_bcastLb_persistent (γ : Names) (X : Nat) (l : List MsgV) :
    Persistent (bcastLb (GF := GF) γ X l) := by unfold bcastLb; infer_instance
instance cons_hLb_persistent (γl : SrvNames) (l : List (Nat × Nat)) :
    Persistent (hLb (GF := GF) γl l) := by unfold hLb; infer_instance
instance cons_exLb_persistent (γl : SrvNames) (l : List MsgV) :
    Persistent (exLb (GF := GF) γl l) := by unfold exLb; infer_instance
instance cons_qLb_persistent (γc : ConsNames) (s : Nat) (l : List (Option Nat)) :
    Persistent (qLb (GF := GF) γc s l) := by unfold qLb; infer_instance
instance cons_roundDone_persistent (γc : ConsNames) (s ρ : Nat) :
    Persistent (roundDone (GF := GF) γc s ρ) := by unfold roundDone; infer_instance
instance cons_counted_persistent (γl : SrvNames) (γc : ConsNames) (s ρ X : Nat) :
    Persistent (counted (GF := GF) γl γc s ρ X) := by unfold counted; infer_instance
instance cons_notified_persistent (γc : ConsNames) (s ρ : Nat) :
    Persistent (notified (GF := GF) γc s ρ) := by unfold notified qLb; infer_instance
instance cons_doneW_persistent (γl : SrvNames) (γc : ConsNames) (s : Nat) :
    Persistent (doneW (GF := GF) γl γc s) := by unfold doneW; infer_instance
instance cons_rdW_persistent (γl : SrvNames) (γc : ConsNames) (s : Nat) :
    Persistent (rdW (GF := GF) γl γc s) := by unfold rdW; infer_instance
instance cons_pendOk_persistent_objOk (γ : Names) (o : ObjV) :
    Persistent (objOk (GF := GF) γ cf o) := by unfold objOk; infer_instance

/-- (A missing law of `message`: unfolds `msgRep`.) A represented message's scalar fields. -/
theorem cons_msgRep_fields (v : Msg) (m : MsgV) :
    msgRep (GF := GF) v m ⊢ ⌜v.Type' = m.ty ∧ v.Phase' = m.phase ∧ v.Value' = m.value⌝ := by
  unfold msgRep; iintro ⟨%h, -⟩; ipureintro; exact h

/-- (A missing law of `message`: unfolds `msgRep`.) A represented message's object. -/
theorem cons_msgRep_obj (v : Msg) (m : MsgV) (o : ObjV) (h : m.obj = some o) :
    msgRep (GF := GF) v m ⊢ ∃ ov, v.Obj' ↦□ ov ∗ objRep ov o := by
  unfold msgRep; rw [h]; iintro ⟨-, H⟩; iexact H

/-- (A missing law of `message`: unfolds `msgRep`.) Building a represented message. -/
theorem cons_msgRep_intro (v : Msg) (m : MsgV)
    (h : v.Type' = m.ty ∧ v.Phase' = m.phase ∧ v.Value' = m.value) :
    (match m.obj with
     | none => iprop(⌜v.Obj' = null⌝)
     | some o => iprop(∃ ov, v.Obj' ↦□ ov ∗ objRep ov o)) ⊢ msgRep (GF := GF) v m := by
  unfold msgRep; iintro H; iframe H; ipureintro; exact h

end timeless

end Perennial.rabia.roles.server.layers.consensus

namespace Perennial.rabia.roles.server.layers.consensus

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model Net rabia.internal.message
  rabia.internal.config rabia.internal.ledger rabia rabia.internal.queue

section acc
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable {cf : RCfg}
variable [package_sem : rabia.internal.ledger.Assumptions]

theorem slotsInv_lookup (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : SlotV)
    (he : γl.slots[s]? = some e) :
    slotsInv (GF := GF) γ cf k γl γc ⊢ inv (slotN k s) (slotInv γ cf k γl γc s e) := by
  unfold slotsInv
  iintro #Hinv
  iapply (BigSepL.bigSepL_lookup
    (Φ := fun s e => iprop(inv (slotN k s) (slotInv (GF := GF) γ cf k γl γc s e))) he) $$ Hinv

/-- `GetIsDone` with slot `s`'s invariant open (a ghost step `Hstep` on its state). -/
theorem wp_GetIsDone_inv (hspec : Slot.GetIsDone.spec (GF := GF)) (γ : Names) (k : Nat)
    (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : SlotV) (he : γl.slots[s]? = some e)
    
    (R : IProp GF) (Q : SlotSt → IProp GF) (Φ : val → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger ∗ isSlot e.loc e.γ e.q ∗
      slotsInv γ cf k γl γc ∗ R ∗
      (∀ st, slotGhost γ cf k γl γc s st -∗ R ={⊤ \ ↑(slotN k s)}=∗
        slotGhost γ cf k γl γc s (st) ∗ Q st) ∗
      (∀ st, Q st -∗ Φ (#st.isDone)) ⊢
    WP (App (Val (e.loc @!! go.GoType.PointerType Slot.ty @!! go!"GetIsDone")) (Val #())) {{ Φ }} := by
  iintro ⟨#Hpkg, #Hslot, #Hinvs, HR, Hstep, HΦ⟩
  ihave #Hinv := slotsInv_lookup γ k γl γc s e he $$ Hinvs
  ihave Hspec := hspec e.loc e.γ e.q  $$ Hpkg Hslot
  iunfold atomic_wp at Hspec
  iapply Hspec
  rw [Std.LawfulSet.diff_empty]
  iauintro
  unfold atomic_acc
  iinv Hinv with Hi Hclose
  imod Hi with Hi
  unfold slotInv
  icases Hi with ⟨%st, Hst, #Hd, Hg⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists (⟨st, ⟨⟩⟩ : (Tele.cons fun _ : SlotSt => Tele.nil).Arg)
  dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM]
  iframe Hst
  isplit
  · iintro Hst
    imod Hmask with -
    imod Hclose $$ [Hst Hg] with -
    · inext
      iexists st
      iframe Hst Hg; iexact Hd
    imodintro
    iframe
  · iintro Hst
    imod Hmask with -
    imod Hstep $$ %st Hg HR with ⟨Hg, HQ⟩
    imod Hclose $$ [Hst Hg] with -
    · inext
      iexists st
      iframe Hst Hg
      iexact Hd
    imodintro
    iintro -
    iapply HΦ $$ HQ

/-- `GetHasRecvDec` with slot `s`'s invariant open (a ghost step `Hstep` on its state). -/
theorem wp_GetHasRecvDec_inv (hspec : Slot.GetHasRecvDec.spec (GF := GF)) (γ : Names) (k : Nat)
    (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : SlotV) (he : γl.slots[s]? = some e)
    
    (R : IProp GF) (Q : SlotSt → IProp GF) (Φ : val → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger ∗ isSlot e.loc e.γ e.q ∗
      slotsInv γ cf k γl γc ∗ R ∗
      (∀ st, slotGhost γ cf k γl γc s st -∗ R ={⊤ \ ↑(slotN k s)}=∗
        slotGhost γ cf k γl γc s (st) ∗ Q st) ∗
      (∀ st, Q st -∗ Φ (#st.hasRecvDec)) ⊢
    WP (App (Val (e.loc @!! go.GoType.PointerType Slot.ty @!! go!"GetHasRecvDec")) (Val #())) {{ Φ }} := by
  iintro ⟨#Hpkg, #Hslot, #Hinvs, HR, Hstep, HΦ⟩
  ihave #Hinv := slotsInv_lookup γ k γl γc s e he $$ Hinvs
  ihave Hspec := hspec e.loc e.γ e.q  $$ Hpkg Hslot
  iunfold atomic_wp at Hspec
  iapply Hspec
  rw [Std.LawfulSet.diff_empty]
  iauintro
  unfold atomic_acc
  iinv Hinv with Hi Hclose
  imod Hi with Hi
  unfold slotInv
  icases Hi with ⟨%st, Hst, #Hd, Hg⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists (⟨st, ⟨⟩⟩ : (Tele.cons fun _ : SlotSt => Tele.nil).Arg)
  dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM]
  iframe Hst
  isplit
  · iintro Hst
    imod Hmask with -
    imod Hclose $$ [Hst Hg] with -
    · inext
      iexists st
      iframe Hst Hg; iexact Hd
    imodintro
    iframe
  · iintro Hst
    imod Hmask with -
    imod Hstep $$ %st Hg HR with ⟨Hg, HQ⟩
    imod Hclose $$ [Hst Hg] with -
    · inext
      iexists st
      iframe Hst Hg
      iexact Hd
    imodintro
    iintro -
    iapply HΦ $$ HQ

/-- `SetHasRecvDec` with slot `s`'s invariant open (a ghost step `Hstep` on its state). -/
theorem wp_SetHasRecvDec_inv (hspec : Slot.SetHasRecvDec.spec (GF := GF)) (γ : Names) (k : Nat)
    (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : SlotV) (he : γl.slots[s]? = some e)
    
    (R : IProp GF) (Q : SlotSt → IProp GF) (Φ : val → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger ∗ isSlot e.loc e.γ e.q ∗
      slotsInv γ cf k γl γc ∗ R ∗
      (∀ st, slotGhost γ cf k γl γc s st -∗ R ={⊤ \ ↑(slotN k s)}=∗
        slotGhost γ cf k γl γc s ({ st with hasRecvDec := true }) ∗ Q st) ∗
      (∀ st, Q st -∗ Φ (#())) ⊢
    WP (App (Val (e.loc @!! go.GoType.PointerType Slot.ty @!! go!"SetHasRecvDec")) (Val #())) {{ Φ }} := by
  iintro ⟨#Hpkg, #Hslot, #Hinvs, HR, Hstep, HΦ⟩
  ihave #Hinv := slotsInv_lookup γ k γl γc s e he $$ Hinvs
  ihave Hspec := hspec e.loc e.γ e.q  $$ Hpkg Hslot
  iunfold atomic_wp at Hspec
  iapply Hspec
  rw [Std.LawfulSet.diff_empty]
  iauintro
  unfold atomic_acc
  iinv Hinv with Hi Hclose
  imod Hi with Hi
  unfold slotInv
  icases Hi with ⟨%st, Hst, #Hd, Hg⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists (⟨st, ⟨⟩⟩ : (Tele.cons fun _ : SlotSt => Tele.nil).Arg)
  dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM]
  iframe Hst
  isplit
  · iintro Hst
    imod Hmask with -
    imod Hclose $$ [Hst Hg] with -
    · inext
      iexists st
      iframe Hst Hg; iexact Hd
    imodintro
    iframe
  · iintro Hst
    imod Hmask with -
    imod Hstep $$ %st Hg HR with ⟨Hg, HQ⟩
    imod Hclose $$ [Hst Hg] with -
    · inext
      iexists { st with hasRecvDec := true }
      iframe Hst Hg
      iapply decInfo_eq γ s (st := st) (st' := { st with hasRecvDec := true }) rfl rfl $$ Hd
    imodintro
    iintro -
    iapply HΦ $$ HQ

/-- `HasEnoughMsg` with slot `s`'s invariant open (a ghost step `Hstep` on its state). -/
theorem wp_HasEnoughMsg_inv (hspec : Slot.HasEnoughMsg.spec (GF := GF)) (γ : Names) (k : Nat)
    (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : SlotV) (he : γl.slots[s]? = some e)
    (phase round : w32) (hr : round = 1 ∨ round = 2)
    (R : IProp GF) (Q : SlotSt → IProp GF) (Φ : val → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger ∗ isSlot e.loc e.γ e.q ∗ confRO cf ∗
      slotsInv γ cf k γl γc ∗ R ∗
      (∀ st, slotGhost γ cf k γl γc s st -∗ R ={⊤ \ ↑(slotN k s)}=∗
        slotGhost γ cf k γl γc s (st) ∗ Q st) ∗
      (∀ st, Q st -∗ Φ (#(decide (st.total phase.toNat round.toNat ≥ cf.q)))) ⊢
    WP (App (App (Val (e.loc @!! go.GoType.PointerType Slot.ty @!! go!"HasEnoughMsg")) (Val #phase)) (Val #round)) {{ Φ }} := by
  iintro ⟨#Hpkg, #Hslot, #Hconf, #Hinvs, HR, Hstep, HΦ⟩
  ihave #Hinv := slotsInv_lookup γ k γl γc s e he $$ Hinvs
  ihave Hspec := hspec cf e.loc e.γ e.q phase round hr $$ Hpkg Hslot Hconf
  iunfold atomic_wp at Hspec
  iapply Hspec
  rw [Std.LawfulSet.diff_empty]
  iauintro
  unfold atomic_acc
  iinv Hinv with Hi Hclose
  imod Hi with Hi
  unfold slotInv
  icases Hi with ⟨%st, Hst, #Hd, Hg⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists (⟨st, ⟨⟩⟩ : (Tele.cons fun _ : SlotSt => Tele.nil).Arg)
  dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM]
  iframe Hst
  isplit
  · iintro Hst
    imod Hmask with -
    imod Hclose $$ [Hst Hg] with -
    · inext
      iexists st
      iframe Hst Hg; iexact Hd
    imodintro
    iframe
  · iintro Hst
    imod Hmask with -
    imod Hstep $$ %st Hg HR with ⟨Hg, HQ⟩
    imod Hclose $$ [Hst Hg] with -
    · inext
      iexists st
      iframe Hst Hg
      iexact Hd
    imodintro
    iintro -
    iapply HΦ $$ HQ

/-- `RecvBCMsgsMajV` with slot `s`'s invariant open (a ghost step `Hstep` on its state). -/
theorem wp_RecvBCMsgsMajV_inv (hspec : Slot.RecvBCMsgsMajV.spec (GF := GF)) (γ : Names) (k : Nat)
    (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : SlotV) (he : γl.slots[s]? = some e)
    (phase round : w32) (hr : round = 1 ∨ round = 2)
    (R : IProp GF) (Q : SlotSt → IProp GF) (Φ : val → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger ∗ isSlot e.loc e.γ e.q ∗
      slotsInv γ cf k γl γc ∗ R ∗
      (∀ st, slotGhost γ cf k γl γc s st -∗ R ={⊤ \ ↑(slotN k s)}=∗
        slotGhost γ cf k γl γc s (st) ∗ Q st) ∗
      (∀ st, Q st -∗ Φ (#(W32 ((st.counts phase.toNat round.toNat).majV : Nat)))) ⊢
    WP (App (App (Val (e.loc @!! go.GoType.PointerType Slot.ty @!! go!"RecvBCMsgsMajV")) (Val #phase)) (Val #round)) {{ Φ }} := by
  iintro ⟨#Hpkg, #Hslot, #Hinvs, HR, Hstep, HΦ⟩
  ihave #Hinv := slotsInv_lookup γ k γl γc s e he $$ Hinvs
  ihave Hspec := hspec e.loc e.γ e.q phase round hr $$ Hpkg Hslot
  iunfold atomic_wp at Hspec
  iapply Hspec
  rw [Std.LawfulSet.diff_empty]
  iauintro
  unfold atomic_acc
  iinv Hinv with Hi Hclose
  imod Hi with Hi
  unfold slotInv
  icases Hi with ⟨%st, Hst, #Hd, Hg⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists (⟨st, ⟨⟩⟩ : (Tele.cons fun _ : SlotSt => Tele.nil).Arg)
  dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM]
  iframe Hst
  isplit
  · iintro Hst
    imod Hmask with -
    imod Hclose $$ [Hst Hg] with -
    · inext
      iexists st
      iframe Hst Hg; iexact Hd
    imodintro
    iframe
  · iintro Hst
    imod Hmask with -
    imod Hstep $$ %st Hg HR with ⟨Hg, HQ⟩
    imod Hclose $$ [Hst Hg] with -
    · inext
      iexists st
      iframe Hst Hg
      iexact Hd
    imodintro
    iintro -
    iapply HΦ $$ HQ

/-- `RecvBCMsgsMajT` with slot `s`'s invariant open (a ghost step `Hstep` on its state). -/
theorem wp_RecvBCMsgsMajT_inv (hspec : Slot.RecvBCMsgsMajT.spec (GF := GF)) (γ : Names) (k : Nat)
    (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : SlotV) (he : γl.slots[s]? = some e)
    (phase round : w32) (hr : round = 1 ∨ round = 2)
    (R : IProp GF) (Q : SlotSt → IProp GF) (Φ : val → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger ∗ isSlot e.loc e.γ e.q ∗
      slotsInv γ cf k γl γc ∗ R ∗
      (∀ st, slotGhost γ cf k γl γc s st -∗ R ={⊤ \ ↑(slotN k s)}=∗
        slotGhost γ cf k γl γc s (st) ∗ Q st) ∗
      (∀ st, Q st -∗ Φ (#(W64 ((st.counts phase.toNat round.toNat).majT : Nat)))) ⊢
    WP (App (App (Val (e.loc @!! go.GoType.PointerType Slot.ty @!! go!"RecvBCMsgsMajT")) (Val #phase)) (Val #round)) {{ Φ }} := by
  iintro ⟨#Hpkg, #Hslot, #Hinvs, HR, Hstep, HΦ⟩
  ihave #Hinv := slotsInv_lookup γ k γl γc s e he $$ Hinvs
  ihave Hspec := hspec e.loc e.γ e.q phase round hr $$ Hpkg Hslot
  iunfold atomic_wp at Hspec
  iapply Hspec
  rw [Std.LawfulSet.diff_empty]
  iauintro
  unfold atomic_acc
  iinv Hinv with Hi Hclose
  imod Hi with Hi
  unfold slotInv
  icases Hi with ⟨%st, Hst, #Hd, Hg⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists (⟨st, ⟨⟩⟩ : (Tele.cons fun _ : SlotSt => Tele.nil).Arg)
  dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM]
  iframe Hst
  isplit
  · iintro Hst
    imod Hmask with -
    imod Hclose $$ [Hst Hg] with -
    · inext
      iexists st
      iframe Hst Hg; iexact Hd
    imodintro
    iframe
  · iintro Hst
    imod Hmask with -
    imod Hstep $$ %st Hg HR with ⟨Hg, HQ⟩
    imod Hclose $$ [Hst Hg] with -
    · inext
      iexists st
      iframe Hst Hg
      iexact Hd
    imodintro
    iintro -
    iapply HΦ $$ HQ

/-- `RecvProposalsMajT` with slot `s`'s invariant open (a ghost step `Hstep` on its state). -/
theorem wp_RecvProposalsMajT_inv (hspec : Slot.RecvProposalsMajT.spec (GF := GF)) (γ : Names) (k : Nat)
    (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : SlotV) (he : γl.slots[s]? = some e)
    
    (R : IProp GF) (Q : SlotSt → IProp GF) (Φ : val → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger ∗ isSlot e.loc e.γ e.q ∗
      slotsInv γ cf k γl γc ∗ R ∗
      □ (∀ st, slotGhost γ cf k γl γc s st -∗ R -∗
        ⌜st.props ≠ []⌝ ∗ slotGhost γ cf k γl γc s st ∗ R) ∗
      (∀ st, slotGhost γ cf k γl γc s st -∗ R ={⊤ \ ↑(slotN k s)}=∗
        slotGhost γ cf k γl γc s ({ st with props := sortProps st.props }) ∗ Q st) ∗
      (∀ st (n : Nat), ⌜n = ((sortProps st.props).head?.map (·.2)).getD 0⌝ -∗ Q st -∗
        Φ (#(W64 (n : Nat)))) ⊢
    WP (App (Val (e.loc @!! go.GoType.PointerType Slot.ty @!! go!"RecvProposalsMajT")) (Val #())) {{ Φ }} := by
  iintro ⟨#Hpkg, #Hslot, #Hinvs, HR, #Hpre, Hstep, HΦ⟩
  ihave #Hinv := slotsInv_lookup γ k γl γc s e he $$ Hinvs
  ihave Hspec := hspec e.loc e.γ e.q  $$ Hpkg Hslot
  iunfold atomic_wp at Hspec
  iapply Hspec
  rw [Std.LawfulSet.diff_empty]
  iauintro
  unfold atomic_acc
  iinv Hinv with Hi Hclose
  imod Hi with Hi
  unfold slotInv
  icases Hi with ⟨%st, Hst, #Hd, Hg⟩
  ihave ⟨%hpre, Hg, HR⟩ := Hpre $$ %st Hg HR
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists (⟨st, ⟨⟩⟩ : (Tele.cons fun _ : SlotSt => Tele.nil).Arg)
  dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM]
  iframe Hst
  isplitr
  · ipureintro; exact hpre
  isplit
  · iintro ⟨Hst, -⟩
    imod Hmask with -
    imod Hclose $$ [Hst Hg] with -
    · inext
      iexists st
      iframe Hst Hg; iexact Hd
    imodintro
    iframe
  · iintro Hst
    imod Hmask with -
    imod Hstep $$ %st Hg HR with ⟨Hg, HQ⟩
    imod Hclose $$ [Hst Hg] with -
    · inext
      iexists { st with props := sortProps st.props }
      iframe Hst Hg
      iapply decInfo_eq γ s (st := st) (st' := { st with props := sortProps st.props }) rfl rfl $$ Hd
    imodintro
    iintro -
    iapply HΦ $$ %st %_ [] HQ
    ipureintro; rfl

/-- `PutRecvProposals` with slot `s`'s invariant open (a ghost step `Hstep` on its state). -/
theorem wp_PutRecvProposals_inv (hspec : Slot.PutRecvProposals.spec (GF := GF)) (γ : Names) (k : Nat)
    (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : SlotV) (he : γl.slots[s]? = some e)
    (v : ConsensusObj) (o : ObjV)
    (R : IProp GF) (Q : SlotSt → IProp GF) (Φ : val → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger ∗ isSlot e.loc e.γ e.q ∗ objRep v o ∗
      slotsInv γ cf k γl γc ∗ R ∗
      □ (∀ st, slotGhost γ cf k γl γc s st -∗ R -∗
        ⌜st.total 0 1 + 1 < 2 ^ 62⌝ ∗ slotGhost γ cf k γl γc s st ∗ R) ∗
      (∀ st, slotGhost γ cf k γl γc s st -∗ R ={⊤ \ ↑(slotN k s)}=∗
        slotGhost γ cf k γl γc s (st.addProp o) ∗ Q st) ∗
      (∀ st, Q st -∗ Φ (#())) ⊢
    WP (App (Val (e.loc @!! go.GoType.PointerType Slot.ty @!! go!"PutRecvProposals")) (Val #v)) {{ Φ }} := by
  iintro ⟨#Hpkg, #Hslot, #Hv, #Hinvs, HR, #Hpre, Hstep, HΦ⟩
  ihave #Hinv := slotsInv_lookup γ k γl γc s e he $$ Hinvs
  ihave Hspec := hspec e.loc e.γ e.q v o $$ Hpkg Hslot Hv
  iunfold atomic_wp at Hspec
  iapply Hspec
  rw [Std.LawfulSet.diff_empty]
  iauintro
  unfold atomic_acc
  iinv Hinv with Hi Hclose
  imod Hi with Hi
  unfold slotInv
  icases Hi with ⟨%st, Hst, #Hd, Hg⟩
  ihave ⟨%hpre, Hg, HR⟩ := Hpre $$ %st Hg HR
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists (⟨st, ⟨⟩⟩ : (Tele.cons fun _ : SlotSt => Tele.nil).Arg)
  dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM]
  iframe Hst
  isplitr
  · ipureintro; exact hpre
  isplit
  · iintro ⟨Hst, -⟩
    imod Hmask with -
    imod Hclose $$ [Hst Hg] with -
    · inext
      iexists st
      iframe Hst Hg; iexact Hd
    imodintro
    iframe
  · iintro Hst
    imod Hmask with -
    imod Hstep $$ %st Hg HR with ⟨Hg, HQ⟩
    imod Hclose $$ [Hst Hg] with -
    · inext
      iexists st.addProp o
      iframe Hst Hg
      iapply decInfo_eq γ s (st := st) (st' := st.addProp o) rfl rfl $$ Hd
    imodintro
    iintro -
    iapply HΦ $$ HQ

/-- `PutRecvBCMsgs` with slot `s`'s invariant open. -/
theorem wp_PutRecvBCMsgs_inv (hspec : Slot.PutRecvBCMsgs.spec (GF := GF)) (γ : Names) (k : Nat)
    (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : SlotV) (he : γl.slots[s]? = some e)
    (phase round x : w32) (hr : round = 1 ∨ round = 2) (hx : x.toNat ≤ 2)
    (R : IProp GF) (Q : IProp GF) (Φ : val → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger ∗ isSlot e.loc e.γ e.q ∗
      slotsInv γ cf k γl γc ∗ R ∗
      □ (∀ st, slotGhost γ cf k γl γc s st -∗ R -∗
        ⌜st.total phase.toNat round.toNat + 1 < 2 ^ 62⌝ ∗ slotGhost γ cf k γl γc s st ∗ R) ∗
      (∀ st, slotGhost γ cf k γl γc s st -∗ R ={⊤ \ ↑(slotN k s)}=∗
        slotGhost γ cf k γl γc s (st.put phase.toNat round.toNat x.toNat) ∗ Q) ∗
      (Q -∗ Φ #()) ⊢
    WP (App (App (App (Val (e.loc @!! go.GoType.PointerType Slot.ty @!! go!"PutRecvBCMsgs"))
        (Val #phase)) (Val #round)) (Val #x)) {{ Φ }} := by
  iintro ⟨#Hpkg, #Hslot, #Hinvs, HR, #Hpre, Hstep, HΦ⟩
  ihave #Hinv := slotsInv_lookup γ k γl γc s e he $$ Hinvs
  ihave Hspec := hspec e.loc e.γ e.q phase round x hr hx $$ Hpkg Hslot
  iunfold atomic_wp at Hspec
  iapply Hspec
  rw [Std.LawfulSet.diff_empty]
  iauintro
  unfold atomic_acc
  iinv Hinv with Hi Hclose
  imod Hi with Hi
  unfold slotInv
  icases Hi with ⟨%st, Hst, #Hd, Hg⟩
  ihave ⟨%hpre, Hg, HR⟩ := Hpre $$ %st Hg HR
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists (⟨st, ⟨⟩⟩ : (Tele.cons fun _ : SlotSt => Tele.nil).Arg)
  dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM]
  iframe Hst
  isplitr
  · ipureintro; exact hpre
  isplit
  · iintro ⟨Hst, -⟩
    imod Hmask with -
    imod Hclose $$ [Hst Hg] with -
    · inext
      iexists st
      iframe Hst Hg; iexact Hd
    imodintro
    iframe
  · iintro Hst
    imod Hmask with -
    imod Hstep $$ %st Hg HR with ⟨Hg, HQ⟩
    imod Hclose $$ [Hst Hg] with -
    · inext
      iexists st.put phase.toNat round.toNat x.toNat
      iframe Hst Hg
      iapply decInfo_eq γ s (st := st) (st' := st.put phase.toNat round.toNat x.toNat) rfl rfl $$ Hd
    imodintro
    iintro -
    iapply HΦ $$ HQ

/-- `RecvProposalsMajV` with slot `s`'s invariant open. -/
theorem wp_RecvProposalsMajV_inv (hspec : Slot.RecvProposalsMajV.spec (GF := GF)) (γ : Names)
    (k : Nat) (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : SlotV) (he : γl.slots[s]? = some e)
    (R : IProp GF) (Q : SlotSt → IProp GF) (Φ : val → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger ∗ isSlot e.loc e.γ e.q ∗
      slotsInv γ cf k γl γc ∗ R ∗
      □ (∀ st, slotGhost γ cf k γl γc s st -∗ R -∗
        ⌜st.props ≠ []⌝ ∗ slotGhost γ cf k γl γc s st ∗ R) ∗
      (∀ st, slotGhost γ cf k γl γc s st -∗ R ={⊤ \ ↑(slotN k s)}=∗
        slotGhost γ cf k γl γc s { st with props := sortProps st.props } ∗ Q st) ∗
      (∀ st (v : ConsensusObj), objRep v ((sortProps st.props).head?.map (·.1)).get! -∗ Q st -∗
        Φ #v) ⊢
    WP (App (Val (e.loc @!! go.GoType.PointerType Slot.ty @!! go!"RecvProposalsMajV")) (Val #()))
      {{ Φ }} := by
  iintro ⟨#Hpkg, #Hslot, #Hinvs, HR, #Hpre, Hstep, HΦ⟩
  ihave #Hinv := slotsInv_lookup γ k γl γc s e he $$ Hinvs
  ihave Hspec := hspec e.loc e.γ e.q $$ Hpkg Hslot
  iunfold atomic_wp at Hspec
  iapply Hspec
  rw [Std.LawfulSet.diff_empty]
  iauintro
  unfold atomic_acc
  iinv Hinv with Hi Hclose
  imod Hi with Hi
  unfold slotInv
  icases Hi with ⟨%st, Hst, #Hd, Hg⟩
  ihave ⟨%hpre, Hg, HR⟩ := Hpre $$ %st Hg HR
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists (⟨st, ⟨⟩⟩ : (Tele.cons fun _ : SlotSt => Tele.nil).Arg)
  dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM]
  iframe Hst
  isplitr
  · ipureintro; exact hpre
  isplit
  · iintro ⟨Hst, -⟩
    imod Hmask with -
    imod Hclose $$ [Hst Hg] with -
    · inext
      iexists st
      iframe Hst Hg; iexact Hd
    imodintro
    iframe
  · iintro Hst
    imod Hmask with -
    imod Hstep $$ %st Hg HR with ⟨Hg, HQ⟩
    imod Hclose $$ [Hst Hg] with -
    · inext
      iexists { st with props := sortProps st.props }
      iframe Hst Hg
      iapply decInfo_eq γ s (st := st) (st' := { st with props := sortProps st.props }) rfl rfl $$ Hd
    imodintro
    iintro %v Hv
    iapply HΦ $$ %st %v Hv HQ

/-- `SetDecision` with slot `s`'s invariant open (the step gives the new state's `decInfo`). -/
theorem wp_SetDecision_inv (hspec : Slot.SetDecision.spec (GF := GF)) (γ : Names)
    (k : Nat) (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : SlotV) (he : γl.slots[s]? = some e)
    (v : ConsensusObj) (o : ObjV) (R : IProp GF) (Q : SlotSt → IProp GF) (Φ : val → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger ∗ isSlot e.loc e.γ e.q ∗ objRep v o ∗
      slotsInv γ cf k γl γc ∗ R ∗
      (∀ st, slotGhost γ cf k γl γc s st -∗ R ={⊤ \ ↑(slotN k s)}=∗
        slotGhost γ cf k γl γc s { st with isDone := true, decision := o } ∗
        decInfo γ cf s { st with isDone := true, decision := o } ∗ Q st) ∗
      (∀ st, Q st -∗ Φ #()) ⊢
    WP (App (Val (e.loc @!! go.GoType.PointerType Slot.ty @!! go!"SetDecision")) (Val #v))
      {{ Φ }} := by
  iintro ⟨#Hpkg, #Hslot, #Hv, #Hinvs, HR, Hstep, HΦ⟩
  ihave #Hinv := slotsInv_lookup γ k γl γc s e he $$ Hinvs
  ihave Hspec := hspec e.loc e.γ e.q v o $$ Hpkg Hslot Hv
  iunfold atomic_wp at Hspec
  iapply Hspec
  rw [Std.LawfulSet.diff_empty]
  iauintro
  unfold atomic_acc
  iinv Hinv with Hi Hclose
  imod Hi with Hi
  unfold slotInv
  icases Hi with ⟨%st, Hst, #Hd, Hg⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists (⟨st, ⟨⟩⟩ : (Tele.cons fun _ : SlotSt => Tele.nil).Arg)
  dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM]
  iframe Hst
  isplit
  · iintro Hst
    imod Hmask with -
    imod Hclose $$ [Hst Hg] with -
    · inext
      iexists st
      iframe Hst Hg; iexact Hd
    imodintro
    iframe
  · iintro Hst
    imod Hmask with -
    imod Hstep $$ %st Hg HR with ⟨Hg, #Hd', HQ⟩
    imod Hclose $$ [Hst Hg] with -
    · inext
      iexists { st with isDone := true, decision := o }
      iframe Hst Hg; iexact Hd'
    imodintro
    iintro -
    iapply HΦ $$ HQ

end acc

end Perennial.rabia.roles.server.layers.consensus
