/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Wire/Proof/Genericsmr.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# U1: `genericsmrproto`'s messages: `Marshal` (general form and frozen statement) and `Unmarshal`.
-/
module

public import Dsverify.Proof.gryff.Wire.Proof.Gryff1

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.wire

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [bufio.Assumptions] [io.Assumptions] [encoding.binary.Assumptions]
variable [src.state.Assumptions] [src.gryffproto.Assumptions] [src.epaxosproto.Assumptions]
variable [src.clientproto.Assumptions] [src.genericsmrproto.Assumptions]

namespace genericsmrproto

theorem Beacon.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : Beacon.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmrproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ Beacon.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ t ↦{dq} m }}
      (App (Val (t @!! go.GoType.PointerType src.genericsmrproto.Beacon.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ Beacon.enc m) ∗ t ↦{dq} m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  u1_marshal_auto
  u1_marshal_finish

theorem BeaconReply.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : BeaconReply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmrproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ BeaconReply.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ t ↦{dq} m }}
      (App (Val (t @!! go.GoType.PointerType src.genericsmrproto.BeaconReply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ BeaconReply.enc m) ∗ t ↦{dq} m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  u1_marshal_auto
  u1_marshal_finish

theorem Propose.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : Propose.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmrproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ Propose.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ t ↦{dq} m }}
      (App (Val (t @!! go.GoType.PointerType src.genericsmrproto.Propose.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ Propose.enc m) ∗ t ↦{dq} m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  u1_marshal_auto
  u1_marshal_finish

theorem ProposeReplyTS.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : ProposeReplyTS.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmrproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ ProposeReplyTS.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ t ↦{dq} m }}
      (App (Val (t @!! go.GoType.PointerType src.genericsmrproto.ProposeReplyTS.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ ProposeReplyTS.enc m) ∗ t ↦{dq} m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  u1_marshal_auto
  u1_marshal_finish

theorem Beacon.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : Beacon.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmrproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Beacon.enc m) ∗
        Beacon.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.genericsmrproto.Beacon.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Beacon.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Beacon.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Beacon.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Beacon.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen Beacon.wp_Marshal_gen

theorem BeaconReply.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : BeaconReply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmrproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ BeaconReply.enc m) ∗
        BeaconReply.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.genericsmrproto.BeaconReply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (BeaconReply.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (BeaconReply.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (BeaconReply.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        BeaconReply.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen BeaconReply.wp_Marshal_gen

theorem Propose.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : Propose.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmrproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Propose.enc m) ∗
        Propose.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.genericsmrproto.Propose.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Propose.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Propose.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Propose.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Propose.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen Propose.wp_Marshal_gen

theorem ProposeReplyTS.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : ProposeReplyTS.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmrproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ ProposeReplyTS.enc m) ∗
        ProposeReplyTS.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.genericsmrproto.ProposeReplyTS.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (ProposeReplyTS.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (ProposeReplyTS.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (ProposeReplyTS.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        ProposeReplyTS.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen ProposeReplyTS.wp_Marshal_gen
end genericsmrproto
end proofs
section uproofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [bufio.Assumptions] [io.Assumptions] [encoding.binary.Assumptions]
variable [src.state.Assumptions] [src.gryffproto.Assumptions] [src.epaxosproto.Assumptions]
variable [src.clientproto.Assumptions] [src.genericsmrproto.Assumptions]

namespace genericsmrproto

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem Beacon.wp_Unmarshal_proof (t : Loc) (v0 : src.genericsmrproto.Beacon) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmrproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Beacon.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.genericsmrproto.Beacon.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Beacon.Msg, ⌜Beacon.wf m⌝ ∗
          Beacon.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Beacon.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.genericsmrproto.Beacon) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, -, Hown, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  wp_auto
  u1_unmarshal_auto (src.genericsmrproto.Beacon.mk _)
  icases pt_name _ _ _ $$ Timestamp with ⟨%xTimestamp, Timestamp, %hxTimestamp⟩
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists (src.genericsmrproto.Beacon.mk xTimestamp)
  isplitr
  · ipureintro; trivial
  isplitl [Timestamp]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply ownReader_eq _ _ _ _ _ ?_ $$ Hown
  subst_vars
  u1_dec_norm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem BeaconReply.wp_Unmarshal_proof (t : Loc) (v0 : src.genericsmrproto.BeaconReply) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmrproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R BeaconReply.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.genericsmrproto.BeaconReply.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : BeaconReply.Msg, ⌜BeaconReply.wf m⌝ ∗
          BeaconReply.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ BeaconReply.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.genericsmrproto.BeaconReply) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, -, Hown, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  wp_auto
  u1_unmarshal_auto (src.genericsmrproto.BeaconReply.mk _)
  icases pt_name _ _ _ $$ Timestamp with ⟨%xTimestamp, Timestamp, %hxTimestamp⟩
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists (src.genericsmrproto.BeaconReply.mk xTimestamp)
  isplitr
  · ipureintro; trivial
  isplitl [Timestamp]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply ownReader_eq _ _ _ _ _ ?_ $$ Hown
  subst_vars
  u1_dec_norm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem Propose.wp_Unmarshal_proof (t : Loc) (v0 : src.genericsmrproto.Propose) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmrproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Propose.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.genericsmrproto.Propose.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Propose.Msg, ⌜Propose.wf m⌝ ∗
          Propose.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Propose.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.genericsmrproto.Propose) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, -, Hown, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  wp_auto
  u1_unmarshal_auto (src.genericsmrproto.Propose.mk _ _ _)
  icases pt_name _ _ _ $$ CommandId with ⟨%xCommandId, CommandId, %hxCommandId⟩
  icases pt_name _ _ _ $$ Command with ⟨%xCommand, Command, %hxCommand⟩
  icases pt_name _ _ _ $$ Timestamp with ⟨%xTimestamp, Timestamp, %hxTimestamp⟩
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists (src.genericsmrproto.Propose.mk xCommandId xCommand xTimestamp)
  isplitr
  · ipureintro; trivial
  isplitl [CommandId Command Timestamp]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply ownReader_eq _ _ _ _ _ ?_ $$ Hown
  subst_vars
  u1_dec_norm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ProposeReplyTS.wp_Unmarshal_proof (t : Loc) (v0 : src.genericsmrproto.ProposeReplyTS) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmrproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R ProposeReplyTS.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.genericsmrproto.ProposeReplyTS.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : ProposeReplyTS.Msg, ⌜ProposeReplyTS.wf m⌝ ∗
          ProposeReplyTS.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ ProposeReplyTS.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.genericsmrproto.ProposeReplyTS) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, -, Hown, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  wp_auto
  u1_unmarshal_auto (src.genericsmrproto.ProposeReplyTS.mk _ _ _ _)
  icases pt_name _ _ _ $$ OK with ⟨%xOK, OK, %hxOK⟩
  icases pt_name _ _ _ $$ CommandId with ⟨%xCommandId, CommandId, %hxCommandId⟩
  icases pt_name _ _ _ $$ Value with ⟨%xValue, Value, %hxValue⟩
  icases pt_name _ _ _ $$ Timestamp with ⟨%xTimestamp, Timestamp, %hxTimestamp⟩
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists (src.genericsmrproto.ProposeReplyTS.mk xOK xCommandId xValue xTimestamp)
  isplitr
  · ipureintro; trivial
  isplitl [OK CommandId Value Timestamp]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply ownReader_eq _ _ _ _ _ ?_ $$ Hown
  subst_vars
  u1_dec_norm



end genericsmrproto
end uproofs
end Perennial.gryff.wire
