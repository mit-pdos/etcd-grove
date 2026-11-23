/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Wire/Proof/Epaxos.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# U1: `epaxosproto`'s messages: `Marshal` (general form and frozen statement) and `Unmarshal`.
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

namespace epaxosproto

theorem Prepare.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : Prepare.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.epaxosproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ Prepare.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ t ↦{dq} m }}
      (App (Val (t @!! go.GoType.PointerType src.epaxosproto.Prepare.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ Prepare.enc m) ∗ t ↦{dq} m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  u1_marshal_auto
  u1_marshal_finish

theorem PreAcceptOK.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : PreAcceptOK.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.epaxosproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ PreAcceptOK.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ t ↦{dq} m }}
      (App (Val (t @!! go.GoType.PointerType src.epaxosproto.PreAcceptOK.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ PreAcceptOK.enc m) ∗ t ↦{dq} m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  u1_marshal_auto
  u1_marshal_finish

theorem AcceptReply.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : AcceptReply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.epaxosproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ AcceptReply.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ t ↦{dq} m }}
      (App (Val (t @!! go.GoType.PointerType src.epaxosproto.AcceptReply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ AcceptReply.enc m) ∗ t ↦{dq} m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  u1_marshal_auto
  u1_marshal_finish

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem CommitShort.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : CommitShort.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.epaxosproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ CommitShort.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ t ↦{dq} m }}
      (App (Val (t @!! go.GoType.PointerType src.epaxosproto.CommitShort.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ CommitShort.enc m) ∗ t ↦{dq} m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  u1_marshal_auto
  u1_marshal_finish

theorem TryPreAcceptReply.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : TryPreAcceptReply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.epaxosproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ TryPreAcceptReply.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ t ↦{dq} m }}
      (App (Val (t @!! go.GoType.PointerType src.epaxosproto.TryPreAcceptReply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ TryPreAcceptReply.enc m) ∗ t ↦{dq} m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  u1_marshal_auto
  u1_marshal_finish

theorem Prepare.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : Prepare.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.epaxosproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Prepare.enc m) ∗
        Prepare.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.epaxosproto.Prepare.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Prepare.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Prepare.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Prepare.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Prepare.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen Prepare.wp_Marshal_gen

theorem PreAcceptOK.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : PreAcceptOK.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.epaxosproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ PreAcceptOK.enc m) ∗
        PreAcceptOK.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.epaxosproto.PreAcceptOK.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (PreAcceptOK.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (PreAcceptOK.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (PreAcceptOK.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        PreAcceptOK.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen PreAcceptOK.wp_Marshal_gen

theorem AcceptReply.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : AcceptReply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.epaxosproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ AcceptReply.enc m) ∗
        AcceptReply.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.epaxosproto.AcceptReply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (AcceptReply.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (AcceptReply.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (AcceptReply.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        AcceptReply.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen AcceptReply.wp_Marshal_gen

theorem CommitShort.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : CommitShort.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.epaxosproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ CommitShort.enc m) ∗
        CommitShort.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.epaxosproto.CommitShort.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (CommitShort.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (CommitShort.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (CommitShort.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        CommitShort.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen CommitShort.wp_Marshal_gen

theorem TryPreAcceptReply.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : TryPreAcceptReply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.epaxosproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ TryPreAcceptReply.enc m) ∗
        TryPreAcceptReply.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.epaxosproto.TryPreAcceptReply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (TryPreAcceptReply.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (TryPreAcceptReply.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (TryPreAcceptReply.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        TryPreAcceptReply.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen TryPreAcceptReply.wp_Marshal_gen
end epaxosproto
end proofs
section uproofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [bufio.Assumptions] [io.Assumptions] [encoding.binary.Assumptions]
variable [src.state.Assumptions] [src.gryffproto.Assumptions] [src.epaxosproto.Assumptions]
variable [src.clientproto.Assumptions] [src.genericsmrproto.Assumptions]

namespace epaxosproto

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem Prepare.wp_Unmarshal_proof (t : Loc) (v0 : src.epaxosproto.Prepare) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.epaxosproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Prepare.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.epaxosproto.Prepare.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Prepare.Msg, ⌜Prepare.wf m⌝ ∗
          Prepare.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Prepare.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.epaxosproto.Prepare) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, -, Hown, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  wp_auto
  u1_unmarshal_auto (src.epaxosproto.Prepare.mk _ _ _ _)
  icases pt_name _ _ _ $$ LeaderId with ⟨%xLeaderId, LeaderId, %hxLeaderId⟩
  icases pt_name _ _ _ $$ Replica with ⟨%xReplica, Replica, %hxReplica⟩
  icases pt_name _ _ _ $$ Instance with ⟨%xInstance, Instance, %hxInstance⟩
  icases pt_name _ _ _ $$ Ballot with ⟨%xBallot, Ballot, %hxBallot⟩
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists (src.epaxosproto.Prepare.mk xLeaderId xReplica xInstance xBallot)
  isplitr
  · ipureintro; trivial
  isplitl [LeaderId Replica Instance Ballot]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply ownReader_eq _ _ _ _ _ ?_ $$ Hown
  subst_vars
  u1_dec_norm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem PreAcceptOK.wp_Unmarshal_proof (t : Loc) (v0 : src.epaxosproto.PreAcceptOK) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.epaxosproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R PreAcceptOK.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.epaxosproto.PreAcceptOK.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : PreAcceptOK.Msg, ⌜PreAcceptOK.wf m⌝ ∗
          PreAcceptOK.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ PreAcceptOK.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.epaxosproto.PreAcceptOK) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, -, Hown, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  wp_auto
  u1_unmarshal_auto (src.epaxosproto.PreAcceptOK.mk _)
  icases pt_name _ _ _ $$ Instance with ⟨%xInstance, Instance, %hxInstance⟩
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists (src.epaxosproto.PreAcceptOK.mk xInstance)
  isplitr
  · ipureintro; trivial
  isplitl [Instance]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply ownReader_eq _ _ _ _ _ ?_ $$ Hown
  subst_vars
  u1_dec_norm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem AcceptReply.wp_Unmarshal_proof (t : Loc) (v0 : src.epaxosproto.AcceptReply) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.epaxosproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R AcceptReply.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.epaxosproto.AcceptReply.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : AcceptReply.Msg, ⌜AcceptReply.wf m⌝ ∗
          AcceptReply.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ AcceptReply.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.epaxosproto.AcceptReply) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, -, Hown, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  wp_auto
  u1_unmarshal_auto (src.epaxosproto.AcceptReply.mk _ _ _ _)
  icases pt_name _ _ _ $$ Replica with ⟨%xReplica, Replica, %hxReplica⟩
  icases pt_name _ _ _ $$ Instance with ⟨%xInstance, Instance, %hxInstance⟩
  icases pt_name _ _ _ $$ OK with ⟨%xOK, OK, %hxOK⟩
  icases pt_name _ _ _ $$ Ballot with ⟨%xBallot, Ballot, %hxBallot⟩
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists (src.epaxosproto.AcceptReply.mk xReplica xInstance xOK xBallot)
  isplitr
  · ipureintro; trivial
  isplitl [Replica Instance OK Ballot]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply ownReader_eq _ _ _ _ _ ?_ $$ Hown
  subst_vars
  u1_dec_norm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem CommitShort.wp_Unmarshal_proof (t : Loc) (v0 : src.epaxosproto.CommitShort) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.epaxosproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R CommitShort.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.epaxosproto.CommitShort.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : CommitShort.Msg, ⌜CommitShort.wf m⌝ ∗
          CommitShort.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ CommitShort.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.epaxosproto.CommitShort) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, -, Hown, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  wp_auto
  u1_unmarshal_auto (src.epaxosproto.CommitShort.mk _ _ _ _ _ _)
  ihave %HdlDeps := array_len _ _ _ _ $$ Deps
  icases pt_name _ _ _ $$ LeaderId with ⟨%xLeaderId, LeaderId, %hxLeaderId⟩
  icases pt_name _ _ _ $$ Replica with ⟨%xReplica, Replica, %hxReplica⟩
  icases pt_name _ _ _ $$ Instance with ⟨%xInstance, Instance, %hxInstance⟩
  icases pt_name _ _ _ $$ Count with ⟨%xCount, Count, %hxCount⟩
  icases pt_name _ _ _ $$ Seq with ⟨%xSeq, Seq, %hxSeq⟩
  icases pt_name _ _ _ $$ Deps with ⟨%xDeps, Deps, %hxDeps⟩
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists (src.epaxosproto.CommitShort.mk xLeaderId xReplica xInstance xCount xSeq xDeps)
  isplitr
  · ipureintro; trivial
  isplitl [LeaderId Replica Instance Count Seq Deps]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply ownReader_eq _ _ _ _ _ ?_ $$ Hown
  subst_vars
  simp only [List.length_set] at HdlDeps
  rw [set5 v0.Deps'.arr (by omega)]
  u1_dec_norm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem TryPreAcceptReply.wp_Unmarshal_proof (t : Loc) (v0 : src.epaxosproto.TryPreAcceptReply) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.epaxosproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R TryPreAcceptReply.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.epaxosproto.TryPreAcceptReply.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : TryPreAcceptReply.Msg, ⌜TryPreAcceptReply.wf m⌝ ∗
          TryPreAcceptReply.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ TryPreAcceptReply.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.epaxosproto.TryPreAcceptReply) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, -, Hown, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  wp_auto
  u1_unmarshal_auto (src.epaxosproto.TryPreAcceptReply.mk _ _ _ _ _ _ _ _)
  icases pt_name _ _ _ $$ AcceptorId with ⟨%xAcceptorId, AcceptorId, %hxAcceptorId⟩
  icases pt_name _ _ _ $$ Replica with ⟨%xReplica, Replica, %hxReplica⟩
  icases pt_name _ _ _ $$ Instance with ⟨%xInstance, Instance, %hxInstance⟩
  icases pt_name _ _ _ $$ OK with ⟨%xOK, OK, %hxOK⟩
  icases pt_name _ _ _ $$ Ballot with ⟨%xBallot, Ballot, %hxBallot⟩
  icases pt_name _ _ _ $$ ConflictReplica with ⟨%xConflictReplica, ConflictReplica, %hxConflictReplica⟩
  icases pt_name _ _ _ $$ ConflictInstance with ⟨%xConflictInstance, ConflictInstance, %hxConflictInstance⟩
  icases pt_name _ _ _ $$ ConflictStatus with ⟨%xConflictStatus, ConflictStatus, %hxConflictStatus⟩
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists (src.epaxosproto.TryPreAcceptReply.mk xAcceptorId xReplica xInstance xOK xBallot xConflictReplica xConflictInstance xConflictStatus)
  isplitr
  · ipureintro; trivial
  isplitl [AcceptorId Replica Instance OK Ballot ConflictReplica ConflictInstance ConflictStatus]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply ownReader_eq _ _ _ _ _ ?_ $$ Hown
  subst_vars
  u1_dec_norm



end epaxosproto
end uproofs
end Perennial.gryff.wire
