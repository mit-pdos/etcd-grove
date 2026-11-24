/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Wire/Proof/Client.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# U1: `clientproto`'s messages: `Marshal` (general form and frozen statement) and `Unmarshal`.
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
variable [bufio.Assumptions] [io.Assumptions] [encoding.binary.Assumptions] [wire.BufioSpecs GF]
variable [src.state.Assumptions] [src.gryffproto.Assumptions] [src.epaxosproto.Assumptions]
variable [src.clientproto.Assumptions] [src.genericsmrproto.Assumptions]

namespace clientproto

theorem Ping.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : Ping.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.clientproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ Ping.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ t ↦{dq} m }}
      (App (Val (t @!! go.GoType.PointerType src.clientproto.Ping.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ Ping.enc m) ∗ t ↦{dq} m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  u1_marshal_auto
  u1_marshal_finish

theorem PingReply.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : PingReply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.clientproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ PingReply.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ t ↦{dq} m }}
      (App (Val (t @!! go.GoType.PointerType src.clientproto.PingReply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ PingReply.enc m) ∗ t ↦{dq} m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  u1_marshal_auto
  u1_marshal_finish

theorem Ping.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : Ping.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.clientproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Ping.enc m) ∗
        Ping.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.clientproto.Ping.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Ping.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Ping.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Ping.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Ping.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen Ping.wp_Marshal_gen

theorem PingReply.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : PingReply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.clientproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ PingReply.enc m) ∗
        PingReply.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.clientproto.PingReply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (PingReply.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (PingReply.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (PingReply.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        PingReply.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen PingReply.wp_Marshal_gen
end clientproto
end proofs
section uproofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [bufio.Assumptions] [io.Assumptions] [encoding.binary.Assumptions] [wire.BufioSpecs GF]
variable [src.state.Assumptions] [src.gryffproto.Assumptions] [src.epaxosproto.Assumptions]
variable [src.clientproto.Assumptions] [src.genericsmrproto.Assumptions]

namespace clientproto

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem Ping.wp_Unmarshal_proof (t : Loc) (v0 : src.clientproto.Ping) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.clientproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Ping.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.clientproto.Ping.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Ping.Msg, ⌜Ping.wf m⌝ ∗
          Ping.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Ping.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.clientproto.Ping) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, -, Hown, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  wp_auto
  u1_unmarshal_auto (src.clientproto.Ping.mk _ _)
  icases pt_name _ _ _ $$ ClientId with ⟨%xClientId, ClientId, %hxClientId⟩
  icases pt_name _ _ _ $$ Ts with ⟨%xTs, Ts, %hxTs⟩
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists (src.clientproto.Ping.mk xClientId xTs)
  isplitr
  · ipureintro; trivial
  isplitl [ClientId Ts]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply ownReader_eq _ _ _ _ _ ?_ $$ Hown
  subst_vars
  u1_dec_norm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem PingReply.wp_Unmarshal_proof (t : Loc) (v0 : src.clientproto.PingReply) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.clientproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R PingReply.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.clientproto.PingReply.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : PingReply.Msg, ⌜PingReply.wf m⌝ ∗
          PingReply.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ PingReply.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.clientproto.PingReply) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, -, Hown, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  wp_auto
  u1_unmarshal_auto (src.clientproto.PingReply.mk _ _)
  icases pt_name _ _ _ $$ ReplicaId with ⟨%xReplicaId, ReplicaId, %hxReplicaId⟩
  icases pt_name _ _ _ $$ Ts with ⟨%xTs, Ts, %hxTs⟩
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists (src.clientproto.PingReply.mk xReplicaId xTs)
  isplitr
  · ipureintro; trivial
  isplitl [ReplicaId Ts]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply ownReader_eq _ _ _ _ _ ?_ $$ Hown
  subst_vars
  u1_dec_norm



end clientproto
end uproofs
end Perennial.gryff.wire
