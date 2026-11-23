/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Wire/Proof/State.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# U1: `state`'s `Key`, `Value`, `Command`: `Marshal` (the general form `wp_Marshal_gen`, over
`wst`) and `Unmarshal`.
-/
module

public import Dsverify.Proof.gryff.Wire.Proof.Lemmas
public import Dsverify.Proof.gryff.src.state.Base
public import Dsverify.Proof.gryff.src.gryffproto.Base
public import Dsverify.Proof.gryff.src.epaxosproto.Base
public import Dsverify.Proof.gryff.src.clientproto.Base
public import Dsverify.Proof.gryff.src.genericsmrproto.Base

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
variable [src.state.Assumptions]

namespace state

theorem Key.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : Key.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.state ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ Key.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ t ↦{dq} m }}
      (App (Val (t @!! go.GoType.PointerType src.state.Key.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ Key.enc m) ∗ t ↦{dq} m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  wp_auto
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 8 - W64 0 = W64 8 from rfl]
  ihave Hb := slice_array (GF := GF) b_ptr _ _ (by decide) $$ b
  wp_apply encoding.binary.wp_LittleEndian_PutUint64 _ (zero_val (GoArray w8 8)).arr [] _ (by rfl) $$ [Hb] as Hb
  · simp only [List.append_nil]; iexact Hb
  simp only [List.append_nil]
  wp_apply wp_wire_Write $$ [$Hwr $HQ $Hw $Hb] as %nn %e ⟨Hw, Hb⟩
  · ipureintro; exact Hpre
  iapply HΦ
  simp only [Key.enc]
  iframe

theorem Command.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : Command.Msg) (bw : Loc)
    (wr : WSt GF) (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface)
    (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.state ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ Command.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ t ↦{dq} m }}
      (App (Val (t @!! go.GoType.PointerType src.state.Command.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ Command.enc m) ∗ t ↦{dq} m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  wp_auto
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 25 - W64 0 = W64 25 from rfl]
  ihave Hb := slice_array (GF := GF) b_ptr _ _ (by decide) $$ b
  (try wp_auto)
  repeat u1_wstore
  u1_buf_norm
  u1_marshal_write
  u1_marshal_finish

theorem Value.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : Value.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.state ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ Value.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ t ↦{dq} m }}
      (App (Val (t @!! go.GoType.PointerType src.state.Value.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ Value.enc m) ∗ t ↦{dq} m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  wp_auto
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 8 - W64 0 = W64 8 from rfl]
  ihave Hb := slice_array (GF := GF) b_ptr _ _ (by decide) $$ b
  wp_apply encoding.binary.wp_LittleEndian_PutUint64 _ (zero_val (GoArray w8 8)).arr [] _ (by rfl) $$ [Hb] as Hb
  · simp only [List.append_nil]; iexact Hb
  simp only [List.append_nil]
  wp_apply wp_wire_Write $$ [$Hwr $HQ $Hw $Hb] as %nn %e ⟨Hw, Hb⟩
  · ipureintro; exact Hpre
  iapply HΦ
  simp only [Value.enc]
  iframe

theorem Key.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : Key.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.state ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Key.enc m) ∗
        Key.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.state.Key.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Key.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Key.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Key.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Key.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen Key.wp_Marshal_gen

theorem Value.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : Value.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.state ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Value.enc m) ∗
        Value.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.state.Value.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Value.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Value.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Value.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Value.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen Value.wp_Marshal_gen

theorem Command.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : Command.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.state ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Command.enc m) ∗
        Command.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.state.Command.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Command.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Command.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Command.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Command.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen Command.wp_Marshal_gen

end state
end proofs

section uproofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [bufio.Assumptions] [io.Assumptions] [encoding.binary.Assumptions] [wire.BufioSpecs GF]
variable [src.state.Assumptions]

namespace state

theorem Key.wp_Unmarshal_proof (t : Loc) (v0 : src.state.Key) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.state ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Key.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.state.Key.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Key.Msg, ⌜Key.wf m⌝ ∗
          Key.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Key.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.state.Key) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, -, Hown, Ht⟩
  wp_auto
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 8 - W64 0 = W64 8 from rfl]
  ihave Hb := slice_array (GF := GF) b_ptr _ _ (by decide) $$ b
  wp_apply wp_wire_ReadFull $$ [$Hrd $Hown $Hb] as %nr %err ⟨%data, Hown, Hr⟩
  icases Hr with (⟨⟨%Hnil, %Hlen⟩, Hb⟩ | ⟨%Hne, #Ha, %vs', Hb⟩)
  · subst Hnil
    wp_auto
    have hl : data.length = 8 := by simpa using Hlen
    wp_apply encoding.binary.wp_LittleEndian_Uint64 _ data _ [] hl $$ [Hb] as Hb
    · simp only [List.append_nil]; iexact Hb
    wp_pure
    wp_auto
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists _
    iframe Ht
    isplitr
    · ipureintro; trivial
    iapply ownReader_app_eq _ _ _ _ _ _ ?_ $$ Hown
    simp only [Key.enc, leToU64_le _ hl]
  · rcases err with ei | _
    · wp_auto
      iapply HΦ
      iright
      iframe Ha
      isplitr
      · ipureintro; exact Hne
      iexists v0, data
      iframe Ht Hown
    · exact absurd rfl Hne

theorem Value.wp_Unmarshal_proof (t : Loc) (v0 : src.state.Value) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.state ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Value.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.state.Value.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Value.Msg, ⌜Value.wf m⌝ ∗
          Value.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Value.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.state.Value) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, -, Hown, Ht⟩
  wp_auto
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 8 - W64 0 = W64 8 from rfl]
  ihave Hb := slice_array (GF := GF) b_ptr _ _ (by decide) $$ b
  wp_apply wp_wire_ReadFull $$ [$Hrd $Hown $Hb] as %nr %err ⟨%data, Hown, Hr⟩
  icases Hr with (⟨⟨%Hnil, %Hlen⟩, Hb⟩ | ⟨%Hne, #Ha, %vs', Hb⟩)
  · subst Hnil
    wp_auto
    have hl : data.length = 8 := by simpa using Hlen
    wp_apply encoding.binary.wp_LittleEndian_Uint64 _ data _ [] hl $$ [Hb] as Hb
    · simp only [List.append_nil]; iexact Hb
    wp_pure
    wp_auto
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists _
    iframe Ht
    isplitr
    · ipureintro; trivial
    iapply ownReader_app_eq _ _ _ _ _ _ ?_ $$ Hown
    simp only [Value.enc, leToU64_le _ hl]
  · rcases err with ei | _
    · wp_auto
      iapply HΦ
      iright
      iframe Ha
      isplitr
      · ipureintro; exact Hne
      iexists v0, data
      iframe Ht Hown
    · exact absurd rfl Hne

theorem Command.wp_Unmarshal_proof (t : Loc) (v0 : src.state.Command) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.state ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Command.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.state.Command.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Command.Msg, ⌜Command.wf m⌝ ∗
          Command.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Command.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.state.Command) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, -, Hown, Ht⟩
  wp_auto
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 25 - W64 0 = W64 25 from rfl]
  ihave Hb := slice_array (GF := GF) b_ptr _ _ (by decide) $$ b
  wp_apply wp_wire_ReadAtLeast $$ [$Hrd $Hown $Hb] as %nr %err ⟨%data, Hown, Hr⟩
  icases Hr with (⟨⟨%Hnil, %Hlen⟩, Hb⟩ | ⟨%Hne, #Ha, %vs', Hb⟩)
  · subst Hnil
    wp_auto
    repeat u1_wload
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists _
    iframe Ht
    isplitr
    · ipureintro; trivial
    have hl : data.length = 25 := by simpa using Hlen
    iapply ownReader_app_eq _ _ _ _ _ _ ?_ $$ Hown
    u1_dec_tac hl
  · rcases err with ei | _
    · wp_auto
      iapply HΦ
      iright
      iframe Ha
      isplitr
      · ipureintro; exact Hne
      iexists v0, data
      iframe Ht Hown
    · exact absurd rfl Hne

end state
end uproofs
end Perennial.gryff.wire
