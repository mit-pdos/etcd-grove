/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Wire/Proof/Gryff2.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# U1: `gryffproto`'s fixed-size messages: `Unmarshal`.
-/
module

public import Dsverify.Proof.gryff.Wire.Proof.Gryff1

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.wire

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section uproofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [bufio.Assumptions] [io.Assumptions] [encoding.binary.Assumptions]
variable [src.state.Assumptions] [src.gryffproto.Assumptions] [src.epaxosproto.Assumptions]
variable [src.clientproto.Assumptions] [src.genericsmrproto.Assumptions]

namespace gryffproto

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem Read.wp_Unmarshal_proof (t : Loc) (v0 : src.gryffproto.Read) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Read.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Read.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Read.Msg, ⌜Read.wf m⌝ ∗
          Read.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Read.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.Read) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, -, Hown, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  wp_auto
  u1_unmarshal_auto (src.gryffproto.Read.mk _ _ _ _)
  icases pt_name _ _ _ $$ RequestId with ⟨%xRequestId, RequestId, %hxRequestId⟩
  icases pt_name _ _ _ $$ ClientId with ⟨%xClientId, ClientId, %hxClientId⟩
  icases pt_name _ _ _ $$ K with ⟨%xK, K, %hxK⟩
  icases pt_name _ _ _ $$ D with ⟨%xD, D, %hxD⟩
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists (src.gryffproto.Read.mk xRequestId xClientId xK xD)
  isplitr
  · ipureintro; trivial
  isplitl [RequestId ClientId K D]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply ownReader_eq _ _ _ _ _ ?_ $$ Hown
  subst_vars
  u1_dec_norm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ReadReply.wp_Unmarshal_proof (t : Loc) (v0 : src.gryffproto.ReadReply) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R ReadReply.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.ReadReply.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : ReadReply.Msg, ⌜ReadReply.wf m⌝ ∗
          ReadReply.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ ReadReply.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.ReadReply) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, -, Hown, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  wp_auto
  u1_unmarshal_auto (src.gryffproto.ReadReply.mk _ _ _ _ _)
  icases pt_name _ _ _ $$ RequestId with ⟨%xRequestId, RequestId, %hxRequestId⟩
  icases pt_name _ _ _ $$ ClientId with ⟨%xClientId, ClientId, %hxClientId⟩
  icases pt_name _ _ _ $$ V with ⟨%xV, V, %hxV⟩
  icases pt_name _ _ _ $$ MaxSeenTag with ⟨%xMaxSeenTag, MaxSeenTag, %hxMaxSeenTag⟩
  icases pt_name _ _ _ $$ OK with ⟨%xOK, OK, %hxOK⟩
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists (src.gryffproto.ReadReply.mk xRequestId xClientId xV xMaxSeenTag xOK)
  isplitr
  · ipureintro; trivial
  isplitl [RequestId ClientId V MaxSeenTag OK]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply ownReader_eq _ _ _ _ _ ?_ $$ Hown
  subst_vars
  u1_dec_norm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem Write.wp_Unmarshal_proof (t : Loc) (v0 : src.gryffproto.Write) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Write.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Write.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Write.Msg, ⌜Write.wf m⌝ ∗
          Write.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Write.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.Write) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, -, Hown, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  wp_auto
  u1_unmarshal_auto (src.gryffproto.Write.mk _ _ _ _ _)
  icases pt_name _ _ _ $$ RequestId with ⟨%xRequestId, RequestId, %hxRequestId⟩
  icases pt_name _ _ _ $$ ClientId with ⟨%xClientId, ClientId, %hxClientId⟩
  icases pt_name _ _ _ $$ K with ⟨%xK, K, %hxK⟩
  icases pt_name _ _ _ $$ V with ⟨%xV, V, %hxV⟩
  icases pt_name _ _ _ $$ D with ⟨%xD, D, %hxD⟩
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists (src.gryffproto.Write.mk xRequestId xClientId xK xV xD)
  isplitr
  · ipureintro; trivial
  isplitl [RequestId ClientId K V D]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply ownReader_eq _ _ _ _ _ ?_ $$ Hown
  subst_vars
  u1_dec_norm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem WriteReply.wp_Unmarshal_proof (t : Loc) (v0 : src.gryffproto.WriteReply) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R WriteReply.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.WriteReply.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : WriteReply.Msg, ⌜WriteReply.wf m⌝ ∗
          WriteReply.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ WriteReply.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.WriteReply) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, -, Hown, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  wp_auto
  u1_unmarshal_auto (src.gryffproto.WriteReply.mk _ _ _ _)
  icases pt_name _ _ _ $$ RequestId with ⟨%xRequestId, RequestId, %hxRequestId⟩
  icases pt_name _ _ _ $$ ClientId with ⟨%xClientId, ClientId, %hxClientId⟩
  icases pt_name _ _ _ $$ MaxSeenTag with ⟨%xMaxSeenTag, MaxSeenTag, %hxMaxSeenTag⟩
  icases pt_name _ _ _ $$ OK with ⟨%xOK, OK, %hxOK⟩
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists (src.gryffproto.WriteReply.mk xRequestId xClientId xMaxSeenTag xOK)
  isplitr
  · ipureintro; trivial
  isplitl [RequestId ClientId MaxSeenTag OK]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply ownReader_eq _ _ _ _ _ ?_ $$ Hown
  subst_vars
  u1_dec_norm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem RMW.wp_Unmarshal_proof (t : Loc) (v0 : src.gryffproto.RMW) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R RMW.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.RMW.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : RMW.Msg, ⌜RMW.wf m⌝ ∗
          RMW.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ RMW.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.RMW) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, -, Hown, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  wp_auto
  u1_unmarshal_auto (src.gryffproto.RMW.mk _ _ _ _ _ _)
  icases pt_name _ _ _ $$ RequestId with ⟨%xRequestId, RequestId, %hxRequestId⟩
  icases pt_name _ _ _ $$ ClientId with ⟨%xClientId, ClientId, %hxClientId⟩
  icases pt_name _ _ _ $$ K with ⟨%xK, K, %hxK⟩
  icases pt_name _ _ _ $$ D with ⟨%xD, D, %hxD⟩
  icases pt_name _ _ _ $$ OldValue with ⟨%xOldValue, OldValue, %hxOldValue⟩
  icases pt_name _ _ _ $$ NewValue with ⟨%xNewValue, NewValue, %hxNewValue⟩
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists (src.gryffproto.RMW.mk xRequestId xClientId xK xD xOldValue xNewValue)
  isplitr
  · ipureintro; trivial
  isplitl [RequestId ClientId K D OldValue NewValue]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply ownReader_eq _ _ _ _ _ ?_ $$ Hown
  subst_vars
  u1_dec_norm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem RMWReply.wp_Unmarshal_proof (t : Loc) (v0 : src.gryffproto.RMWReply) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R RMWReply.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.RMWReply.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : RMWReply.Msg, ⌜RMWReply.wf m⌝ ∗
          RMWReply.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ RMWReply.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.RMWReply) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, -, Hown, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  wp_auto
  u1_unmarshal_auto (src.gryffproto.RMWReply.mk _ _ _ _)
  icases pt_name _ _ _ $$ RequestId with ⟨%xRequestId, RequestId, %hxRequestId⟩
  icases pt_name _ _ _ $$ ReplicaId with ⟨%xReplicaId, ReplicaId, %hxReplicaId⟩
  icases pt_name _ _ _ $$ OldValue with ⟨%xOldValue, OldValue, %hxOldValue⟩
  icases pt_name _ _ _ $$ OK with ⟨%xOK, OK, %hxOK⟩
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists (src.gryffproto.RMWReply.mk xRequestId xReplicaId xOldValue xOK)
  isplitr
  · ipureintro; trivial
  isplitl [RequestId ReplicaId OldValue OK]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply ownReader_eq _ _ _ _ _ ?_ $$ Hown
  subst_vars
  u1_dec_norm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem Read1Proxied.wp_Unmarshal_proof (t : Loc) (v0 : src.gryffproto.Read1Proxied) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Read1Proxied.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Read1Proxied.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Read1Proxied.Msg, ⌜Read1Proxied.wf m⌝ ∗
          Read1Proxied.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Read1Proxied.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.Read1Proxied) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, -, Hown, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  wp_auto
  u1_unmarshal_auto (src.gryffproto.Read1Proxied.mk _ _ _ _ _ _)
  icases pt_name _ _ _ $$ RequestId with ⟨%xRequestId, RequestId, %hxRequestId⟩
  icases pt_name _ _ _ $$ ClientId with ⟨%xClientId, ClientId, %hxClientId⟩
  icases pt_name _ _ _ $$ K with ⟨%xK, K, %hxK⟩
  icases pt_name _ _ _ $$ D with ⟨%xD, D, %hxD⟩
  icases pt_name _ _ _ $$ ReplicaId with ⟨%xReplicaId, ReplicaId, %hxReplicaId⟩
  icases pt_name _ _ _ $$ Vt with ⟨%xVt, Vt, %hxVt⟩
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists (src.gryffproto.Read1Proxied.mk xRequestId xClientId xK xD xReplicaId xVt)
  isplitr
  · ipureintro; trivial
  isplitl [RequestId ClientId K D ReplicaId Vt]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply ownReader_eq _ _ _ _ _ ?_ $$ Hown
  subst_vars
  u1_dec_norm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem Read1Reply.wp_Unmarshal_proof (t : Loc) (v0 : src.gryffproto.Read1Reply) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Read1Reply.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Read1Reply.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Read1Reply.Msg, ⌜Read1Reply.wf m⌝ ∗
          Read1Reply.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Read1Reply.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.Read1Reply) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, -, Hown, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  wp_auto
  u1_unmarshal_auto (src.gryffproto.Read1Reply.mk _ _ _ _)
  icases pt_name _ _ _ $$ RequestId with ⟨%xRequestId, RequestId, %hxRequestId⟩
  icases pt_name _ _ _ $$ ClientId with ⟨%xClientId, ClientId, %hxClientId⟩
  icases pt_name _ _ _ $$ ReplicaId with ⟨%xReplicaId, ReplicaId, %hxReplicaId⟩
  icases pt_name _ _ _ $$ Vt with ⟨%xVt, Vt, %hxVt⟩
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists (src.gryffproto.Read1Reply.mk xRequestId xClientId xReplicaId xVt)
  isplitr
  · ipureintro; trivial
  isplitl [RequestId ClientId ReplicaId Vt]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply ownReader_eq _ _ _ _ _ ?_ $$ Hown
  subst_vars
  u1_dec_norm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem Read2Proxied.wp_Unmarshal_proof (t : Loc) (v0 : src.gryffproto.Read2Proxied) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Read2Proxied.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Read2Proxied.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Read2Proxied.Msg, ⌜Read2Proxied.wf m⌝ ∗
          Read2Proxied.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Read2Proxied.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.Read2Proxied) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, -, Hown, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  wp_auto
  u1_unmarshal_auto (src.gryffproto.Read2Proxied.mk _ _ _ _ _ _)
  icases pt_name _ _ _ $$ RequestId with ⟨%xRequestId, RequestId, %hxRequestId⟩
  icases pt_name _ _ _ $$ ClientId with ⟨%xClientId, ClientId, %hxClientId⟩
  icases pt_name _ _ _ $$ K with ⟨%xK, K, %hxK⟩
  icases pt_name _ _ _ $$ Vt with ⟨%xVt, Vt, %hxVt⟩
  icases pt_name _ _ _ $$ ReplicaId with ⟨%xReplicaId, ReplicaId, %hxReplicaId⟩
  icases pt_name _ _ _ $$ UpdateId with ⟨%xUpdateId, UpdateId, %hxUpdateId⟩
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists (src.gryffproto.Read2Proxied.mk xRequestId xClientId xK xVt xReplicaId xUpdateId)
  isplitr
  · ipureintro; trivial
  isplitl [RequestId ClientId K Vt ReplicaId UpdateId]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply ownReader_eq _ _ _ _ _ ?_ $$ Hown
  subst_vars
  u1_dec_norm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem Read2Reply.wp_Unmarshal_proof (t : Loc) (v0 : src.gryffproto.Read2Reply) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Read2Reply.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Read2Reply.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Read2Reply.Msg, ⌜Read2Reply.wf m⌝ ∗
          Read2Reply.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Read2Reply.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.Read2Reply) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, -, Hown, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  wp_auto
  u1_unmarshal_auto (src.gryffproto.Read2Reply.mk _ _ _ _)
  icases pt_name _ _ _ $$ RequestId with ⟨%xRequestId, RequestId, %hxRequestId⟩
  icases pt_name _ _ _ $$ ClientId with ⟨%xClientId, ClientId, %hxClientId⟩
  icases pt_name _ _ _ $$ ReplicaId with ⟨%xReplicaId, ReplicaId, %hxReplicaId⟩
  icases pt_name _ _ _ $$ T with ⟨%xT, T, %hxT⟩
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists (src.gryffproto.Read2Reply.mk xRequestId xClientId xReplicaId xT)
  isplitr
  · ipureintro; trivial
  isplitl [RequestId ClientId ReplicaId T]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply ownReader_eq _ _ _ _ _ ?_ $$ Hown
  subst_vars
  u1_dec_norm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem Write1Proxied.wp_Unmarshal_proof (t : Loc) (v0 : src.gryffproto.Write1Proxied) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Write1Proxied.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Write1Proxied.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Write1Proxied.Msg, ⌜Write1Proxied.wf m⌝ ∗
          Write1Proxied.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Write1Proxied.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.Write1Proxied) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, -, Hown, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  wp_auto
  u1_unmarshal_auto (src.gryffproto.Write1Proxied.mk _ _ _ _ _ _ _ _ _)
  icases pt_name _ _ _ $$ RequestId with ⟨%xRequestId, RequestId, %hxRequestId⟩
  icases pt_name _ _ _ $$ ClientId with ⟨%xClientId, ClientId, %hxClientId⟩
  icases pt_name _ _ _ $$ N with ⟨%xN, N, %hxN⟩
  icases pt_name _ _ _ $$ ForceWrite with ⟨%xForceWrite, ForceWrite, %hxForceWrite⟩
  icases pt_name _ _ _ $$ K with ⟨%xK, K, %hxK⟩
  icases pt_name _ _ _ $$ V with ⟨%xV, V, %hxV⟩
  icases pt_name _ _ _ $$ D with ⟨%xD, D, %hxD⟩
  icases pt_name _ _ _ $$ ReplicaId with ⟨%xReplicaId, ReplicaId, %hxReplicaId⟩
  icases pt_name _ _ _ $$ MaxAppliedTag with ⟨%xMaxAppliedTag, MaxAppliedTag, %hxMaxAppliedTag⟩
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists (src.gryffproto.Write1Proxied.mk xRequestId xClientId xN xForceWrite xK xV xD xReplicaId xMaxAppliedTag)
  isplitr
  · ipureintro; trivial
  isplitl [RequestId ClientId N ForceWrite K V D ReplicaId MaxAppliedTag]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply ownReader_eq _ _ _ _ _ ?_ $$ Hown
  subst_vars
  u1_dec_norm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem Write1Reply.wp_Unmarshal_proof (t : Loc) (v0 : src.gryffproto.Write1Reply) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Write1Reply.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Write1Reply.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Write1Reply.Msg, ⌜Write1Reply.wf m⌝ ∗
          Write1Reply.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Write1Reply.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.Write1Reply) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, -, Hown, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  wp_auto
  u1_unmarshal_auto (src.gryffproto.Write1Reply.mk _ _ _ _)
  icases pt_name _ _ _ $$ RequestId with ⟨%xRequestId, RequestId, %hxRequestId⟩
  icases pt_name _ _ _ $$ ClientId with ⟨%xClientId, ClientId, %hxClientId⟩
  icases pt_name _ _ _ $$ ReplicaId with ⟨%xReplicaId, ReplicaId, %hxReplicaId⟩
  icases pt_name _ _ _ $$ Vt with ⟨%xVt, Vt, %hxVt⟩
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists (src.gryffproto.Write1Reply.mk xRequestId xClientId xReplicaId xVt)
  isplitr
  · ipureintro; trivial
  isplitl [RequestId ClientId ReplicaId Vt]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply ownReader_eq _ _ _ _ _ ?_ $$ Hown
  subst_vars
  u1_dec_norm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem Write2Proxied.wp_Unmarshal_proof (t : Loc) (v0 : src.gryffproto.Write2Proxied) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Write2Proxied.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Write2Proxied.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Write2Proxied.Msg, ⌜Write2Proxied.wf m⌝ ∗
          Write2Proxied.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Write2Proxied.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.Write2Proxied) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, -, Hown, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  wp_auto
  u1_unmarshal_auto (src.gryffproto.Write2Proxied.mk _ _ _ _ _ _)
  icases pt_name _ _ _ $$ RequestId with ⟨%xRequestId, RequestId, %hxRequestId⟩
  icases pt_name _ _ _ $$ ClientId with ⟨%xClientId, ClientId, %hxClientId⟩
  icases pt_name _ _ _ $$ N with ⟨%xN, N, %hxN⟩
  icases pt_name _ _ _ $$ K with ⟨%xK, K, %hxK⟩
  icases pt_name _ _ _ $$ Vt with ⟨%xVt, Vt, %hxVt⟩
  icases pt_name _ _ _ $$ ReplicaId with ⟨%xReplicaId, ReplicaId, %hxReplicaId⟩
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists (src.gryffproto.Write2Proxied.mk xRequestId xClientId xN xK xVt xReplicaId)
  isplitr
  · ipureintro; trivial
  isplitl [RequestId ClientId N K Vt ReplicaId]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply ownReader_eq _ _ _ _ _ ?_ $$ Hown
  subst_vars
  u1_dec_norm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem Write2Reply.wp_Unmarshal_proof (t : Loc) (v0 : src.gryffproto.Write2Reply) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Write2Reply.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Write2Reply.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Write2Reply.Msg, ⌜Write2Reply.wf m⌝ ∗
          Write2Reply.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Write2Reply.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.Write2Reply) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, -, Hown, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  wp_auto
  u1_unmarshal_auto (src.gryffproto.Write2Reply.mk _ _ _ _ _)
  icases pt_name _ _ _ $$ RequestId with ⟨%xRequestId, RequestId, %hxRequestId⟩
  icases pt_name _ _ _ $$ ClientId with ⟨%xClientId, ClientId, %hxClientId⟩
  icases pt_name _ _ _ $$ ReplicaId with ⟨%xReplicaId, ReplicaId, %hxReplicaId⟩
  icases pt_name _ _ _ $$ T with ⟨%xT, T, %hxT⟩
  icases pt_name _ _ _ $$ Applied with ⟨%xApplied, Applied, %hxApplied⟩
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists (src.gryffproto.Write2Reply.mk xRequestId xClientId xReplicaId xT xApplied)
  isplitr
  · ipureintro; trivial
  isplitl [RequestId ClientId ReplicaId T Applied]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply ownReader_eq _ _ _ _ _ ?_ $$ Hown
  subst_vars
  u1_dec_norm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem PreAcceptReply.wp_Unmarshal_proof (t : Loc) (v0 : src.gryffproto.PreAcceptReply) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R PreAcceptReply.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.PreAcceptReply.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : PreAcceptReply.Msg, ⌜PreAcceptReply.wf m⌝ ∗
          PreAcceptReply.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ PreAcceptReply.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.PreAcceptReply) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, -, Hown, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  wp_auto
  u1_unmarshal_auto (src.gryffproto.PreAcceptReply.mk _ _ _ _ _ _ _ _)
  ihave %HdlDeps := array_len _ _ _ _ $$ Deps
  ihave %HdlCommittedDeps := array_len _ _ _ _ $$ CommittedDeps
  icases pt_name _ _ _ $$ Replica with ⟨%xReplica, Replica, %hxReplica⟩
  icases pt_name _ _ _ $$ Instance with ⟨%xInstance, Instance, %hxInstance⟩
  icases pt_name _ _ _ $$ OK with ⟨%xOK, OK, %hxOK⟩
  icases pt_name _ _ _ $$ Ballot with ⟨%xBallot, Ballot, %hxBallot⟩
  icases pt_name _ _ _ $$ Seq with ⟨%xSeq, Seq, %hxSeq⟩
  icases pt_name _ _ _ $$ Deps with ⟨%xDeps, Deps, %hxDeps⟩
  icases pt_name _ _ _ $$ CommittedDeps with ⟨%xCommittedDeps, CommittedDeps, %hxCommittedDeps⟩
  icases pt_name _ _ _ $$ Base with ⟨%xBase, Base, %hxBase⟩
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists (src.gryffproto.PreAcceptReply.mk xReplica xInstance xOK xBallot xSeq xDeps xCommittedDeps xBase)
  isplitr
  · ipureintro; trivial
  isplitl [Replica Instance OK Ballot Seq Deps CommittedDeps Base]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply ownReader_eq _ _ _ _ _ ?_ $$ Hown
  subst_vars
  simp only [List.length_set] at HdlDeps
  rw [set5 v0.Deps'.arr (by omega)]
  simp only [List.length_set] at HdlCommittedDeps
  rw [set5 v0.CommittedDeps'.arr (by omega)]
  u1_dec_norm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem Executed.wp_Unmarshal_proof (t : Loc) (v0 : src.gryffproto.Executed) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Executed.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Executed.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Executed.Msg, ⌜Executed.wf m⌝ ∗
          Executed.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Executed.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.Executed) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, -, Hown, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  wp_auto
  u1_unmarshal_auto (src.gryffproto.Executed.mk _ _)
  icases pt_name _ _ _ $$ Replica with ⟨%xReplica, Replica, %hxReplica⟩
  icases pt_name _ _ _ $$ Instance with ⟨%xInstance, Instance, %hxInstance⟩
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists (src.gryffproto.Executed.mk xReplica xInstance)
  isplitr
  · ipureintro; trivial
  isplitl [Replica Instance]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply ownReader_eq _ _ _ _ _ ?_ $$ Hown
  subst_vars
  u1_dec_norm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem PreAcceptOKReply.wp_Unmarshal_proof (t : Loc) (v0 : src.gryffproto.PreAcceptOKReply) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R PreAcceptOKReply.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.PreAcceptOKReply.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : PreAcceptOKReply.Msg, ⌜PreAcceptOKReply.wf m⌝ ∗
          PreAcceptOKReply.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ PreAcceptOKReply.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.PreAcceptOKReply) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, -, Hown, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  wp_auto
  u1_unmarshal_auto (src.gryffproto.PreAcceptOKReply.mk _ _)
  icases pt_name _ _ _ $$ Replica with ⟨%xReplica, Replica, %hxReplica⟩
  icases pt_name _ _ _ $$ Instance with ⟨%xInstance, Instance, %hxInstance⟩
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists (src.gryffproto.PreAcceptOKReply.mk xReplica xInstance)
  isplitr
  · ipureintro; trivial
  isplitl [Replica Instance]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply ownReader_eq _ _ _ _ _ ?_ $$ Hown
  subst_vars
  u1_dec_norm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem AcceptOKReply.wp_Unmarshal_proof (t : Loc) (v0 : src.gryffproto.AcceptOKReply) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R AcceptOKReply.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.AcceptOKReply.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : AcceptOKReply.Msg, ⌜AcceptOKReply.wf m⌝ ∗
          AcceptOKReply.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ AcceptOKReply.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.AcceptOKReply) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, -, Hown, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  wp_auto
  u1_unmarshal_auto (src.gryffproto.AcceptOKReply.mk _ _)
  icases pt_name _ _ _ $$ Replica with ⟨%xReplica, Replica, %hxReplica⟩
  icases pt_name _ _ _ $$ Instance with ⟨%xInstance, Instance, %hxInstance⟩
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists (src.gryffproto.AcceptOKReply.mk xReplica xInstance)
  isplitr
  · ipureintro; trivial
  isplitl [Replica Instance]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply ownReader_eq _ _ _ _ _ ?_ $$ Hown
  subst_vars
  u1_dec_norm
end gryffproto
end uproofs
end Perennial.gryff.wire
