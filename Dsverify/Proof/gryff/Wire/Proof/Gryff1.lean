/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Wire/Proof/Gryff1.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).
-/
module

public import Dsverify.Proof.gryff.Wire.Proof.State

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

namespace gryffproto

theorem Tag.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : Tag.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ Tag.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ Tag.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Tag.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ Tag.enc m) ∗ Tag.own t dq m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  iunfold Tag.own at Ht
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  wp_auto
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 12 - W64 0 = W64 12 from rfl]
  ihave Hb := slice_array (GF := GF) b_ptr _ _ (by decide) $$ b
  (try wp_auto)
  repeat u1_wstore
  u1_buf_norm
  wp_apply wp_wire_Write $$ [$Hwr $HQ $Hw $Hb] as %nn %e ⟨Hw, Hb⟩
  · ipureintro; u1_prefix_tac
  iapply HΦ
  isplitl [Hw]
  · iapply wst_congr _ _ _ _ _ _ _ _ _ (by u1_enc_norm) $$ Hw
  iunfold Tag.own
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

theorem ValTag.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : ValTag.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ ValTag.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ t ↦{dq} m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.ValTag.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ ValTag.enc m) ∗ t ↦{dq} m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  ihave %HnnT := typedPointsto_not_null _ _ _ $$ T
  iStructNamedPrefix T "T_"
  u1_marshal_auto
  ihave T : (t.[src.gryffproto.ValTag, go!"T"] ↦{dq} m.T' : IProp GF) $$ [T_Ts T_Cid T_Rmwc T__]
  · iapply typedPointsto_combine _ _ _ HnnT
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  u1_marshal_finish

theorem Dep.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : Dep.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ Dep.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ t ↦{dq} m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Dep.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ Dep.enc m) ∗ t ↦{dq} m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  u1_marshal_auto
  u1_marshal_finish

theorem Read.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : Read.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ Read.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ t ↦{dq} m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Read.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ Read.enc m) ∗ t ↦{dq} m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  u1_marshal_auto
  u1_marshal_finish

theorem ReadReply.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : ReadReply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ ReadReply.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ t ↦{dq} m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.ReadReply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ ReadReply.enc m) ∗ t ↦{dq} m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  ihave %HnnMaxSeenTag := typedPointsto_not_null _ _ _ $$ MaxSeenTag
  iStructNamedPrefix MaxSeenTag "MaxSeenTag_"
  u1_marshal_auto
  ihave MaxSeenTag : (t.[src.gryffproto.ReadReply, go!"MaxSeenTag"] ↦{dq} m.MaxSeenTag' : IProp GF) $$ [MaxSeenTag_Ts MaxSeenTag_Cid MaxSeenTag_Rmwc MaxSeenTag__]
  · iapply typedPointsto_combine _ _ _ HnnMaxSeenTag
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  u1_marshal_finish

theorem Dep.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : Dep.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Dep.enc m) ∗
        Dep.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Dep.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Dep.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Dep.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Dep.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Dep.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen Dep.wp_Marshal_gen

theorem Read.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : Read.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Read.enc m) ∗
        Read.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Read.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Read.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Read.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Read.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Read.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen Read.wp_Marshal_gen

theorem ReadReply.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : ReadReply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ ReadReply.enc m) ∗
        ReadReply.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.ReadReply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (ReadReply.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (ReadReply.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (ReadReply.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        ReadReply.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen ReadReply.wp_Marshal_gen


theorem Write.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : Write.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ Write.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ t ↦{dq} m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Write.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ Write.enc m) ∗ t ↦{dq} m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  u1_marshal_auto
  u1_marshal_finish

theorem WriteReply.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : WriteReply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ WriteReply.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ t ↦{dq} m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.WriteReply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ WriteReply.enc m) ∗ t ↦{dq} m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  ihave %HnnMaxSeenTag := typedPointsto_not_null _ _ _ $$ MaxSeenTag
  iStructNamedPrefix MaxSeenTag "MaxSeenTag_"
  u1_marshal_auto
  ihave MaxSeenTag : (t.[src.gryffproto.WriteReply, go!"MaxSeenTag"] ↦{dq} m.MaxSeenTag' : IProp GF) $$ [MaxSeenTag_Ts MaxSeenTag_Cid MaxSeenTag_Rmwc MaxSeenTag__]
  · iapply typedPointsto_combine _ _ _ HnnMaxSeenTag
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  u1_marshal_finish

theorem RMW.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : RMW.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ RMW.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ t ↦{dq} m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.RMW.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ RMW.enc m) ∗ t ↦{dq} m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  u1_marshal_auto
  u1_marshal_finish

theorem RMWReply.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : RMWReply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ RMWReply.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ t ↦{dq} m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.RMWReply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ RMWReply.enc m) ∗ t ↦{dq} m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  u1_marshal_auto
  u1_marshal_finish

theorem Read1Proxied.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : Read1Proxied.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ Read1Proxied.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ t ↦{dq} m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Read1Proxied.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ Read1Proxied.enc m) ∗ t ↦{dq} m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  u1_marshal_auto
  u1_marshal_finish

theorem Read1Reply.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : Read1Reply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ Read1Reply.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ t ↦{dq} m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Read1Reply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ Read1Reply.enc m) ∗ t ↦{dq} m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  u1_marshal_auto
  u1_marshal_finish

theorem Read2Proxied.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : Read2Proxied.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ Read2Proxied.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ t ↦{dq} m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Read2Proxied.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ Read2Proxied.enc m) ∗ t ↦{dq} m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  u1_marshal_auto
  u1_marshal_finish

theorem Read2Reply.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : Read2Reply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ Read2Reply.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ t ↦{dq} m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Read2Reply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ Read2Reply.enc m) ∗ t ↦{dq} m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  ihave %HnnT := typedPointsto_not_null _ _ _ $$ T
  iStructNamedPrefix T "T_"
  u1_marshal_auto
  ihave T : (t.[src.gryffproto.Read2Reply, go!"T"] ↦{dq} m.T' : IProp GF) $$ [T_Ts T_Cid T_Rmwc T__]
  · iapply typedPointsto_combine _ _ _ HnnT
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  u1_marshal_finish

theorem Write1Proxied.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : Write1Proxied.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ Write1Proxied.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ t ↦{dq} m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Write1Proxied.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ Write1Proxied.enc m) ∗ t ↦{dq} m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  ihave %HnnMaxAppliedTag := typedPointsto_not_null _ _ _ $$ MaxAppliedTag
  iStructNamedPrefix MaxAppliedTag "MaxAppliedTag_"
  u1_marshal_auto
  ihave MaxAppliedTag : (t.[src.gryffproto.Write1Proxied, go!"MaxAppliedTag"] ↦{dq} m.MaxAppliedTag' : IProp GF) $$ [MaxAppliedTag_Ts MaxAppliedTag_Cid MaxAppliedTag_Rmwc MaxAppliedTag__]
  · iapply typedPointsto_combine _ _ _ HnnMaxAppliedTag
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  u1_marshal_finish

theorem Write1Reply.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : Write1Reply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ Write1Reply.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ t ↦{dq} m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Write1Reply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ Write1Reply.enc m) ∗ t ↦{dq} m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  u1_marshal_auto
  u1_marshal_finish

theorem Write2Proxied.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : Write2Proxied.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ Write2Proxied.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ t ↦{dq} m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Write2Proxied.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ Write2Proxied.enc m) ∗ t ↦{dq} m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  u1_marshal_auto
  u1_marshal_finish

theorem Write2Reply.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : Write2Reply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ Write2Reply.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ t ↦{dq} m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Write2Reply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ Write2Reply.enc m) ∗ t ↦{dq} m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  ihave %HnnT := typedPointsto_not_null _ _ _ $$ T
  iStructNamedPrefix T "T_"
  u1_marshal_auto
  ihave T : (t.[src.gryffproto.Write2Reply, go!"T"] ↦{dq} m.T' : IProp GF) $$ [T_Ts T_Cid T_Rmwc T__]
  · iapply typedPointsto_combine _ _ _ HnnT
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  u1_marshal_finish

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem PreAcceptReply.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : PreAcceptReply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ PreAcceptReply.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ t ↦{dq} m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.PreAcceptReply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ PreAcceptReply.enc m) ∗ t ↦{dq} m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  u1_marshal_auto
  u1_marshal_finish

theorem Executed.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : Executed.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ Executed.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ t ↦{dq} m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Executed.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ Executed.enc m) ∗ t ↦{dq} m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  u1_marshal_auto
  u1_marshal_finish

theorem PreAcceptOKReply.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : PreAcceptOKReply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ PreAcceptOKReply.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ t ↦{dq} m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.PreAcceptOKReply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ PreAcceptOKReply.enc m) ∗ t ↦{dq} m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  u1_marshal_auto
  u1_marshal_finish

theorem AcceptOKReply.wp_Marshal_gen (t : Loc) (dq : DFrac) (m : AcceptOKReply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) (E0 D : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        □ Q (sent ++ pend ++ E0) ∗ ⌜D ++ AcceptOKReply.enc m <+: E0⌝ ∗
        wst bw wr J Q sent pend err D ∗ t ↦{dq} m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.AcceptOKReply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); wst bw wr J Q sent pend err (D ++ AcceptOKReply.enc m) ∗ t ↦{dq} m }} := by
  wp_start as ⟨#Hwr, #HQ, %Hpre, Hw, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  u1_marshal_auto
  u1_marshal_finish

theorem Write.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : Write.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Write.enc m) ∗
        Write.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Write.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Write.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Write.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Write.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Write.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen Write.wp_Marshal_gen

theorem WriteReply.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : WriteReply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ WriteReply.enc m) ∗
        WriteReply.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.WriteReply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (WriteReply.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (WriteReply.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (WriteReply.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        WriteReply.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen WriteReply.wp_Marshal_gen

theorem RMW.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : RMW.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ RMW.enc m) ∗
        RMW.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.RMW.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (RMW.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (RMW.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (RMW.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        RMW.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen RMW.wp_Marshal_gen

theorem RMWReply.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : RMWReply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ RMWReply.enc m) ∗
        RMWReply.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.RMWReply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (RMWReply.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (RMWReply.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (RMWReply.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        RMWReply.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen RMWReply.wp_Marshal_gen

theorem Read1Proxied.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : Read1Proxied.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Read1Proxied.enc m) ∗
        Read1Proxied.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Read1Proxied.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Read1Proxied.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Read1Proxied.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Read1Proxied.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Read1Proxied.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen Read1Proxied.wp_Marshal_gen

theorem Read1Reply.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : Read1Reply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Read1Reply.enc m) ∗
        Read1Reply.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Read1Reply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Read1Reply.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Read1Reply.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Read1Reply.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Read1Reply.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen Read1Reply.wp_Marshal_gen

theorem Read2Proxied.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : Read2Proxied.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Read2Proxied.enc m) ∗
        Read2Proxied.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Read2Proxied.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Read2Proxied.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Read2Proxied.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Read2Proxied.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Read2Proxied.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen Read2Proxied.wp_Marshal_gen

theorem Read2Reply.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : Read2Reply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Read2Reply.enc m) ∗
        Read2Reply.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Read2Reply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Read2Reply.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Read2Reply.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Read2Reply.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Read2Reply.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen Read2Reply.wp_Marshal_gen

theorem Write1Proxied.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : Write1Proxied.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Write1Proxied.enc m) ∗
        Write1Proxied.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Write1Proxied.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Write1Proxied.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Write1Proxied.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Write1Proxied.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Write1Proxied.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen Write1Proxied.wp_Marshal_gen

theorem Write1Reply.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : Write1Reply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Write1Reply.enc m) ∗
        Write1Reply.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Write1Reply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Write1Reply.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Write1Reply.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Write1Reply.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Write1Reply.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen Write1Reply.wp_Marshal_gen

theorem Write2Proxied.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : Write2Proxied.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Write2Proxied.enc m) ∗
        Write2Proxied.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Write2Proxied.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Write2Proxied.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Write2Proxied.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Write2Proxied.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Write2Proxied.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen Write2Proxied.wp_Marshal_gen

theorem Write2Reply.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : Write2Reply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Write2Reply.enc m) ∗
        Write2Reply.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Write2Reply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Write2Reply.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Write2Reply.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Write2Reply.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Write2Reply.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen Write2Reply.wp_Marshal_gen

theorem PreAcceptReply.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : PreAcceptReply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ PreAcceptReply.enc m) ∗
        PreAcceptReply.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.PreAcceptReply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (PreAcceptReply.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (PreAcceptReply.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (PreAcceptReply.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        PreAcceptReply.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen PreAcceptReply.wp_Marshal_gen

theorem Executed.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : Executed.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Executed.enc m) ∗
        Executed.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Executed.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Executed.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Executed.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Executed.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Executed.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen Executed.wp_Marshal_gen

theorem PreAcceptOKReply.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : PreAcceptOKReply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ PreAcceptOKReply.enc m) ∗
        PreAcceptOKReply.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.PreAcceptOKReply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (PreAcceptOKReply.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (PreAcceptOKReply.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (PreAcceptOKReply.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        PreAcceptOKReply.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen PreAcceptOKReply.wp_Marshal_gen

theorem AcceptOKReply.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : AcceptOKReply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ AcceptOKReply.enc m) ∗
        AcceptOKReply.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.AcceptOKReply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (AcceptOKReply.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (AcceptOKReply.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (AcceptOKReply.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        AcceptOKReply.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen AcceptOKReply.wp_Marshal_gen


theorem Tag.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : Tag.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Tag.enc m) ∗
        Tag.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Tag.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Tag.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Tag.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Tag.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Tag.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen Tag.wp_Marshal_gen


theorem ValTag.wp_Marshal_proof (t : Loc) (dq : DFrac) (m : ValTag.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ ValTag.enc m) ∗
        ValTag.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.ValTag.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (ValTag.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (ValTag.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (ValTag.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        ValTag.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  u1_marshal_frozen ValTag.wp_Marshal_gen


end gryffproto
end proofs

section uproofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [bufio.Assumptions] [io.Assumptions] [encoding.binary.Assumptions] [wire.BufioSpecs GF]
variable [src.state.Assumptions] [src.gryffproto.Assumptions] [src.epaxosproto.Assumptions]
variable [src.clientproto.Assumptions] [src.genericsmrproto.Assumptions]

namespace gryffproto

theorem Tag.wp_Unmarshal_proof (t : Loc) (v0 : src.gryffproto.Tag) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Tag.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Tag.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Tag.Msg, ⌜Tag.wf m⌝ ∗
          Tag.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Tag.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.Tag) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, -, Hown, Ht⟩
  wp_auto
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 12 - W64 0 = W64 12 from rfl]
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
    have hl : data.length = 12 := by simpa using Hlen
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

theorem ValTag.wp_Unmarshal_proof (t : Loc) (v0 : src.gryffproto.ValTag) (br : Loc)
    (rd : RSt GF) (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R ValTag.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.ValTag.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : ValTag.Msg, ⌜ValTag.wf m⌝ ∗
          ValTag.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ ValTag.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.ValTag) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, -, Hown, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  wp_auto
  wp_apply state.Value.wp_Unmarshal_proof $$ [$Hrd $Hown $V] as %err
    (⟨%Hnil, %mv, -, HV, Hown⟩ | ⟨%Hne, #Ha, %vv, %R1, HV, Hown⟩)
  · iapply readNext_true; intro; trivial
  · subst Hnil
    wp_auto
    rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0,
      show W64 12 - W64 0 = W64 12 from rfl]
    ihave Hb := slice_array (GF := GF) b_ptr _ _ (by decide) $$ b
    wp_apply wp_wire_ReadAtLeast $$ [$Hrd $Hown $Hb] as %nr %err ⟨%data, Hown, Hr⟩
    icases Hr with (⟨⟨%Hnil, %Hlen⟩, Hb⟩ | ⟨%Hne, #Ha, %vs', Hb⟩)
    · subst Hnil
      wp_auto
      repeat u1_wload
      have hl : data.length = 12 := by simpa using Hlen
      icases pt_name _ _ _ $$ T with ⟨%Tv, T, %hTv⟩
      iapply HΦ
      ileft
      isplitr
      · ipureintro; rfl
      iexists (src.gryffproto.ValTag.mk mv Tv)
      isplitr
      · ipureintro; trivial
      isplitl [HV T]
      · iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      iapply ownReader_eq _ _ _ _ _ ?_ $$ Hown
      rw [List.append_assoc]
      congr 1
      simp only [ValTag.enc]
      congr 1
      subst hTv
      u1_dec_tac hl
    · obtain ⟨ei, rfl⟩ : ∃ ei, err = interface.ok ei := by
        cases err with
        | nil => exact absurd rfl Hne
        | ok ei => exact ⟨ei, rfl⟩
      wp_auto
      simp only [List.append_assoc]
      iapply HΦ
      iright
      iframe Ha
      isplitr
      · ipureintro; exact Hne
      iexists (src.gryffproto.ValTag.mk _ _), _
      iframe Hown
      iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
  · obtain ⟨ei, rfl⟩ : ∃ ei, err = interface.ok ei := by
      cases err with
      | nil => exact absurd rfl Hne
      | ok ei => exact ⟨ei, rfl⟩
    wp_auto
    iapply HΦ
    iright
    iframe Ha
    isplitr
    · ipureintro; exact Hne
    iexists (src.gryffproto.ValTag.mk _ _), _
    iframe Hown
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem Dep.wp_Unmarshal_proof (t : Loc) (v0 : src.gryffproto.Dep) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Dep.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Dep.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Dep.Msg, ⌜Dep.wf m⌝ ∗
          Dep.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Dep.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.Dep) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, -, Hown, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  wp_auto
  u1_unmarshal_auto (src.gryffproto.Dep.mk _ _)
  icases pt_name _ _ _ $$ Key with ⟨%xKey, Key, %hxKey⟩
  icases pt_name _ _ _ $$ Vt with ⟨%xVt, Vt, %hxVt⟩
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists (src.gryffproto.Dep.mk xKey xVt)
  isplitr
  · ipureintro; trivial
  isplitl [Key Vt]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply ownReader_eq _ _ _ _ _ ?_ $$ Hown
  subst_vars
  u1_dec_norm


end gryffproto
end uproofs
end Perennial.gryff.wire
