/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/N/Marshal.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit N: each message type's `Marshal` as `marSpec` (from `Wire/Specs.lean`'s general forms)
-/
module

public import Dsverify.Proof.gryff.N.Generic
public import Dsverify.Proof.gryff.N.SliceMarshal

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.netN

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section generic
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [bufio.Assumptions] [io.Assumptions] [encoding.binary.Assumptions] [wire.BufioSpecs GF]
variable [wire.BinaryVarintHyps GF]
variable [src.state.Assumptions] [src.gryffproto.Assumptions] [src.epaxosproto.Assumptions]
variable [src.clientproto.Assumptions] [src.genericsmrproto.Assumptions]

theorem marSpec_Read1Proxied (pm : Loc) (g : wire.gryffproto.Read1Proxied.Msg) :
    marSpec (GF := GF) (go.GoType.PointerType src.gryffproto.Read1Proxied.ty) pm (wire.gryffproto.Read1Proxied.enc g)
      iprop(isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ wire.gryffproto.Read1Proxied.own pm (DFrac.own 1) g) := by
  intro w wr J Q s p er E0 D
  iintro %Φ ⟨#Hwr, #HQ, %Hp, Hw, #Hp1, #Hp2, Ho⟩ HΦ
  wp_apply (wire.gryffproto.Read1Proxied.wp_Marshal_gen pm (DFrac.own 1) g w wr J Q s p er E0 D)
    $$ [$Hwr $HQ $Hw $Ho $Hp1 $Hp2] as ⟨Hw, Ho⟩
  · ipureintro; exact Hp
  iapply HΦ; iframe; iframe #

theorem marSpec_Read2Proxied (pm : Loc) (g : wire.gryffproto.Read2Proxied.Msg) :
    marSpec (GF := GF) (go.GoType.PointerType src.gryffproto.Read2Proxied.ty) pm (wire.gryffproto.Read2Proxied.enc g)
      iprop(isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ wire.gryffproto.Read2Proxied.own pm (DFrac.own 1) g) := by
  intro w wr J Q s p er E0 D
  iintro %Φ ⟨#Hwr, #HQ, %Hp, Hw, #Hp1, #Hp2, Ho⟩ HΦ
  wp_apply (wire.gryffproto.Read2Proxied.wp_Marshal_gen pm (DFrac.own 1) g w wr J Q s p er E0 D)
    $$ [$Hwr $HQ $Hw $Ho $Hp1 $Hp2] as ⟨Hw, Ho⟩
  · ipureintro; exact Hp
  iapply HΦ; iframe; iframe #

theorem marSpec_Read1Reply (pm : Loc) (g : wire.gryffproto.Read1Reply.Msg) :
    marSpec (GF := GF) (go.GoType.PointerType src.gryffproto.Read1Reply.ty) pm (wire.gryffproto.Read1Reply.enc g)
      iprop(isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ wire.gryffproto.Read1Reply.own pm (DFrac.own 1) g) := by
  intro w wr J Q s p er E0 D
  iintro %Φ ⟨#Hwr, #HQ, %Hp, Hw, #Hp1, #Hp2, Ho⟩ HΦ
  wp_apply (wire.gryffproto.Read1Reply.wp_Marshal_gen pm (DFrac.own 1) g w wr J Q s p er E0 D)
    $$ [$Hwr $HQ $Hw $Ho $Hp1 $Hp2] as ⟨Hw, Ho⟩
  · ipureintro; exact Hp
  iapply HΦ; iframe; iframe #

theorem marSpec_Read2Reply (pm : Loc) (g : wire.gryffproto.Read2Reply.Msg) :
    marSpec (GF := GF) (go.GoType.PointerType src.gryffproto.Read2Reply.ty) pm (wire.gryffproto.Read2Reply.enc g)
      iprop(isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ wire.gryffproto.Read2Reply.own pm (DFrac.own 1) g) := by
  intro w wr J Q s p er E0 D
  iintro %Φ ⟨#Hwr, #HQ, %Hp, Hw, #Hp1, #Hp2, Ho⟩ HΦ
  wp_apply (wire.gryffproto.Read2Reply.wp_Marshal_gen pm (DFrac.own 1) g w wr J Q s p er E0 D)
    $$ [$Hwr $HQ $Hw $Ho $Hp1 $Hp2] as ⟨Hw, Ho⟩
  · ipureintro; exact Hp
  iapply HΦ; iframe; iframe #

theorem marSpec_Write1Proxied (pm : Loc) (g : wire.gryffproto.Write1Proxied.Msg) :
    marSpec (GF := GF) (go.GoType.PointerType src.gryffproto.Write1Proxied.ty) pm (wire.gryffproto.Write1Proxied.enc g)
      iprop(isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ wire.gryffproto.Write1Proxied.own pm (DFrac.own 1) g) := by
  intro w wr J Q s p er E0 D
  iintro %Φ ⟨#Hwr, #HQ, %Hp, Hw, #Hp1, #Hp2, Ho⟩ HΦ
  wp_apply (wire.gryffproto.Write1Proxied.wp_Marshal_gen pm (DFrac.own 1) g w wr J Q s p er E0 D)
    $$ [$Hwr $HQ $Hw $Ho $Hp1 $Hp2] as ⟨Hw, Ho⟩
  · ipureintro; exact Hp
  iapply HΦ; iframe; iframe #

theorem marSpec_Write2Proxied (pm : Loc) (g : wire.gryffproto.Write2Proxied.Msg) :
    marSpec (GF := GF) (go.GoType.PointerType src.gryffproto.Write2Proxied.ty) pm (wire.gryffproto.Write2Proxied.enc g)
      iprop(isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ wire.gryffproto.Write2Proxied.own pm (DFrac.own 1) g) := by
  intro w wr J Q s p er E0 D
  iintro %Φ ⟨#Hwr, #HQ, %Hp, Hw, #Hp1, #Hp2, Ho⟩ HΦ
  wp_apply (wire.gryffproto.Write2Proxied.wp_Marshal_gen pm (DFrac.own 1) g w wr J Q s p er E0 D)
    $$ [$Hwr $HQ $Hw $Ho $Hp1 $Hp2] as ⟨Hw, Ho⟩
  · ipureintro; exact Hp
  iapply HΦ; iframe; iframe #

theorem marSpec_Write1Reply (pm : Loc) (g : wire.gryffproto.Write1Reply.Msg) :
    marSpec (GF := GF) (go.GoType.PointerType src.gryffproto.Write1Reply.ty) pm (wire.gryffproto.Write1Reply.enc g)
      iprop(isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ wire.gryffproto.Write1Reply.own pm (DFrac.own 1) g) := by
  intro w wr J Q s p er E0 D
  iintro %Φ ⟨#Hwr, #HQ, %Hp, Hw, #Hp1, #Hp2, Ho⟩ HΦ
  wp_apply (wire.gryffproto.Write1Reply.wp_Marshal_gen pm (DFrac.own 1) g w wr J Q s p er E0 D)
    $$ [$Hwr $HQ $Hw $Ho $Hp1 $Hp2] as ⟨Hw, Ho⟩
  · ipureintro; exact Hp
  iapply HΦ; iframe; iframe #

theorem marSpec_Write2Reply (pm : Loc) (g : wire.gryffproto.Write2Reply.Msg) :
    marSpec (GF := GF) (go.GoType.PointerType src.gryffproto.Write2Reply.ty) pm (wire.gryffproto.Write2Reply.enc g)
      iprop(isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ wire.gryffproto.Write2Reply.own pm (DFrac.own 1) g) := by
  intro w wr J Q s p er E0 D
  iintro %Φ ⟨#Hwr, #HQ, %Hp, Hw, #Hp1, #Hp2, Ho⟩ HΦ
  wp_apply (wire.gryffproto.Write2Reply.wp_Marshal_gen pm (DFrac.own 1) g w wr J Q s p er E0 D)
    $$ [$Hwr $HQ $Hw $Ho $Hp1 $Hp2] as ⟨Hw, Ho⟩
  · ipureintro; exact Hp
  iapply HΦ; iframe; iframe #

theorem marSpec_PreAccept (pm : Loc) (g : wire.gryffproto.PreAccept.Msg) (sl : GoSlice) :
    marSpec (GF := GF) (go.GoType.PointerType src.gryffproto.PreAccept.ty) pm (wire.gryffproto.PreAccept.enc g)
      iprop(isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ pm ↦ wire.gryffproto.PreAccept.goVal g sl ∗
        sl ↦*□ g.Command) := by
  intro w wr J Q s p er E0 D
  iintro %Φ ⟨#Hwr, #HQ, %Hp, Hw, #Hp1, #Hp2, Ho, #Hsl⟩ HΦ
  wp_apply (wire.gryffproto.PreAccept.wp_Marshal_gen2 pm (DFrac.own 1) DFrac.discard g sl w wr J Q s p er
    E0 D) $$ [$Hwr $HQ $Hw $Ho $Hp1 $Hp2 $Hsl] as ⟨Hw, Ho, -⟩
  · ipureintro; exact Hp
  iapply HΦ; iframe; iframe #

theorem marSpec_PreAcceptReply (pm : Loc) (g : wire.gryffproto.PreAcceptReply.Msg) :
    marSpec (GF := GF) (go.GoType.PointerType src.gryffproto.PreAcceptReply.ty) pm (wire.gryffproto.PreAcceptReply.enc g)
      iprop(isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ wire.gryffproto.PreAcceptReply.own pm (DFrac.own 1) g) := by
  intro w wr J Q s p er E0 D
  iintro %Φ ⟨#Hwr, #HQ, %Hp, Hw, #Hp1, #Hp2, Ho⟩ HΦ
  wp_apply (wire.gryffproto.PreAcceptReply.wp_Marshal_gen pm (DFrac.own 1) g w wr J Q s p er E0 D)
    $$ [$Hwr $HQ $Hw $Ho $Hp1 $Hp2] as ⟨Hw, Ho⟩
  · ipureintro; exact Hp
  iapply HΦ; iframe; iframe #

theorem marSpec_EAccept (pm : Loc) (g : wire.gryffproto.EAccept.Msg) (sl : GoSlice) :
    marSpec (GF := GF) (go.GoType.PointerType src.gryffproto.EAccept.ty) pm (wire.gryffproto.EAccept.enc g)
      iprop(isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ pm ↦ wire.gryffproto.EAccept.goVal g sl ∗
        sl ↦*□ g.Command) := by
  intro w wr J Q s p er E0 D
  iintro %Φ ⟨#Hwr, #HQ, %Hp, Hw, #Hp1, #Hp2, Ho, #Hsl⟩ HΦ
  wp_apply (wire.gryffproto.EAccept.wp_Marshal_gen2 pm (DFrac.own 1) DFrac.discard g sl w wr J Q s p er
    E0 D) $$ [$Hwr $HQ $Hw $Ho $Hp1 $Hp2 $Hsl] as ⟨Hw, Ho, -⟩
  · ipureintro; exact Hp
  iapply HΦ; iframe; iframe #

theorem marSpec_ECommit (pm : Loc) (g : wire.gryffproto.ECommit.Msg) (sl : GoSlice) :
    marSpec (GF := GF) (go.GoType.PointerType src.gryffproto.ECommit.ty) pm (wire.gryffproto.ECommit.enc g)
      iprop(isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ pm ↦ wire.gryffproto.ECommit.goVal g sl ∗
        sl ↦*□ g.Command) := by
  intro w wr J Q s p er E0 D
  iintro %Φ ⟨#Hwr, #HQ, %Hp, Hw, #Hp1, #Hp2, Ho, #Hsl⟩ HΦ
  wp_apply (wire.gryffproto.ECommit.wp_Marshal_gen2 pm (DFrac.own 1) DFrac.discard g sl w wr J Q s p er
    E0 D) $$ [$Hwr $HQ $Hw $Ho $Hp1 $Hp2 $Hsl] as ⟨Hw, Ho, -⟩
  · ipureintro; exact Hp
  iapply HΦ; iframe; iframe #

theorem marSpec_PrepareReply (pm : Loc) (g : wire.gryffproto.PrepareReply.Msg) (sl : GoSlice) :
    marSpec (GF := GF) (go.GoType.PointerType src.gryffproto.PrepareReply.ty) pm (wire.gryffproto.PrepareReply.enc g)
      iprop(isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ pm ↦ wire.gryffproto.PrepareReply.goVal g sl ∗
        sl ↦*□ g.Command) := by
  intro w wr J Q s p er E0 D
  iintro %Φ ⟨#Hwr, #HQ, %Hp, Hw, #Hp1, #Hp2, Ho, #Hsl⟩ HΦ
  wp_apply (wire.gryffproto.PrepareReply.wp_Marshal_gen2 pm (DFrac.own 1) DFrac.discard g sl w wr J Q s p er
    E0 D) $$ [$Hwr $HQ $Hw $Ho $Hp1 $Hp2 $Hsl] as ⟨Hw, Ho, -⟩
  · ipureintro; exact Hp
  iapply HΦ; iframe; iframe #

theorem marSpec_Executed (pm : Loc) (g : wire.gryffproto.Executed.Msg) :
    marSpec (GF := GF) (go.GoType.PointerType src.gryffproto.Executed.ty) pm (wire.gryffproto.Executed.enc g)
      iprop(isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ wire.gryffproto.Executed.own pm (DFrac.own 1) g) := by
  intro w wr J Q s p er E0 D
  iintro %Φ ⟨#Hwr, #HQ, %Hp, Hw, #Hp1, #Hp2, Ho⟩ HΦ
  wp_apply (wire.gryffproto.Executed.wp_Marshal_gen pm (DFrac.own 1) g w wr J Q s p er E0 D)
    $$ [$Hwr $HQ $Hw $Ho $Hp1 $Hp2] as ⟨Hw, Ho⟩
  · ipureintro; exact Hp
  iapply HΦ; iframe; iframe #

theorem marSpec_Prepare (pm : Loc) (g : wire.epaxosproto.Prepare.Msg) :
    marSpec (GF := GF) (go.GoType.PointerType src.epaxosproto.Prepare.ty) pm (wire.epaxosproto.Prepare.enc g)
      iprop(isPkgInit (PROP := IProp GF) pkg_id.gryff.src.epaxosproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ wire.epaxosproto.Prepare.own pm (DFrac.own 1) g) := by
  intro w wr J Q s p er E0 D
  iintro %Φ ⟨#Hwr, #HQ, %Hp, Hw, #Hp1, #Hp2, Ho⟩ HΦ
  wp_apply (wire.epaxosproto.Prepare.wp_Marshal_gen pm (DFrac.own 1) g w wr J Q s p er E0 D)
    $$ [$Hwr $HQ $Hw $Ho $Hp1 $Hp2] as ⟨Hw, Ho⟩
  · ipureintro; exact Hp
  iapply HΦ; iframe; iframe #

theorem marSpec_PreAcceptOK (pm : Loc) (g : wire.epaxosproto.PreAcceptOK.Msg) :
    marSpec (GF := GF) (go.GoType.PointerType src.epaxosproto.PreAcceptOK.ty) pm (wire.epaxosproto.PreAcceptOK.enc g)
      iprop(isPkgInit (PROP := IProp GF) pkg_id.gryff.src.epaxosproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ wire.epaxosproto.PreAcceptOK.own pm (DFrac.own 1) g) := by
  intro w wr J Q s p er E0 D
  iintro %Φ ⟨#Hwr, #HQ, %Hp, Hw, #Hp1, #Hp2, Ho⟩ HΦ
  wp_apply (wire.epaxosproto.PreAcceptOK.wp_Marshal_gen pm (DFrac.own 1) g w wr J Q s p er E0 D)
    $$ [$Hwr $HQ $Hw $Ho $Hp1 $Hp2] as ⟨Hw, Ho⟩
  · ipureintro; exact Hp
  iapply HΦ; iframe; iframe #

theorem marSpec_AcceptReply (pm : Loc) (g : wire.epaxosproto.AcceptReply.Msg) :
    marSpec (GF := GF) (go.GoType.PointerType src.epaxosproto.AcceptReply.ty) pm (wire.epaxosproto.AcceptReply.enc g)
      iprop(isPkgInit (PROP := IProp GF) pkg_id.gryff.src.epaxosproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ wire.epaxosproto.AcceptReply.own pm (DFrac.own 1) g) := by
  intro w wr J Q s p er E0 D
  iintro %Φ ⟨#Hwr, #HQ, %Hp, Hw, #Hp1, #Hp2, Ho⟩ HΦ
  wp_apply (wire.epaxosproto.AcceptReply.wp_Marshal_gen pm (DFrac.own 1) g w wr J Q s p er E0 D)
    $$ [$Hwr $HQ $Hw $Ho $Hp1 $Hp2] as ⟨Hw, Ho⟩
  · ipureintro; exact Hp
  iapply HΦ; iframe; iframe #

end generic

end Perennial.gryff.netN
