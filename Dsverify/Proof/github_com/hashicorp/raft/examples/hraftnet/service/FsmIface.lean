/-
The hraft kit's store meets raft's FSM contract (`iface/FSM.lean`): `store_isFSM`, from the specs of
the store's methods (hypotheses, which the kit's linking module passes), and `store_fsmNotBatching`.
Adapted from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/examples/hr3/
ServerFSM.lean (241f27e).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.Store__Apply
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.Store__Snapshot
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.Store__Restore
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.snapshot__Persist
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.snapshot__Release
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.Store__StoreConfiguration

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft.examples.hraftnet.service

open github_com.hashicorp.raft proto gprot

section fsm
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.service.Assumptions]

/-- A `*snapshot` value of `x` is an `FSMSnapshot` of `x` (`Persist`, `Release`). -/
theorem snapVal_fsmSnapOk
    (wp_Persist : github_com.hashicorp.raft.examples.hraftnet.service.snapshot.Persist.spec (GF := GF) (hG := hG))
    (wp_Release : github_com.hashicorp.raft.examples.hraftnet.service.snapshot.Release.spec (GF := GF) (hG := hG))
    (γ : GNames) (fc : FCtx GF) (sn : Loc) (x : Nat) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.service ∗
      snapVal γ fc sn x ⊢
      fsmSnapOk (interface.mk (go.GoType.PointerType snapshot.ty) #sn) (snapP γ fc) x := by
  iintro ⟨#Hinit, #Hsv⟩
  unfold fsmSnapOk
  isplitr
  · imodintro
    iintro %k %id %own %Q %R %Φ #Hsink #HQ Hown HΦ
    iapply (wp_Persist γ fc sn x k id own Q R) $$ [Hown]
    · iframe; iframe #
    inext
    iexact HΦ
  · imodintro
    iintro %Φ HΦ
    iapply (wp_Release sn) $$ []
    · iframe #
    inext
    iintro -
    iexact HΦ

/-- **Server `i`'s store `s` is its FSM**, with state `fsmOwn alb`, responses `respP γ fc alb` and
snapshots `snapP γ fc`. -/
theorem store_isFSM
    (wp_Apply : github_com.hashicorp.raft.examples.hraftnet.service.Store.Apply.spec (GF := GF) (hG := hG))
    (wp_Snapshot : github_com.hashicorp.raft.examples.hraftnet.service.Store.Snapshot.spec (GF := GF) (hG := hG))
    (wp_Restore : github_com.hashicorp.raft.examples.hraftnet.service.Store.Restore.spec (GF := GF) (hG := hG))
    (wp_Persist : github_com.hashicorp.raft.examples.hraftnet.service.snapshot.Persist.spec (GF := GF) (hG := hG))
    (wp_Release : github_com.hashicorp.raft.examples.hraftnet.service.snapshot.Release.spec (GF := GF) (hG := hG))
    (wp_StoreConfiguration :
      github_com.hashicorp.raft.examples.hraftnet.service.Store.StoreConfiguration.spec (GF := GF) (hG := hG))
    (γ : GNames) (fc : FCtx GF) (alb : GName) (i : SID) (s : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.service ∗
      isStore γ fc alb i s ⊢
      isFSM (interface.mk (go.GoType.PointerType Store.ty) #s) γ i (fsmOwn alb) (respP γ fc alb)
        (snapP γ fc) := by
  iintro ⟨#Hinit, #Hst⟩
  unfold isFSM
  isplitr
  · imodintro
    iintro %k %r #H
    imodintro
    iexact H
  isplitr
  · imodintro
    iintro %k %b #H
    imodintro
    iexact H
  isplitr
  · imodintro
    iintro %l %k0 %k %e %Φ Hown #Hl %Hk #Hc #Hdur #Hnc HΦ
    iapply (wp_Apply γ fc alb i s l k0 k e) $$ [Hown]
    · iframe; iframe #; ipureintro; exact Hk
    inext
    iintro %r ⟨Hown, Hr⟩
    iapply HΦ $$ Hown Hr
  isplitr
  · imodintro
    iintro %k0 %x %r %Φ Hown %Hk0 #Hnc -  HΦ
    iapply (wp_Snapshot γ fc alb i s k0 x) $$ [Hown]
    · iframe; iframe #; ipureintro; exact Hk0
    inext
    iintro %sn ⟨Hown, #Hsv⟩
    iapply HΦ $$ Hown
    iapply snapVal_fsmSnapOk wp_Persist wp_Release γ fc sn x $$ [Hinit Hsv]
    iframe #
  isplitr
  · imodintro
    iintro %k0 %x %rd %R %b %eof %Φ Hown %Hk0 #Heof #Hrd HR #Hsp HΦ
    iapply (wp_Restore γ fc alb i s k0 x rd R b eof) $$ [Hown HR]
    · iframe; iframe #; ipureintro; exact Hk0
    inext
    iintro ⟨%k0', %r, Hown, %Hk0', #Hnc, Hr⟩
    iapply HΦ $$ %k0' %r Hown %Hk0' Hnc Hr
  · imodintro
    iintro %_hcs %k0 %k %e %c %ss %Φ Hown %_hk #_Hc #_Hdur _Hsl HΦ
    iapply (wp_StoreConfiguration s (W64 k) c) $$ []
    · iframe #
    inext
    iintro -
    iapply HΦ $$ Hown

/-- `*Store` does not implement `BatchingFSM`; it is a `ConfigurationStore`. -/
theorem store_fsmNotBatching (s : Loc) :
    fsmNotBatching (interface.mk (go.GoType.PointerType Store.ty) #s) := by
  unfold fsmNotBatching
  constructor <;> go_type_set

end fsm

end github_com.hashicorp.raft.examples.hraftnet.service
end Perennial
