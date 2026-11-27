/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/SnapFut.lean (241f27e).
-/
/-
(stage 3, snap) `init`, `respond` and `Error` promoted through raft's own futures of the snapshot
paths (`*userSnapshotFuture`, `*restoreFuture`, `*reqSnapshotFuture`, `*configurationsFuture`), as
`FutBase`'s for `*verifyFuture`; `respond`/`Error` are instances of `deferError.respond.spec` and
`deferError.Error.spec` (any `*deferError`).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.deferError__respond
public import Dsverify.Spec.github_com.hashicorp.raft.deferError__Error

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft proto

namespace github_com.hashicorp.raft.snapFut

theorem wp_uf_init (f : Loc) (Q : GoInterface → IProp GF) (ch0 : Loc) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
     (f.[userSnapshotFuture, go!"deferError"]).[deferError, go!"errCh"] ↦ ch0 }}
    (App (Val (f @!! go.GoType.PointerType userSnapshotFuture.ty @!! go!"init")) (Val #()))
  {{ RET #(); ∃ (ch : Loc) (γe : SpscNames), ⌜ch ≠ chan.nil⌝ ∗
      (f.[userSnapshotFuture, go!"deferError"]).[deferError, go!"errCh"] ↦ ch ∗
      isSpsc (V := GoInterface) γe ch (fun n v => iprop(⌜n = 0⌝ ∗ Q v)) (fun sent => iprop(⌜sent ≠ []⌝)) ∗
      spscProducer γe ([] : List GoInterface) ∗ spscConsumer γe ([] : List GoInterface) }} := by
  wp_start as Hch
  wp_method_call
  wp_call
  iapply wp_fupd
  wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 1)) as %ch %γc ⟨#Hisch, %Hcap, Hown⟩
  · ipureintro; decide
  ihave %Hnn := isChan_not_null (ch := ch) (γ := γc) (V := GoInterface) $$ Hisch
  imod start_spsc ch (fun n v => iprop(⌜n = 0⌝ ∗ Q v)) (fun sent => iprop(⌜sent ≠ []⌝)) γc $$ Hisch [Hown]
    with ⟨%γe, #Hspsc, Hprod, Hcons⟩
  · iright; iexact Hown
  imodintro
  iapply HΦ
  iexists ch, γe
  iframe
  iframe #
  ipureintro; exact Hnn

theorem wp_uf_respond
    (wp_respond : github_com.hashicorp.raft.deferError.respond.spec (GF := GF) (hG := hG))
    (f : Loc) (Q : GoInterface → IProp GF) (err : GoInterface) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
     ((deferResp (f.[userSnapshotFuture, go!"deferError"]) Q ∗ Q err) ∨ deferDone (f.[userSnapshotFuture, go!"deferError"])) }}
    (App (Val (f @!! go.GoType.PointerType userSnapshotFuture.ty @!! go!"respond")) (Val #err))
  {{ RET #(); deferDone (f.[userSnapshotFuture, go!"deferError"]) }} := by
  have h := wp_respond (f.[userSnapshotFuture, go!"deferError"]) Q err
  wp_start as Hpre
  wp_method_call
  have e := MethodUnfold.method_unfold (t := go.GoType.PointerType deferError.ty) (m := go!"respond")
    #(f.[userSnapshotFuture, go!"deferError"])
  simp only [e] at h
  iapply h $$ [$Hpkg $Hpre] HΦ

theorem wp_uf_Error
    (wp_Error : github_com.hashicorp.raft.deferError.Error.spec (GF := GF) (hG := hG))
    (f : Loc) (Q : GoInterface → IProp GF) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
     deferWait (f.[userSnapshotFuture, go!"deferError"]) Q }}
    (App (Val (f @!! go.GoType.PointerType userSnapshotFuture.ty @!! go!"Error")) (Val #()))
  {{ (err : GoInterface), RET #err; Q err }} := by
  have h := wp_Error.2.2.2.2.2 (f.[userSnapshotFuture, go!"deferError"]) Q
  wp_start as Hpre
  wp_method_call
  have e := MethodUnfold.method_unfold (t := go.GoType.PointerType deferError.ty) (m := go!"Error")
    #(f.[userSnapshotFuture, go!"deferError"])
  simp only [e] at h
  iapply h $$ %Φ [$Hpkg $Hpre]
  inext; iintro %err Hq
  iapply HΦ $$ Hq

theorem wp_rf_init (f : Loc) (Q : GoInterface → IProp GF) (ch0 : Loc) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
     (f.[restoreFuture, go!"deferError"]).[deferError, go!"errCh"] ↦ ch0 }}
    (App (Val (f @!! go.GoType.PointerType restoreFuture.ty @!! go!"init")) (Val #()))
  {{ RET #(); ∃ (ch : Loc) (γe : SpscNames), ⌜ch ≠ chan.nil⌝ ∗
      (f.[restoreFuture, go!"deferError"]).[deferError, go!"errCh"] ↦ ch ∗
      isSpsc (V := GoInterface) γe ch (fun n v => iprop(⌜n = 0⌝ ∗ Q v)) (fun sent => iprop(⌜sent ≠ []⌝)) ∗
      spscProducer γe ([] : List GoInterface) ∗ spscConsumer γe ([] : List GoInterface) }} := by
  wp_start as Hch
  wp_method_call
  wp_call
  iapply wp_fupd
  wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 1)) as %ch %γc ⟨#Hisch, %Hcap, Hown⟩
  · ipureintro; decide
  ihave %Hnn := isChan_not_null (ch := ch) (γ := γc) (V := GoInterface) $$ Hisch
  imod start_spsc ch (fun n v => iprop(⌜n = 0⌝ ∗ Q v)) (fun sent => iprop(⌜sent ≠ []⌝)) γc $$ Hisch [Hown]
    with ⟨%γe, #Hspsc, Hprod, Hcons⟩
  · iright; iexact Hown
  imodintro
  iapply HΦ
  iexists ch, γe
  iframe
  iframe #
  ipureintro; exact Hnn

theorem wp_rf_respond
    (wp_respond : github_com.hashicorp.raft.deferError.respond.spec (GF := GF) (hG := hG))
    (f : Loc) (Q : GoInterface → IProp GF) (err : GoInterface) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
     ((deferResp (f.[restoreFuture, go!"deferError"]) Q ∗ Q err) ∨ deferDone (f.[restoreFuture, go!"deferError"])) }}
    (App (Val (f @!! go.GoType.PointerType restoreFuture.ty @!! go!"respond")) (Val #err))
  {{ RET #(); deferDone (f.[restoreFuture, go!"deferError"]) }} := by
  have h := wp_respond (f.[restoreFuture, go!"deferError"]) Q err
  wp_start as Hpre
  wp_method_call
  have e := MethodUnfold.method_unfold (t := go.GoType.PointerType deferError.ty) (m := go!"respond")
    #(f.[restoreFuture, go!"deferError"])
  simp only [e] at h
  iapply h $$ [$Hpkg $Hpre] HΦ

theorem wp_rf_Error
    (wp_Error : github_com.hashicorp.raft.deferError.Error.spec (GF := GF) (hG := hG))
    (f : Loc) (Q : GoInterface → IProp GF) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
     deferWait (f.[restoreFuture, go!"deferError"]) Q }}
    (App (Val (f @!! go.GoType.PointerType restoreFuture.ty @!! go!"Error")) (Val #()))
  {{ (err : GoInterface), RET #err; Q err }} := by
  have h := wp_Error.2.2.2.2.2 (f.[restoreFuture, go!"deferError"]) Q
  wp_start as Hpre
  wp_method_call
  have e := MethodUnfold.method_unfold (t := go.GoType.PointerType deferError.ty) (m := go!"Error")
    #(f.[restoreFuture, go!"deferError"])
  simp only [e] at h
  iapply h $$ %Φ [$Hpkg $Hpre]
  inext; iintro %err Hq
  iapply HΦ $$ Hq

theorem wp_sf_init (f : Loc) (Q : GoInterface → IProp GF) (ch0 : Loc) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
     (f.[reqSnapshotFuture, go!"deferError"]).[deferError, go!"errCh"] ↦ ch0 }}
    (App (Val (f @!! go.GoType.PointerType reqSnapshotFuture.ty @!! go!"init")) (Val #()))
  {{ RET #(); ∃ (ch : Loc) (γe : SpscNames), ⌜ch ≠ chan.nil⌝ ∗
      (f.[reqSnapshotFuture, go!"deferError"]).[deferError, go!"errCh"] ↦ ch ∗
      isSpsc (V := GoInterface) γe ch (fun n v => iprop(⌜n = 0⌝ ∗ Q v)) (fun sent => iprop(⌜sent ≠ []⌝)) ∗
      spscProducer γe ([] : List GoInterface) ∗ spscConsumer γe ([] : List GoInterface) }} := by
  wp_start as Hch
  wp_method_call
  wp_call
  iapply wp_fupd
  wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 1)) as %ch %γc ⟨#Hisch, %Hcap, Hown⟩
  · ipureintro; decide
  ihave %Hnn := isChan_not_null (ch := ch) (γ := γc) (V := GoInterface) $$ Hisch
  imod start_spsc ch (fun n v => iprop(⌜n = 0⌝ ∗ Q v)) (fun sent => iprop(⌜sent ≠ []⌝)) γc $$ Hisch [Hown]
    with ⟨%γe, #Hspsc, Hprod, Hcons⟩
  · iright; iexact Hown
  imodintro
  iapply HΦ
  iexists ch, γe
  iframe
  iframe #
  ipureintro; exact Hnn

theorem wp_sf_respond
    (wp_respond : github_com.hashicorp.raft.deferError.respond.spec (GF := GF) (hG := hG))
    (f : Loc) (Q : GoInterface → IProp GF) (err : GoInterface) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
     ((deferResp (f.[reqSnapshotFuture, go!"deferError"]) Q ∗ Q err) ∨ deferDone (f.[reqSnapshotFuture, go!"deferError"])) }}
    (App (Val (f @!! go.GoType.PointerType reqSnapshotFuture.ty @!! go!"respond")) (Val #err))
  {{ RET #(); deferDone (f.[reqSnapshotFuture, go!"deferError"]) }} := by
  have h := wp_respond (f.[reqSnapshotFuture, go!"deferError"]) Q err
  wp_start as Hpre
  wp_method_call
  have e := MethodUnfold.method_unfold (t := go.GoType.PointerType deferError.ty) (m := go!"respond")
    #(f.[reqSnapshotFuture, go!"deferError"])
  simp only [e] at h
  iapply h $$ [$Hpkg $Hpre] HΦ

theorem wp_sf_Error
    (wp_Error : github_com.hashicorp.raft.deferError.Error.spec (GF := GF) (hG := hG))
    (f : Loc) (Q : GoInterface → IProp GF) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
     deferWait (f.[reqSnapshotFuture, go!"deferError"]) Q }}
    (App (Val (f @!! go.GoType.PointerType reqSnapshotFuture.ty @!! go!"Error")) (Val #()))
  {{ (err : GoInterface), RET #err; Q err }} := by
  have h := wp_Error.2.2.2.2.2 (f.[reqSnapshotFuture, go!"deferError"]) Q
  wp_start as Hpre
  wp_method_call
  have e := MethodUnfold.method_unfold (t := go.GoType.PointerType deferError.ty) (m := go!"Error")
    #(f.[reqSnapshotFuture, go!"deferError"])
  simp only [e] at h
  iapply h $$ %Φ [$Hpkg $Hpre]
  inext; iintro %err Hq
  iapply HΦ $$ Hq

theorem wp_cf_init (f : Loc) (Q : GoInterface → IProp GF) (ch0 : Loc) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
     (f.[configurationsFuture, go!"deferError"]).[deferError, go!"errCh"] ↦ ch0 }}
    (App (Val (f @!! go.GoType.PointerType configurationsFuture.ty @!! go!"init")) (Val #()))
  {{ RET #(); ∃ (ch : Loc) (γe : SpscNames), ⌜ch ≠ chan.nil⌝ ∗
      (f.[configurationsFuture, go!"deferError"]).[deferError, go!"errCh"] ↦ ch ∗
      isSpsc (V := GoInterface) γe ch (fun n v => iprop(⌜n = 0⌝ ∗ Q v)) (fun sent => iprop(⌜sent ≠ []⌝)) ∗
      spscProducer γe ([] : List GoInterface) ∗ spscConsumer γe ([] : List GoInterface) }} := by
  wp_start as Hch
  wp_method_call
  wp_call
  iapply wp_fupd
  wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 1)) as %ch %γc ⟨#Hisch, %Hcap, Hown⟩
  · ipureintro; decide
  ihave %Hnn := isChan_not_null (ch := ch) (γ := γc) (V := GoInterface) $$ Hisch
  imod start_spsc ch (fun n v => iprop(⌜n = 0⌝ ∗ Q v)) (fun sent => iprop(⌜sent ≠ []⌝)) γc $$ Hisch [Hown]
    with ⟨%γe, #Hspsc, Hprod, Hcons⟩
  · iright; iexact Hown
  imodintro
  iapply HΦ
  iexists ch, γe
  iframe
  iframe #
  ipureintro; exact Hnn

theorem wp_cf_respond
    (wp_respond : github_com.hashicorp.raft.deferError.respond.spec (GF := GF) (hG := hG))
    (f : Loc) (Q : GoInterface → IProp GF) (err : GoInterface) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
     ((deferResp (f.[configurationsFuture, go!"deferError"]) Q ∗ Q err) ∨ deferDone (f.[configurationsFuture, go!"deferError"])) }}
    (App (Val (f @!! go.GoType.PointerType configurationsFuture.ty @!! go!"respond")) (Val #err))
  {{ RET #(); deferDone (f.[configurationsFuture, go!"deferError"]) }} := by
  have h := wp_respond (f.[configurationsFuture, go!"deferError"]) Q err
  wp_start as Hpre
  wp_method_call
  have e := MethodUnfold.method_unfold (t := go.GoType.PointerType deferError.ty) (m := go!"respond")
    #(f.[configurationsFuture, go!"deferError"])
  simp only [e] at h
  iapply h $$ [$Hpkg $Hpre] HΦ

theorem wp_cf_Error
    (wp_Error : github_com.hashicorp.raft.deferError.Error.spec (GF := GF) (hG := hG))
    (f : Loc) (Q : GoInterface → IProp GF) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
     deferWait (f.[configurationsFuture, go!"deferError"]) Q }}
    (App (Val (f @!! go.GoType.PointerType configurationsFuture.ty @!! go!"Error")) (Val #()))
  {{ (err : GoInterface), RET #err; Q err }} := by
  have h := wp_Error.2.2.2.2.2 (f.[configurationsFuture, go!"deferError"]) Q
  wp_start as Hpre
  wp_method_call
  have e := MethodUnfold.method_unfold (t := go.GoType.PointerType deferError.ty) (m := go!"Error")
    #(f.[configurationsFuture, go!"deferError"])
  simp only [e] at h
  iapply h $$ %Φ [$Hpkg $Hpre]
  inext; iintro %err Hq
  iapply HΦ $$ Hq

end github_com.hashicorp.raft.snapFut

end proof

end Perennial
