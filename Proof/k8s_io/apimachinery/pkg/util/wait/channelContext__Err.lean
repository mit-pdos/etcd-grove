/-
The proof of `Spec/k8s_io/apimachinery/pkg/util/wait/channelContext__Err.lean` (translated code):
the `select`'s receive at the channel's internal names (`BroadcastInternal.lean`). Lean-first.
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.wait.channelContext__Err
public import Proof.k8s_io.apimachinery.pkg.util.wait.BroadcastInternal

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [wait_sem : k8s_io.apimachinery.pkg.util.wait.Assumptions] [ctx_sem : context.Assumptions]

theorem wait.channelContext.Err.wp_proof : wait.channelContext.Err.spec (GF := GF) (hG := hG) := by
  intro sc γs γi Q cl
  rcases cl with _ | _ | _
  · -- `.Pending`
    dsimp only
    wp_start as ⟨#Hint, Hcl⟩
    ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
    · iPkgInit
    ihave Hci : (context.isInit : IProp GF) $$ []
    · iapply context.isInit_access $$ Pctx
    iNamed Hci
    icases HCanceled with ⟨%eC, #HeC, %-⟩
    wp_auto
    wp_apply_core (wp_select_internal sc γs γi Q .Unknown) $$ Hint []
    dsimp only
    isplit
    · iintro #Hd
      wp_auto
      iapply HΦ
      iright
      iframe HeC Hd
    · wp_auto
      iapply HΦ
      ileft
      ipureintro; exact ⟨rfl, nofun⟩
  · -- `.Done`: the flag known, the channel closed
    dsimp only
    wp_start as ⟨#Hint, Hcl⟩
    ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
    · iPkgInit
    ihave Hci : (context.isInit : IProp GF) $$ []
    · iapply context.isInit_access $$ Pctx
    iNamed Hci
    icases HCanceled with ⟨%eC, #HeC, %-⟩
    wp_auto
    wp_apply_core (wp_select_internal sc γs γi Q .Done) $$ Hint Hcl
    isplit
    · iintro #Hd
      wp_auto
      iapply HΦ
      iright
      iframe HeC Hd
    · itrivial
  · -- `.Unknown`
    dsimp only
    wp_start as ⟨#Hint, Hcl⟩
    ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
    · iPkgInit
    ihave Hci : (context.isInit : IProp GF) $$ []
    · iapply context.isInit_access $$ Pctx
    iNamed Hci
    icases HCanceled with ⟨%eC, #HeC, %-⟩
    wp_auto
    wp_apply_core (wp_select_internal sc γs γi Q .Unknown) $$ Hint []
    dsimp only
    isplit
    · iintro #Hd
      wp_auto
      iapply HΦ
      iright
      iframe HeC Hd
    · wp_auto
      iapply HΦ
      ileft
      ipureintro; exact ⟨rfl, nofun⟩

end proof

end EtcdGrove
end Perennial
