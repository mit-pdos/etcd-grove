/-
Proof of `Spec/go_etcd_io/etcd/client/v3/experimental/recipes/WaitPrefixEvents.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.WaitPrefixEvents
public import Spec.go_etcd_io.etcd.client.v3.WithPrefix
public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.waitEvents
public import Spec.go_etcd_io.etcd.client.v3.WithRev
public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.InvRecipesLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

theorem WaitPrefixEvents.wp_proof (wp_WithPrefix : EtcdGrove.WithPrefix.spec (GF := GF) (hG := hG))
    (wp_WithRev : EtcdGrove.WithRev.spec (GF := GF) (hG := hG))
    (hWE : waitEvents.spec (GF := GF) (hG := hG)) :
    WaitPrefixEvents.spec (GF := GF) (hG := hG) := by
  intro c pfx key rev sl ts typ
  wp_start as ⟨#Hcci, #Hcl, #Hsl, %Hp⟩
  ihave #Hctxp : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Hcl' := Hcl
  iunfold isEtcdRecipesClient at Hcl'
  icases Hcl' with ⟨%kv, %w, -, #HWf, -, #HW⟩
  wp_auto
  wp_apply wp_with_defer
  iintro %defer Hdefer
  (try wp_auto)
  wp_apply context.wp_Background
  wp_apply context.wp_WithCancel_Background iprop(True) $$ [$Hctxp $Hcci]
      as %ctx' %γ' %cancel ⟨#Hcancel, #Hctx', -⟩
  ihave #Hcancel' := context.cancel_spec_forget _ _ _ $$ Hcancel
  (try wp_auto)
  wp_apply wp_WithPrefix $$ [$Hcv] as %f0 #Hf0
  wp_apply wp_WithRev rev $$ [$Hcv] as %f #Hf
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl' ⟨Hsl', -⟩
  ipersist Hsl'
  generalize hsl : slice.mk sl' _ _ = optsSl
  ihave #Hopts : optsAt optsSl ([withPrefixM, withRevM rev] : List (OpFull → OpFull)) $$ []
  · iunfold optsAt
    iexists _
    iframe Hsl'
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %f' %g %Hf' %Hg
    rcases i with _ | _ | i
    · cases Hf'; cases Hg; iexact Hf0
    · cases Hf'; cases Hg; iexact Hf
    · simp at Hf'
  iunfold isEtcdRangeWatcherOpen at HW
  ihave #HWa := HW $$ %ctx' %({ Values := ∅, Deadline := none, Done_gn := γ', PDone := iprop(True) } : context.ContextDesc (IProp GF))
    %key %optsSl %([withPrefixM, withRevM rev] : List (OpFull → OpFull)) %rev
  (try wp_auto)
  obtain ⟨Hw1, Hw2, -⟩ := prefixWatchOp_fields key rev
  have Hw3 := prefixWatchOp_under pfx key rev Hp.2.1
  unfold prefixWatchOp at Hw1 Hw3
  wp_apply HWa $$ [] as %wch %γw ⟨#Hwch, Hcons, -⟩
  · iframe Hctx' Hopts
    ipureintro
    exact ⟨Hw1, Hw2, Hp.2.2, Hw3⟩
  ihave %Hnn : ⌜wch ≠ null⌝ $$ [Hwch]
  · iunfold isSpsc at Hwch
    icases Hwch with ⟨#Hch, -⟩
    iapply isChan_not_null wch γw.spsc.chanName go_etcd_io.etcd.client.v3.WatchResponse $$ Hch
  (try wp_auto)
  have Hnn' : wch ≠ chan.nil := Hnn
  rw [decide_eq_false Hnn']
  (try wp_auto)
  wp_apply hWE wch γw pfx (opWatchModel key [withPrefixM, withRevM rev]) rev [] sl ts typ $$ [$Hwch $Hcons $Hsl]
      as %ev ⟨#Hev, -⟩
  · ipureintro; exact Hp.1
  (try wp_auto)
  wp_apply Hcancel'
  · imodintro; itrivial
  (try wp_auto)
  iapply HΦ
  isplitr
  · ipureintro; rfl
  unfold prefixWatchOp
  iexact Hev

end proof

end recipes
end EtcdGrove
end Perennial
