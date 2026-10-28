/-
Proof of `Spec/k8s_io/client_go/tools/cache/synctrack/SingleFileTracker__Finished.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.synctrack.SingleFileTracker__Finished

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace synctrack

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache.synctrack

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.synctrack.Assumptions]

theorem SingleFileTracker.Finished.wp_proof :
    SingleFileTracker.Finished.spec (GF := GF) (hG := hG) := by
  intro t γ
  wp_start as ⟨#Hsft, Htok⟩
  ihave #Hat : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  iunfold isSFT at Hsft
  icases Hsft with ⟨%f, #Hf, #Hcancel, #Hinv⟩
  wp_auto
  wp_apply_core sync.atomic.wp_AddInt64 _ _ $$ %_ Hat
  iinv Hinv with Hi Hclose
  iunfold sftInv at Hi
  icases Hi with ⟨%n, %b, >%Hn63, >Hc, >Ha, >Hk, >Hb⟩
  unfold sftTok
  icombine Ha Htok gives %Hle
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  ihave %Hlt := receipt_lt (m + 1) $$ Hk
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists W64 ((m + 1 : Nat) : Int)
  iframe Hc
  iintro Hc
  imod Hmask
  imod ownTokAuth_delete_S γ m $$ Ha Htok with Ha
  icases (receipt_add m 1).1 $$ Hk with ⟨Hk, -⟩
  have Hsub : W64 ((m + 1 : Nat) : Int) + W64 (-1) = W64 (m : Int) := by word
  imod Hclose $$ [Hc Ha Hk Hb] with -
  · inext; iunfold sftInv; iexists m, b; rw [Hsub]; iframe; ipureintro; omega
  imodintro
  rw [Hsub]
  have Hnn : ¬ sint.Z (W64 (m : Int)) < sint.Z (W64 0) := by word
  wp_auto
  simp only [Hnn, decide_false]
  wp_auto
  by_cases hm : m = 0
  · subst hm
    wp_auto
    wp_apply_core sync.atomic.Bool.wp_Load _ (DFrac.own 1) $$ %_ Hat
    iinv Hinv with Hi Hclose
    iunfold sftInv at Hi
    icases Hi with ⟨%n, %b, >%Hn63', >Hc, >Ha, >Hk, >Hb⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists b
    iframe Hb
    iintro Hb
    imod Hmask
    imod Hclose $$ [Hc Ha Hk Hb] with -
    · inext; iunfold sftInv; iexists n, b; iframe; ipureintro; exact Hn63'
    imodintro
    cases b
    · wp_auto
      iapply HΦ; itrivial
    · wp_auto
      wp_apply Hcancel
      (try wp_auto)
      iapply HΦ; itrivial
  · have hne : (W64 (m : Int)) ≠ W64 0 := by intro h; apply hm; word
    simp only [hne, decide_false]
    wp_auto
    iapply HΦ; itrivial

end proof

end synctrack
end EtcdGrove
end Perennial
