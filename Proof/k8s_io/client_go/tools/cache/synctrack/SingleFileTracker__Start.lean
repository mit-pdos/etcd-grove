/-
Proof of `Spec/k8s_io/client_go/tools/cache/synctrack/SingleFileTracker__Start.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.synctrack.SingleFileTracker__Start

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

theorem SingleFileTracker.Start.wp_proof :
    SingleFileTracker.Start.spec (GF := GF) (hG := hG) := by
  intro t γ Hbound
  wp_start as #Hsft
  ihave #Hat : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  iunfold isSFT at Hsft
  icases Hsft with ⟨%f, #Hf, #Hcancel, #Hinv⟩
  wp_take_receipt as Hr
  wp_apply_core sync.atomic.wp_AddInt64 _ _ $$ %_ Hat
  iinv Hinv with Hi Hclose
  iunfold sftInv at Hi
  icases Hi with ⟨%n, %b, >%Hn63, >Hc, >Ha, >Hk, >Hb⟩
  icases receipt_add_one_lt n $$ [Hr Hk] with ⟨%Hlt, Hk⟩
  · iframe
  have H63 : n + 1 < 2 ^ 63 := Nat.lt_of_lt_of_le Hlt Hbound
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists W64 (n : Int)
  iframe Hc
  iintro Hc
  imod Hmask
  imod ownTokAuth_S γ n $$ Ha with ⟨Ha, Htok⟩
  have Hadd : W64 (n : Int) + W64 1 = W64 ((n + 1 : Nat) : Int) := by word
  rw [Hadd]
  imod Hclose $$ [Hc Ha Hk Hb] with -
  · inext; iunfold sftInv; iexists n + 1, b; iframe; ipureintro; exact H63
  imodintro
  wp_auto
  iapply HΦ
  unfold sftTok
  iexact Htok

end proof

end synctrack
end EtcdGrove
end Perennial
