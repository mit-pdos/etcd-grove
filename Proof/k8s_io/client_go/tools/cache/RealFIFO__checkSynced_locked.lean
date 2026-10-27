/-
Proof of `Spec/k8s_io/client_go/tools/cache/RealFIFO__checkSynced_locked.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.RealFIFO__checkSynced_locked

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem RealFIFO.checkSynced_locked.wp_proof :
    RealFIFO.checkSynced_locked.spec (GF := GF) (hG := hG) := by
  intro f ch γch Q p n b
  wp_start as ⟨Hp, Hn, %hn, Hb, #Hch, Hbc, HQ⟩
  (try wp_auto)
  by_cases hn0 : n = 0
  · subst hn0
    cases p with
    | false =>
      (try wp_auto)
      iapply HΦ
      simp only [syncsNow, Bool.false_and, Bool.or_false]
      iframe
    | true =>
      (try wp_auto)
      cases b with
      | true =>
        (try wp_auto)
        iapply HΦ
        simp only [syncsNow, Bool.not_true, Bool.and_false, Bool.or_false]
        iframe
      | false =>
        (try wp_auto)
        ihave #HQ' := HQ $$ %rfl
        simp only [Bool.false_eq_true, ↓reduceIte]
        wp_apply wp_broadcast_chan_close $$ [$Hbc $HQ'] as Hbc
        (try wp_auto)
        iapply HΦ
        simp only [syncsNow]
        iframe
  · have hw : (W64 (n : Int)) ≠ W64 0 := by
      intro h; apply hn0
      have := congrArg (fun w : w64 => w.toNat) h
      simp at this; omega
    have hs : ∀ p b, syncsNow p n b = false := by intro p b; simp [syncsNow, hn0]
    cases p <;> (try wp_auto) <;> (try simp only [decide_eq_false hw]) <;> (try wp_auto) <;>
      (iapply HΦ; rw [hs]; simp only [Bool.or_false]; iframe)

end proof

end cache
end EtcdGrove
end Perennial
