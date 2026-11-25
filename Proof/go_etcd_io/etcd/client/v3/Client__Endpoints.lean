/-
The client's `Endpoints`, proved over its body (prove-ps2-clientrdlock, 2026-11-24, decision 1b;
until then a trust-boundary axiom). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Client__Endpoints

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (statusErrOk)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `Endpoints` read-locks `c.epMu` (a reader slot borrowed from `clientEpPool`'s level-0 pool with
the caller's `levelTok 0`), copies the read-only `c.endpoints` into a new slice, and read-unlocks
(deferred), giving the slot back. -/
theorem Client.Endpoints.wp_proof : Client.Endpoints.spec (GF := GF) (hG := hG) := by
  intro c
  wp_start as ⟨#Hc, Htok⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold retryClientOk at Hc
  icases Hc with ⟨%Hcn, #Hlg, %tok, %atb, -, -, -, #Hep⟩
  iunfold clientEpPool at Hep
  icases Hep with ⟨%mu, %γe, %esl, %eps, #Hmu, #Hesl, #Heps, #Hg, #Hpool⟩
  wp_auto_lc 1
  wp_apply wp_with_defer as %defer defer
  imod threadPool.borrowL_lc clientEpN 0 γe _ ⊤ (by simp) $$ [$Hlc1 $Hpool $Htok] with ⟨Hslot, Hloan⟩
  wp_apply (sync.RWMutex.wp_RLock mu (fun _ => iprop(True))) $$ [$Hslot] as ⟨Hlk, -⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Heps
  wp_apply (wp_slice_make2 (V := GoString) esl.len) as %sl ⟨Hsl, Hcap⟩
  · ipureintro; exact Hlen.2
  (try wp_auto)
  wp_apply (wp_slice_copy sl _ esl eps DFrac.discard) $$ [Hsl Heps] as %n ⟨%Hn, Hsl, -⟩
  · iframe Hsl Heps
  have Hcp : eps.take (List.replicate (sint.nat esl.len) (zero_val GoString)).length ++
      (List.replicate (sint.nat esl.len) (zero_val GoString)).drop eps.length = eps := by
    simp [List.length_replicate, ← Hlen.1]
  rw [Hcp]
  (try wp_auto)
  iapply wp_fupd
  wp_apply (sync.RWMutex.wp_RUnlock mu (fun _ => iprop(True))) $$ [$Hlk] as Hslot
  · inext; itrivial
  imod threadPool.giveBackL clientEpN 0 γe _ ⊤ (by simp) $$ [$Hpool $Hloan $Hslot] with Htok
  imodintro
  (try wp_auto)
  iapply HΦ
  iframe Htok
  iexists eps
  iframe Hsl
  iintro %esl' %eps0 Hesl' Heps0
  ihave %Heq := typedPointsto_agree_wand _ _ _ _ _ $$ Hesl Hesl'
  subst Heq
  iapply ownSlice_agree $$ Heps Heps0

end proof

end EtcdGrove
end Perennial
