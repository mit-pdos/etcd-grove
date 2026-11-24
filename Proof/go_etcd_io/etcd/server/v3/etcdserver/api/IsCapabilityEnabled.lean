/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/IsCapabilityEnabled.lean` (prove-ps2-cap,
2026-11-23; until then the trust-boundary axiom of unit P3b): a reader slot of `enableMapMu`
borrowed from the package's pool (`capInit`, `CapPool.lean`) with the level-0 token, the read
lock, `enabledMap`'s read, and the slot given back. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.IsCapabilityEnabled

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.Assumptions]

theorem api.IsCapabilityEnabled.wp_proof : api.IsCapabilityEnabled.spec (GF := GF) (hG := hG) := by
  intro _ c
  have Hb := ThreadBoundLe.le (GF := GF) (2 ^ 30)
  wp_start as Htok
  ihave Hi : (capInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  iunfold capInit at Hi
  icases Hi $$ %Hb with ⟨%γ, -, #HP⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iapply fupd_wp
  imod threadPool.borrowL capPoolN 0 γ (sync.ownRWMutex (globalAddr enableMapMu) capMapP) ⊤
    (fun _ _ => CoPset.mem_full) $$ [HP Htok] with ⟨Hslot, Hloan⟩
  · iframe #; iframe
  imodintro
  wp_auto
  wp_apply wp_with_defer as %defer defer
  wp_apply (sync.RWMutex.wp_RLock (globalAddr enableMapMu) capMapP) $$ [$Hslot] as ⟨Hlk, HR⟩
  iunfold capMapP at HR
  icases HR with ⟨%m, Hm, #Hc⟩
  wp_auto
  wp_if_destruct
  · -- `enabledMap == nil`: `false`
    try wp_auto
    iapply wp_fupd
    wp_apply (sync.RWMutex.wp_RUnlock (globalAddr enableMapMu) capMapP) $$ [$Hlk Hm] as Hslot
    · inext; iunfold capMapP; iexists _; iframe Hm; ileft; ipureintro; rfl
    imod threadPool.giveBackL capPoolN 0 γ (sync.ownRWMutex (globalAddr enableMapMu) capMapP) ⊤
      (fun _ _ => CoPset.mem_full) $$ [HP Hloan Hslot] with Htok
    · iframe #; iframe
    imodintro
    (try wp_auto)
    iapply HΦ
    iexact Htok
  · ihave #Hmm : iprop(∃ mm : GMap GoString Bool, m ↦$□ mm) $$ []
    · icases Hc with (%Hnil | #Hmm)
      · exact absurd Hnil (by assumption)
      · iexact Hmm
    icases Hmm with ⟨%mm, #Hmm⟩
    wp_apply (wp_map_lookup1 (K := GoString) (V := Bool) Capability.ty go.bool m mm c DFrac.discard)
      $$ Hmm as -
    try wp_auto
    iapply wp_fupd
    wp_apply (sync.RWMutex.wp_RUnlock (globalAddr enableMapMu) capMapP) $$ [$Hlk Hm] as Hslot
    · inext; iunfold capMapP; iexists m; iframe Hm; iexact Hc
    imod threadPool.giveBackL capPoolN 0 γ (sync.ownRWMutex (globalAddr enableMapMu) capMapP) ⊤
      (fun _ _ => CoPset.mem_full) $$ [HP Hloan Hslot] with Htok
    · iframe #; iframe
    imodintro
    (try wp_auto)
    iapply HΦ
    iexact Htok

end proof

end EtcdGrove
end Perennial
