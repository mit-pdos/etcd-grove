/-
`(*perRPCCredential).GetRequestMetadata`, proved over its body (prove-ps2-clientrdlock, 2026-11-24;
the auth plan's C1, `notes/c1-plan.md`, finding 2: until then a trust-boundary axiom). Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.credentials.perRPCCredential__GetRequestMetadata

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.credentials.Assumptions]

/-- `GetRequestMetadata` reads `rc.authToken` under `authTokenMu.RLock()`, a reader slot borrowed
from `credTokInv`'s level-0 pool with the caller's `levelTok 0` and given back after `RUnlock`, and
returns `nil, nil` for `""`, else `map[string]string{"token": t}, nil`
(`rpctypes.TokenFieldNameGRPC`, `rpctypes`' package fact). -/
theorem credentials.perRPCCredential.GetRequestMetadata.wp_proof :
    credentials.perRPCCredential.GetRequestMetadata.spec (GF := GF) (hG := hG) := by
  intro rc P ctx sl
  wp_start as ⟨#Hinv, Htok⟩
  iunfold credTokInv at Hinv
  icases Hinv with ⟨%Htb, #Hsync, #Hrpc, #Hg, %γp, #Hpool⟩
  ihave Hri : (go_etcd_io.etcd.cache.v3.rpctypesInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hrpc
  icases Hri with ⟨-, -, -, -, -, -, -, -, -, #Htf, -⟩
  wp_auto_lc 1
  imod threadPool.borrowL_lc credTokN 0 γp _ ⊤ (by simp) $$ [$Hlc1 $Hpool $Htok] with ⟨Hslot, Hloan⟩
  wp_apply (sync.RWMutex.wp_RLock _ (credTokR rc P)) $$ [$Hslot] as ⟨Hlk, HR⟩
  iunfold credTokR at HR
  icases HR with ⟨%t, Ht, #HPt⟩
  (try wp_auto)
  wp_apply (sync.RWMutex.wp_RUnlock _ (credTokR rc P)) $$ [$Hlk Ht] as Hslot
  · inext
    iunfold credTokR
    iexists t
    iframe Ht HPt
  imod threadPool.giveBackL credTokN 0 γp _ ⊤ (by simp) $$ [$Hpool $Hloan $Hslot] with Htok
  wp_if_destruct
  · iapply HΦ
    iframe Htok
    isplitr
    · ipureintro; rfl
    iexists none
    unfold credsMapIs tokMdOk
    isplitr
    · ileft; ipureintro; exact ⟨rfl, rfl⟩
    isplitr
    · ipureintro; intro _ _; rfl
    ileft; ipureintro; rfl
  · wp_apply (wp_map_make1 (K := GoString) (V := GoString) go.string go.string) as %mp Hm
    (try wp_auto)
    iapply wp_fupd
    wp_apply (wp_mapInsert (K := GoString) (V := GoString) go.string mp ∅ go!"token" t) $$ Hm as Hm
    (try wp_auto)
    imod ownMap_persist mp _ _ $$ Hm with #Hm
    imodintro
    iapply HΦ
    iframe Htok
    isplitr
    · ipureintro; rfl
    iexists (some fun k => ((<[go!"token" := t]> (∅ : GMap GoString GoString)) !! k).map fun v => [v])
    unfold credsMapIs tokMdOk
    isplitl
    · iright
      iexists _
      iframe Hm
      ipureintro
      refine ⟨rfl, ?_⟩
      intro k v hk
      by_cases hkt : k = go!"token"
      · subst hkt; unfold metadata.lowerKey; decide
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hkt)] at hk; simp at hk
    isplitr
    · ipureintro
      intro k hk
      simp only [mdGet, Option.bind_some]
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hk)]
      rfl
    iright
    iexists t
    isplitr
    · ipureintro
      simp only [mdGet, Option.bind_some, GMap.lookup_insert, Option.map_some]
    icases HPt with (%Ht0 | #HPt)
    · exfalso; simp_all
    · iexact HPt

end proof

end EtcdGrove
end Perennial
