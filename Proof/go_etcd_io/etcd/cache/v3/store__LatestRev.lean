/-
Proof of `Spec/store__LatestRev.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.store__LatestRev

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem store.LatestRev.wp_proof : store.LatestRev.spec (GF := GF) (hG := hG) := by
  intro s γ cap E R r0
  wp_start as ⟨#Hs, Hrd, #Hlb⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold storeReader
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hrl, HP⟩
  unfold storeLockInv
  iNamed HP
  ihave #Hlb' := monoNatLbOwn_get $$ Hrev
  unfold storeRevLb
  ihave %Hle := monoNatLbOwn_valid $$ Hrev Hlb
  wp_auto
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hst Hrev HlatestRev Hhist Hrest]
  · inext; iexists st; simp only [named]; iframe; iframe #; ipureintro; exact Hinv
  iintro Hrd
  wp_auto
  iapply HΦ
  iframe
  iexists st
  unfold storeSeen storeRevLb
  iframe Hlb'
  iframe HR
  ipureintro
  have := Hinv.rev_nonneg
  refine ⟨⟨Hinv, ?_⟩, rfl⟩
  have h2 := Hle.2
  word

end proof

end EtcdGrove
end Perennial
