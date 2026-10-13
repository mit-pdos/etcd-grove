/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/readTx__RUnlock.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__RUnlock

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

theorem backend.readTx.RUnlock.wp_proof : backend.readTx.RUnlock.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b rt rtx rv
  wp_start as ⟨#Hb, #Hrt, Hh⟩
  unfold rtHeld
  icases Hh with ⟨%rt', %rd, %H, #Hrt', Hrl, HP, %Hrtx, Hcr⟩
  icombine Hrt Hrt' gives %Heq
  subst Heq
  wp_auto
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl HP] as Hmu
  · inext; unfold rtRes; iexists rd, rv, H; iexact HP
  iapply HΦ
  unfold rdTok
  iexists rt
  iframe; iframe #


end proof

end EtcdGrove
end Perennial
