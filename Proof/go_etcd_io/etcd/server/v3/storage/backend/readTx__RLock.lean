/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/readTx__RLock.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__RLock
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ReadLemmas

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

theorem backend.readTx.RLock.wp_proof : backend.readTx.RLock.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b rt qo
  wp_start as ⟨#Hb, #Hrt, Htok, Hopen⟩
  unfold rdTok
  icases Htok with ⟨%rt', #Hrt', Hmu, Hcr⟩
  icombine Hrt Hrt' gives %Heq
  subst Heq
  wp_auto
  wp_apply +noauto sync.RWMutex.wp_RLock $$ [$Hmu] as ⟨Hrl, HP⟩
  wp_pure
  unfold rtRes
  icases HP with ⟨%rd, %rv, %H, HP⟩
  wp_auto
  iapply HΦ
  iframe
  iexists rd.rtx, rv
  unfold rtHeld
  iexists rt, rd, H
  iframe; iframe #
  ipureintro; rfl

end proof

end EtcdGrove
end Perennial
