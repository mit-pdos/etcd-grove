module

public import Spec.google_golang_org.grpc.health.Server__setServingStatusLocked

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
variable [package_sem : google_golang_org.grpc.health.Assumptions]

theorem health.Server.setServingStatusLocked.wp_proof :
    health.Server.setServingStatusLocked.spec (GF := GF) (hG := hG) := by
  intro hs mS mU S service status
  wp_start as ⟨#HfS, #HfU, #HU, HS⟩
  wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := w32) go.string) $$ HS as HS
  wp_apply (wp_map_lookup1 (K := GoString) (V := GoMap) go.string _ mU ∅ service DFrac.discard) $$ HU as -
  -- no watcher: the range is over the nil map
  rw [show (zero_val GoMap : GoMap) = map.nil from rfl]
  wp_call
  iapply HΦ
  iexact HS

end proof

end EtcdGrove
end Perennial
