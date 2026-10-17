/-
Unfinished (PR etcd#22338; the spec is pr-verify/etcd-22560's postulate, which this branch, where
`run` is translated with bodies, leaves as a `sorry`): `simpleTokenTTLKeeper.run`. Every tick it
locks `tm.mu` (= `&t.simpleTokensMu`: `keeperRO`), sweeps its own deadline map (in the lock:
`keeperMap`, found through the membership `k ↪[γk]□ ()`) calling `deleteTokenFunc` (`delfOk`:
keeps the table below the allowed table), sets the gauge (the PR's line: `authInit`'s gauge,
whose `Set` returns) and unlocks; on `stopc` it closes `donec` (its two channels:
`keeperChans`) and returns. What is missing: the ticker's channel in the `select`, and the map
range that deletes while it iterates (`wp_map_for_range_mut_keys`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.simpleTokenTTLKeeper__run

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.simpleTokenTTLKeeper.run.wp_proof :
    auth.simpleTokenTTLKeeper.run.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end EtcdGrove
end Perennial
