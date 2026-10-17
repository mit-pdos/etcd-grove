/-
The trust boundary (pr-verify etcd#22560, 2026-10-16): `simpleTokenTTLKeeper.run` (names only: a loop over a `time.Ticker`, which Perennial does not model). Every tick it locks `tm.mu` (= `&t.simpleTokensMu`: `keeperRO`), sweeps its own deadline map (in the lock: `keeperMap`, found through the membership `k ↪[γk]□ ()`) calling `deleteTokenFunc` (`delfOk`: keeps the tables below the allowed table), and unlocks; on `stopc` it closes `donec` (its two channels: `keeperChans`) and returns. The postulate: run with these resources it does not panic.
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

axiom auth.simpleTokenTTLKeeper.run.wp_proof : auth.simpleTokenTTLKeeper.run.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
