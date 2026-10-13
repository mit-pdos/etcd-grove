/-
`backend.VerifyBackendConsistency(b, lg, skip, buckets...)` (`storage/backend/verify.go`):
verification code (it checks, under `ETCD_VERIFY`, that the backend's read and batch
transactions agree, and panics otherwise). Lean-first (no Rocq counterpart); the request path's
unit 4b (2026-10-13).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Base
public import GeneratedProof.go_etcd_io.etcd.server.v3.storage.backend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `backend.VerifyBackendConsistency(b, lg, skip, buckets)` returns (the trust boundary: names-only,
verification code, as `verify.Verify`). -/
abbrev backend.VerifyBackendConsistency.spec : Prop :=
  ∀ (b : GoInterface) (lg : Loc) (skip : Bool) (bs : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.backend.VerifyBackendConsistency))
      (Val #b)) (Val #lg)) (Val #skip)) (Val #bs))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
