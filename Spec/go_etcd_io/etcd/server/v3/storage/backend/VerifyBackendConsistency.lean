/-
`backend.VerifyBackendConsistency(b, lg, skip, buckets...)` (`storage/backend/verify.go`):
verification code (it checks, under `ETCD_VERIFY`, that the backend's read and batch
transactions agree, and panics otherwise). Lean-first (no Rocq counterpart); the request path's
unit 4b (2026-10-13).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Base
public import GeneratedProof.go_etcd_io.etcd.server.v3.storage.backend
public import Proof.go_etcd_io.etcd.client.pkg.v3.verify.Env

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `backend.VerifyBackendConsistency(b, lg, skip, buckets)` returns (the trust boundary: names-only,
verification code, as `verify.Verify`).
(Sweep repairs 1, B4, 2026-11-07: with `ETCD_VERIFY` off, `envVerifyOff`, from program start; until
then assumed unconditionally, false of a run with `ETCD_VERIFY=all`, `lock` or `assert`: Go
`examples/sweeprepairs/b1`, `TestB4On`.) -/
abbrev backend.VerifyBackendConsistency.spec : Prop :=
  ∀ (b : GoInterface) (lg : Loc) (skip : Bool) (bs : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      -- (sweep repairs 1, B4) `ETCD_VERIFY` off for the run (`envVerifyOff`)
      envVerifyOff }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.backend.VerifyBackendConsistency))
      (Val #b)) (Val #lg)) (Val #skip)) (Val #bs))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
