/-
`jitterUp(duration, jitter)` (`client/v3/utils.go`, names only): `duration` scaled by a random
factor in `[1-jitter, 1+jitter]` (`math/rand.Float64` and float arithmetic, converted back to a
`time.Duration`). PR etcd#20731 (the round-robin backoff function calls it).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvRetry

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (backoffOk)

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `jitterUp(d, j)` returns some duration: float arithmetic and the float-to-integer conversion
have no semantics in Perennial (a float is an opaque bit pattern), so nothing is said of the
value. -/
abbrev jitterUp.spec : Prop :=
  ∀ (d : w64) (j : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.jitterUp)) (Val #d)) (Val #j))
  {{ (r : w64), RET #r; True }}

end spec

end EtcdGrove
end Perennial
