/-
## `bucket.Name()`

**Users.** The backend (4a: a `backend.Bucket`'s `ID`, `Name`, `IsSafeRangeBucket`; `String` in its
logs), the package's `init` (`IsSafeRangeBucket`, `Name`). **Proof sketch.** A field read (`String`:
`string(b.Name())`, a copy of the read-only name). **Changes.** From `specs-ref`'s
`bucket__Name.lean`: over `bucketIs`. **Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Schema

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- The bucket's name slice (read-only for good: `bucketIs`). -/
def bucket.Name.spec : Prop :=
  ∀ (b : Bkt) (v : go_etcd_io.etcd.server.v3.storage.schema.bucket),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ bucketIs b v }}
    (App (Val (v @!! go_etcd_io.etcd.server.v3.storage.schema.bucket.ty @!! go!"Name")) (Val #()))
  {{ RET #v.name'; True }}

end spec
end Schema
end EtcdGrove
end Perennial
