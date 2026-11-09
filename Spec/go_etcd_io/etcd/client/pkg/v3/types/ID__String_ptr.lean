/-
`(*types.ID).String` (`client/pkg/v3/types/id.go`: the method set of `*ID` holds `ID`'s value
method; Goose's wrapper loads the `ID` and calls it).

Users: the server's logs and maps keyed by member ids through a pointer receiver (144 calls of
`MethodResolve (PointerType types.ID.ty) "String"` in the translated `etcdserver`, `api/rafthttp`,
`api/membership`: `streamWriter.run`, `streamHandler.ServeHTTP`, `RaftCluster.RemoveMember`,
`checkClusterCompatibilityFromHeader`, `streamReader.dial`, ...).

Proof sketch: the wrapper loads `*p` (any fraction, kept), then `ID.String.spec`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/pkg/v3/types/ID__String_ptr.lean`.
verify-round: restored (A2-completeness F4: it had no counterpart here, and the server's sketches
cited the value form at pointer calls); at any fraction, the points-to given back.

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.types.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Types

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.types.Assumptions]

/-- `p.String()` of a `*ID`: `idStr` of the `ID` at `p` (read at any fraction, kept). -/
def ID.String_ptr.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (x : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types ∗ p ↦{dq} x }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.types.ID.ty @!! go!"String"))
      (Val #()))
  {{ (s : GoString), RET #s; p ↦{dq} x ∗ ⌜s = idStr x⌝ }}

end spec

end Types
end EtcdGrove
end Perennial
