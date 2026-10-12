/-
Shared lemmas of the backend applier's component methods (`backend.go`). Lean-first (no Rocq
counterpart).

`go.uint64` is not an interface type: Perennial states `NotInterface` for the type
constructors, and `go.uint64` is a (non-reducible) `go.Named`, so instance search does not see
it. The backend's `Alarm` calls `types.ID(ar.MemberID).String()`, a method of a named type whose
underlying type is `uint64`; resolving it (`go_method_resolve_step`) needs this instance.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace apply

instance notInterface_uint64 [FfiSyntax] : go.NotInterface go.uint64 :=
  ⟨by unfold go.uint64; trivial⟩

end apply
end EtcdGrove
end Perennial
