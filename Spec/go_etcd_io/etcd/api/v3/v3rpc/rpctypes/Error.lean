/-
`rpctypes.Error(err)` (`api/v3rpc/rpctypes/error.go`), called by
`clientv3.WatchResponse.Err`. Not translated: its body uses grpc's `status` (`FromError`), which
is not translated, so it is an axiom (`Proof/.../rpctypes/Error.lean`). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `rpctypes.Error(err)` for a non-nil `err` returns a non-nil error (`err` itself, or the
`EtcdError` that its gRPC description maps to), whose `Error()` returns some string if `err`'s
does (`errStrOk`: the result is `err`, or an `EtcdError`, whose `Error` returns its
description). Only what `WatchResponse.Err` needs: nothing about which error, nor about a nil
`err` (for which it returns `nil`). It assumes that `err`'s methods (`Error()`, `GRPCStatus()`,
which `ErrorDesc` and `status.FromError` call) return. -/
abbrev rpctypes.Error.spec : Prop :=
  ∀ (err : GoError),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes ∗
      ⌜err ≠ interface.nil⌝ }}
    (App (Val (@! go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Error)) (Val #err))
  {{ (err' : GoError), RET #err'; ⌜err' ≠ interface.nil⌝ ∗ □ (errStrOk err -∗ errStrOk err') }}

end spec

end EtcdGrove
end Perennial
