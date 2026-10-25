/-
`validateChannelKey(key)` (`client/v3/channel_key.go:73`, PR #21765): rejects the reserved channel
keys `""` and `"default"` with a wrapped `ErrReservedChannelKey`, and returns `nil` for any other
key. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `validateChannelKey(key)` returns a non-nil error (whose `Error()` returns some string) if
`key` is `""` or `"default"`, and `nil` otherwise. -/
abbrev validateChannelKey.spec : Prop :=
  ∀ (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (@! go_etcd_io.etcd.client.v3.validateChannelKey)) (Val #key))
  {{ (err : GoInterface), RET #err;
      if key = go!"" ∨ key = go!"default" then
        ∃ e : GoInterfaceOk, ⌜err = GoInterface.ok e⌝ ∗ go_etcd_io.etcd.cache.v3.errorStringSpec e
      else
        ⌜err = GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
