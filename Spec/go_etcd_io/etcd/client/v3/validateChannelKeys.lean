/-
`validateChannelKeys(keys)` (`client/v3/channel_key.go:64`, PR #21765): validates each key in `keys`
with `validateChannelKey`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.validateChannelKey

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

/-- `validateChannelKeys(keys)` returns `nil` when every key in `keys` is neither `""` nor
`"default"`, and a non-nil error (whose `Error()` returns some string) otherwise. -/
abbrev validateChannelKeys.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (keys : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ sl ↦*{dq} keys }}
    (App (Val (@! go_etcd_io.etcd.client.v3.validateChannelKeys)) (Val #sl))
  {{ (err : GoInterface), RET #err; sl ↦*{dq} keys ∗
      if ∀ k ∈ keys, k ≠ go!"" ∧ k ≠ go!"default" then
        ⌜err = GoInterface.nil⌝
      else
        ∃ e : GoInterfaceOk, ⌜err = GoInterface.ok e⌝ ∗ go_etcd_io.etcd.cache.v3.errorStringSpec e }}

end spec

end EtcdGrove
end Perennial
