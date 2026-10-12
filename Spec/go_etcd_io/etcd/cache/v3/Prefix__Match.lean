/-
`Prefix.Match(key)` (`cache/predicate.go`). Lean-first (no Rocq counterpart); see `InvCache.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvCache

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `prefix.Match(key)` (the exported `Prefix` type; the cache itself does not call it): whether
`key` starts with `prefix` (always for the empty prefix). -/
abbrev Prefix.Match.spec : Prop :=
  ∀ (pfx : GoString) (sl : GoSlice) (key : GoString) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ sl ↦*{dq} key }}
    (App (Val (pfx @!! Prefix.ty @!! go!"Match")) (Val #sl))
  {{ RET #(decide (pfx <+: key)); sl ↦*{dq} key }}

end spec

end EtcdGrove
end Perennial
