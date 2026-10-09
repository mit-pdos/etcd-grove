/-
`WithPerWatcherBufferSize(n)` (`cache/config.go`). Lean-first (no Rocq counterpart); see `InvConfig.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvConfig

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

/-- `WithPerWatcherBufferSize(n)`: an `Option` setting the per-watcher buffer size (`PerWatcherBufferSize`) to `n`. -/
abbrev WithPerWatcherBufferSize.spec : Prop :=
  ∀ (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 }}
    (App (Val (@! WithPerWatcherBufferSize)) (Val #n))
  {{ (f : GoFunc), RET #f; cfgOptSpec f (fun c => { c with PerWatcherBufferSize' := n }) }}

end spec

end EtcdGrove
end Perennial
