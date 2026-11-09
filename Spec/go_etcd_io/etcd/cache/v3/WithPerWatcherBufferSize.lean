/-
`WithPerWatcherBufferSize` (`cache/*.go`).
Users: `New`'s callers (etcd's integration tests: `WithHistoryWindowSize`, `WithProgressNotifyInterval`, ...; snippet `cache/lifecycle.go` `ReqNewOptions`).
Proof sketch: returns the closure `func(c *Config) { c.X = n }`, whose triple is a store to the field.
Changes: unchanged (the closure contract renamed `cfgOptAt`).
Margin: none known.
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Cache

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `WithPerWatcherBufferSize(n)`: an option setting `PerWatcherBufferSize`. -/
def WithPerWatcherBufferSize.spec : Prop :=
  ∀ (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 }}
    (App (Val (@! go_etcd_io.etcd.cache.v3.WithPerWatcherBufferSize)) (Val #n))
  {{ (f : GoFunc), RET #f; cfgOptAt f (fun c => { c with PerWatcherBufferSize' := n }) }}

end spec

end Cache
end EtcdGrove
end Perennial
