/-
`api.IsCapabilityEnabled` (`etcdserver/api/capability.go`; the server's interceptors ask for the v3
RPC capability; unit P3b's trust boundary until prove-ps2-cap, 2026-11-23: translated with its
body and proved). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `api.IsCapabilityEnabled(c)` returns whether the capability `c` is enabled (some boolean: it
read-locks the package's `enableMapMu`, with a reader slot of the package's pool (`capInit`)
borrowed with the caller's level-0 thread token, which comes back, and reads `enabledMap[c]`, or
`false` if the map is `nil`), under the thread bound the pool needs (`2 ^ 30`, the lock's reader
counter). -/
abbrev api.IsCapabilityEnabled.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 30)] (c : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api ∗ levelTok 0 }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.IsCapabilityEnabled)) (Val #c))
  {{ (b : Bool), RET #b; levelTok 0 }}

end spec

end EtcdGrove
end Perennial
