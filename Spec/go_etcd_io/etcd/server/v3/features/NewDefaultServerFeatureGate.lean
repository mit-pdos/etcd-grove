/-
`features.NewDefaultServerFeatureGate(name, lg)` (`server/features/etcd_features.go`): the trust
boundary (`server/v3/features` and `pkg/v3/featuregate` are names-only). Lean-first (no Rocq
counterpart); the adequacy example's (item 9, point 7) configuration.

In Go: `featuregate.New(name + "ServerFeatureGate", lg)` (a fresh `*featureGate`, its known
features featuregate's defaults, none enabled explicitly), then `Add(DefaultEtcdServerFeatureGates)`
(no error: the gate is fresh and the server's features are not featuregate's own; otherwise it
panics), returned as a `FeatureGate`. Its `Enabled(f)` of a registered feature reads two atomic
maps and returns a boolean (`isFeatureGate`, `features/Defs.lean`); the gate is not shared with
anything else, and nothing in the program sets a feature, so the contract holds forever. For the
same reason a feature answers its default for good: `CompactHashCheck`'s is `false`
(`DefaultEtcdServerFeatureGates`, `{Default: false, PreRelease: Alpha}`; `featureIs`, audit B4a,
2026-10-18, for `EtcdServer.monitorCompactHash`).

The postcondition (D19a's rule for a closed theorem's hypotheses and the trust boundary) holds
only fresh resources: a non-nil pointer and a persistent contract about its methods.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Proof.go_etcd_io.etcd.server.v3.features.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`features.NewDefaultServerFeatureGate(name, lg)`** returns a non-nil `*featureGate` (as a
`featuregate.FeatureGate`) meeting the feature gate's contract on the server's features, with
`CompactHashCheck` off. -/
abbrev features.NewDefaultServerFeatureGate.spec : Prop :=
  ∀ (name : GoString) (lg : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.features }}
    (App (App (Val (@! features.NewDefaultServerFeatureGate)) (Val #name)) (Val #lg))
  {{ (p : Loc), RET #(interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.featuregate.featureGate.ty) #p);
      ⌜p ≠ null⌝ ∗ isFeatureGate (interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.featuregate.featureGate.ty) #p) ∗
      -- (audit B4a, 2026-10-18) `CompactHashCheck` at its default, off
      featureIs (interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.featuregate.featureGate.ty) #p)
        go!"CompactHashCheck" false }}

end spec

end EtcdGrove
end Perennial
