/-
`(*prometheus.GaugeVec).With(labels)`: names-only (the server's `start` sets the cluster version gauge). Lean-first (the request path's unit 4c).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base

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

/-- `gv.With(labels)` returns the vector's gauge for the labels, whose `Set` returns (names-only;
the server's `start`: `ClusterVersionMetrics.With(…).Set(1)`). -/
abbrev prometheus.GaugeVec.With.spec : Prop :=
  ∀ (gv : Loc) (labels : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus }}
    (App (Val (gv @!! go.GoType.PointerType github_com.prometheus.client_golang.prometheus.GaugeVec.ty @!! go!"With"))
      (Val #labels))
  {{ (g : GoInterface), RET #g; ∃ gi : GoInterfaceOk, ⌜g = GoInterface.ok gi⌝ ∗
      □ (∀ x : w64, {{ True }} (App (Val #(methods gi.ty go!"Set" gi.v)) (Val #x)) {{ RET #(); True }}) }}

end spec

end EtcdGrove
end Perennial
