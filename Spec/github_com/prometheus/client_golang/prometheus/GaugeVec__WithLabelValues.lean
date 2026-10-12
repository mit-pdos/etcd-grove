/-
`prometheus.GaugeVec.WithLabelValues`: the trust boundary (`prometheus` is names-only). Lean-first (no Rocq counterpart).
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `gv.WithLabelValues(lvs...)` returns the vector's gauge for the labels (one per label: the
apply package's `alarms` has two, and passes two), whose `Inc`/`Dec`/`Add` return
(`gaugeSpec`, mvcc's). -/
abbrev prometheus.GaugeVec.WithLabelValues.spec : Prop :=
  ∀ (gv : Loc) (lvs : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus }}
    (App (Val (gv @!! go.GoType.PointerType github_com.prometheus.client_golang.prometheus.GaugeVec.ty @!! go!"WithLabelValues"))
      (Val #lvs))
  {{ (g : GoInterface), RET #g; ∃ gi : GoInterfaceOk, ⌜g = GoInterface.ok gi⌝ ∗
      go_etcd_io.etcd.server.v3.storage.mvcc.gaugeSpec gi }}

end spec

end EtcdGrove
end Perennial
