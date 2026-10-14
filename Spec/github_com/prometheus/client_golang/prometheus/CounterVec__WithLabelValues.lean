/-
`prometheus.CounterVec.WithLabelValues`: the trust boundary (`prometheus` is names-only; unit
P3b: the server's unary interceptor counts the client's requests by API version). Lean-first (no
Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A prometheus `Counter`: `Inc()` returns (persistent). -/
def prometheus.counterSpec (c : GoInterfaceOk) : IProp GF :=
  iprop(□ ({{ True }} (App (Val #(methods c.ty go!"Inc" c.v)) (Val #())) {{ RET #(); True }}))

instance prometheus.counterSpec_persistent (c : GoInterfaceOk) :
    Persistent (prometheus.counterSpec (GF := GF) c) := by
  unfold prometheus.counterSpec; infer_instance

/-- `cv.WithLabelValues(lvs...)` returns the vector's counter for the labels (the interceptor's
`clientRequests` has two and is passed two), whose `Inc` returns (`counterSpec`). -/
abbrev prometheus.CounterVec.WithLabelValues.spec : Prop :=
  ∀ (cv : Loc) (lvs : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus }}
    (App (Val (cv @!! go.GoType.PointerType github_com.prometheus.client_golang.prometheus.CounterVec.ty @!! go!"WithLabelValues"))
      (Val #lvs))
  {{ (c : GoInterface), RET #c; ∃ ci : GoInterfaceOk, ⌜c = GoInterface.ok ci⌝ ∗
      prometheus.counterSpec ci }}

end spec

end EtcdGrove
end Perennial
