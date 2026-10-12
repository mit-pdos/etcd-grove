/-
`traceutil.Trace.GetStartTime`: the trust boundary (`pkg/v3/traceutil` is names-only). Lean-first (no Rocq counterpart); the request path
(`notes/decisions.md`, "The request path").
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

/-- `t.GetStartTime()`: some time (on a non-nil trace). -/
abbrev traceutil.Trace.GetStartTime.spec : Prop :=
  ∀ (t : Loc) ,
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗ ⌜t ≠ null⌝ }}
    (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.traceutil.Trace.ty @!! go!"GetStartTime")) (Val #()))
  {{ (st : _root_.Perennial.time.Time), RET #st; True }}

end spec

end EtcdGrove
end Perennial
