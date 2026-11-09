/-
## `(*Trace).SetStartTime`

**Users.** `raftRequest`, `Compact` (`v3_server.go:402,1026`). Snippet: `trace.go` (`ReqApplyTraceHandoff`).

**Proof sketch.** A store. **Changes.** From `specs-ref`'s `Trace__SetStartTime.lean` (the emptiness index
dropped). **Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace TraceUtil

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.traceutil.Assumptions]

/-- Sets the start time; the trace kept. -/
def Trace.SetStartTime.spec : Prop :=
  ∀ (t : Loc) (st : _root_.Perennial.time.Time),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗ traceOwn t }}
    (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.traceutil.Trace.ty @!! go!"SetStartTime")) (Val #st))
  {{ RET #(); traceOwn t }}

end spec
end TraceUtil
end EtcdGrove
end Perennial
