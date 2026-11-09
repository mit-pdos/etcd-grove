/-
## `(*Trace).GetStartTime`

**Users.** `raftRequest`, `Compact` (`v3_server.go:401,1023`), on the apply result's trace. Snippet: `trace.go` (`ReqApplyTraceHandoff`).

**Proof sketch.** A load. **Changes.** From `specs-ref`'s `Trace__GetStartTime.lean` (the emptiness index
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

/-- Its start time; the trace kept. -/
def Trace.GetStartTime.spec : Prop :=
  ∀ (t : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗ traceOwn t }}
    (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.traceutil.Trace.ty @!! go!"GetStartTime")) (Val #()))
  {{ (st : _root_.Perennial.time.Time), RET #st; traceOwn t }}

end spec
end TraceUtil
end EtcdGrove
end Perennial
