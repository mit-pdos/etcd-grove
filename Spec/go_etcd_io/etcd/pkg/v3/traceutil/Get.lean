/-
`traceutil.Get`: the trust boundary (`pkg/v3/traceutil` is names-only). Lean-first.

`Get(ctx)` returns the trace `ctx` carries (`ctx.Value(TraceKey{})`) if it is a non-nil
`*Trace`, else `TODO()` (a new empty trace): a trace, not nil.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
public import GeneratedProof.go_etcd_io.etcd.pkg.v3.traceutil
public import Perennial.Proof.context

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- `traceutil.Get(ctx)` returns a trace, not nil. -/
abbrev traceutil.Get.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗
      context.isContext ctx cd }}
    (App (Val (@! traceutil.Get)) (Val #(GoInterface.ok ctx)))
  {{ (t : Loc), RET #t; ⌜t ≠ null⌝ }}

end spec

end EtcdGrove
end Perennial
