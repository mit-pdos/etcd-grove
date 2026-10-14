/-
`traceutil.Get` (`trace.go`: the context's trace if it is a non-nil `*Trace`, else `TODO()`). Lean-first (no Rocq counterpart); unit P1b (2026-10-14): the trace owned (`ownTrace`,
`notes/decisions.md`, "Traces on the request path").
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.traceutil.Defs
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.TxnRange
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.traceutil.Assumptions]

/-- `traceutil.Get(ctx)`, `ctx` carrying the trace `o` (`ctxTraceIs`): that trace (whose owner
holds it), or a fresh empty one, owned (`TODO()`), if `ctx` carries none. -/
abbrev traceutil.Get.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (o : Option Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗ traceutil.ctxTraceIs ctx o }}
    (App (Val (@! traceutil.Get)) (Val #(GoInterface.ok ctx)))
  {{ (t : Loc), RET #t; ⌜t ≠ null⌝ ∗
      match o with
      | some t' => ⌜t = t'⌝
      | none => traceutil.ownTrace t true }}

end spec

end EtcdGrove
end Perennial
