/-
`(*traceutil.Trace).Step`: the trust boundary (`pkg/v3/traceutil` is names-only). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
public import GeneratedProof.go_etcd_io.etcd.pkg.v3.traceutil

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `t.Step(msg, fields...)` returns (any `t`, `nil` included: tracing has no effect here). -/
abbrev traceutil.Trace.Step.spec : Prop :=
  ∀ (t : Loc) (msg : GoString) (fields : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil }}
    (App (App (Val (t @!! go.GoType.PointerType traceutil.Trace.ty @!! go!"Step")) (Val #msg))
      (Val #fields))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
