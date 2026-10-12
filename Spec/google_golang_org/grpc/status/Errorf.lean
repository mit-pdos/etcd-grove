/-
`status.Errorf`: the trust boundary (grpc is names-only). Lean-first (no Rocq counterpart); the request path
(`notes/decisions.md`, "The request path").
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base

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

/-- `status.Errorf(c, format, a...)` for a code other than `codes.OK` returns a non-nil error
(`checkRangeStreamRequest`'s `Unimplemented`). -/
abbrev status.Errorf.spec : Prop :=
  ∀ (c : w32) (format : GoString) (args : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status ∗
      ⌜(#c : val) ≠ google_golang_org.grpc.codes.OK⌝ }}
    (App (App (App (Val (@! google_golang_org.grpc.status.Errorf)) (Val #c)) (Val #format)) (Val #args))
  {{ (err : GoError), RET #err; ⌜err ≠ interface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
