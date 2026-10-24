/-
`protowire.ParseError`: the trust boundary
(`google.golang.org/protobuf/encoding/protowire` is names-only). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI google_golang_org.protobuf.encoding

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `protowire.ParseError(n)` for `n < 0` returns a non-nil `error`. -/
abbrev protowire.ParseError.spec : Prop :=
  ∀ (n : w64),
  sint.Z n < 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.encoding.protowire }}
    (App (Val (@! protowire.ParseError)) (Val #n))
  {{ (err : GoInterface), RET #err; ⌜err ≠ GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
