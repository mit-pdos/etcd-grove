/-
`strconv.FormatBool`: the trust boundary (Perennial translates `strconv` names-only). Lean-first (no Rocq counterpart); the request path
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

/-- `strconv.FormatBool(b)`: a string (`"true"` or `"false"`; the metrics' label, which the
model does not read); it returns. -/
abbrev strconv.FormatBool.spec : Prop :=
  ∀ (b : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.strconv }}
    (App (Val (@! _root_.Perennial.strconv.FormatBool)) (Val #b))
  {{ (str : GoString), RET #str; True }}

end spec

end EtcdGrove
end Perennial
