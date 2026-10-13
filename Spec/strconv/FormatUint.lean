/-
`strconv.FormatUint`: the trust boundary (Perennial translates `strconv` names-only). Lean-first
(no Rocq counterpart); the request path's unit 4a (the read loop's trace field).
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

/-- `strconv.FormatUint(i, base)`: a string (the digits of `i`; the read loop's trace field, which
the model does not read); it returns. -/
abbrev strconv.FormatUint.spec : Prop :=
  ∀ (i : w64) (base : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.strconv }}
    (App (App (Val (@! _root_.Perennial.strconv.FormatUint)) (Val #i)) (Val #base))
  {{ (str : GoString), RET #str; True }}

end spec

end EtcdGrove
end Perennial
