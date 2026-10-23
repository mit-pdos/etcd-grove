/-
`strings.TrimSuffix`: the trust boundary (Perennial translates `strings` names-only for it and
has no spec; rafthttp stage 5e-3, `streamReader.dial`). Lean-first.
-/
module

public import Perennial.Proof.strings.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `strings.TrimSuffix(s, suffix)` returns some string (`dial` compares it with error messages,
choosing which error to return; any is fine). -/
abbrev strings.TrimSuffix.spec : Prop :=
  ∀ (s suf : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
    (App (App (Val (@! _root_.Perennial.strings.TrimSuffix)) (Val #s)) (Val #suf))
  {{ (r : GoString), RET #r; True }}

end spec

end EtcdGrove
end Perennial
