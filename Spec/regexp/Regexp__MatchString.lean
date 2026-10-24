/-
`regexp.Regexp.MatchString`: the trust boundary (`regexp` is names-only; the pure model
`apply.regexpMatch` is in `apply/RestModel.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.RestModel

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

/-- `re.MatchString(s)` for a compiled `*regexp.Regexp` `re` (`EtcdGrove.regexp.isRegex re pat`)
returns `apply.regexpMatch pat s`. -/
abbrev regexp.Regexp.MatchString.spec : Prop :=
  ∀ (re : Loc) (pat s : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.regexp ∗
      ⌜re ≠ null ∧ EtcdGrove.regexp.isRegex re pat⌝ }}
    (App (Val (re @!! go.GoType.PointerType _root_.Perennial.regexp.Regexp.ty @!! go!"MatchString"))
      (Val #s))
  {{ RET #(apply.regexpMatch pat s); True }}

end spec

end EtcdGrove
end Perennial
