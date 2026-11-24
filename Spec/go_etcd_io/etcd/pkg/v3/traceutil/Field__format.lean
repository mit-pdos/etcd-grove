/-
`(*traceutil.Field).format` (`trace.go`: `fmt.Sprintf("%s:%v; ", f.Key, f.Value)`). Lean-first (no
Rocq counterpart); traceutil-log (2026-11-23), a callee of `writeFields`.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.traceutil.Defs
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI _root_.Perennial.go_etcd_io.etcd.pkg.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.traceutil.Assumptions]

/-- `f.format()` of a field whose value is formattable (`fieldsWf`: `nil` or of a predeclared basic
type) returns some string. -/
abbrev traceutil.Field.format.spec : Prop :=
  ∀ (l : Loc) (f : traceutil.Field),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗ l ↦ f ∗
      ⌜traceutil.fieldsWf [f]⌝ }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.traceutil.Field.ty @!! go!"format")) (Val #()))
  {{ (s : GoString), RET #s; l ↦ f }}

end spec

end EtcdGrove
end Perennial
