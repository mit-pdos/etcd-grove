/-
`(*time.Duration).Seconds`: the trust boundary, as `Duration.Seconds` (`Duration__Seconds.lean`).
Goose calls a value method on an addressable variable through the pointer's method set
(`totalDur.Seconds()` in `watch.go`'s `sendLoop`); Perennial translates `time` without
`Duration.Seconds`, so its pointer wrapper is not translated either. Lean-first (no Rocq
counterpart; the watch slice's unit W-S).
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

/-- `(&d).Seconds()` of a duration variable `l ↦{dq} d`, at any fraction: some `float64` (as
`Duration.Seconds`); it returns, the variable unchanged. (Since etcd#22095's verification,
2026-10-17, at any fraction: the auto-periodic compactor reads a read-only package variable.) -/
abbrev time.Duration.Seconds_ptr.spec : Prop :=
  ∀ (l : Loc) (d : _root_.Perennial.time.Duration) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.time ∗ l ↦{dq} d }}
    (App (Val (l @!! go.GoType.PointerType _root_.Perennial.time.Duration.ty @!! go!"Seconds"))
      (Val #()))
  {{ (f : w64), RET #f; l ↦{dq} d }}

end spec

end EtcdGrove
end Perennial
