/-
`trace.New(name, fields...)` (`k8s.io/utils/trace` `be93311217bd`, `trace/trace.go:154-156`:
`&Trace{name: name, startTime: time.Now(), fields: fields}`). Lean-first; phase 4 of
`notes/k8s-daemonset-plan.md` (the informers' FIFO, whose slow-queue trace calls it). Proved over the
real code since prove-otel4 (2026-11-21), which added the premise `isPkgInit` of the package (its
`time.Now` needs `time`'s, which it gives) and defined `trace.fromNew` (notes/specs-only/ledger.md).
-/
module

public import Proof.k8s_io.utils.trace.Defs
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.utils.trace.Assumptions]

/-- `trace.New(name, fields)`: a trace `Step` and `LogIfLong` take (`trace.fromNew`: not nil). -/
abbrev trace.New.spec : Prop :=
  ∀ (name : GoString) (fields : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.trace }}
    (App (App (Val (@! k8s_io.utils.trace.New)) (Val #name)) (Val #fields))
  {{ (t : Loc), RET #t; ⌜trace.fromNew t⌝ }}

end spec

end EtcdGrove
end Perennial
