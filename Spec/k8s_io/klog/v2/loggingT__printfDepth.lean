/-
`logging.printfDepth(s, logger, filter, depth, format, args...)` (klog v2.140.0, `klog.go:764-784`),
with no logger, no filter and a severity `InfoLog..FatalLog`: formats the arguments into the buffer
`header` returns (`fmt.Fprintf`), appends a newline if missing, and hands it to `output`; the arguments'
slice and `klog.argsOk format args` come back. What `Errorf`, `Warningf` and `Verbose.Infof` run
(through `printf`). Proved over its translated body (`Proof/k8s_io/klog/v2/loggingT__printfDepth.lean`;
klog-printf, 2026-11-23, etcd-grove#25). Lean-first.

With a logger installed (`klog.SetLogger`) Go runs the logger's code, and an empty message panics
(`issues/klog-printf-empty-with-logger.md`): the premise `logger = nil` excludes both.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import Spec.k8s_io.klog.v2.Args

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev klog.loggingT.printfDepth.spec : Prop :=
  ∀ (s : w32) (logger : Loc) (filter : GoInterface) (depth : w64) (f : GoString) (args : GoSlice)
    (xs : List GoInterface) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.klog.v2 ∗
      ⌜logger = null ∧ filter = interface.nil ∧ (s = W32 0 ∨ s = W32 1 ∨ s = W32 2 ∨ s = W32 3)⌝ ∗
      args ↦*{dq} xs ∗ klog.argsOk f xs }}
    (App (App (App (App (App (App
      (Val (globalAddr k8s_io.klog.v2.logging @!! go.GoType.PointerType k8s_io.klog.v2.loggingT.ty
        @!! go!"printfDepth"))
      (Val #s)) (Val #logger)) (Val #filter)) (Val #depth)) (Val #f)) (Val #args))
  {{ RET #(); args ↦*{dq} xs ∗ klog.argsOk f xs }}

end spec

end EtcdGrove
end Perennial
