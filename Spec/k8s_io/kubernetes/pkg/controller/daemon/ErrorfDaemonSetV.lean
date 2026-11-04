/-
**`fmt.Errorf(format, ds, err)` with `ds` a `*DaemonSet` formatted by `%#v`**: **a local
trust-boundary hypothesis, pending approval** (the DaemonSet autoverify run, track B, 2026-11-04;
review 1's M2). `updateDaemonSetStatus` returns `fmt.Errorf("error storing status for daemon set
%#v: %w", ds, err)` (`daemon_controller.go:1263`), reachable when `storeDaemonSetStatus` fails
(`FailWrites`, `FailReads`); `syncNodes` (DC:1045) and `syncDaemonSet` (DC:1340) have the same
pattern, unreachable (`KeyFunc` does not fail on a namespaced object).

`fmt.Errorf.spec` takes arguments of predeclared basic types or with an `Error()`/`String()` spec
(`fmt.argOk`). A `*DaemonSet` is neither: under `%#v` Go calls no method of it (it has no
`GoString`; its gogo `String()` is not called) and prints the struct reflectively, reading every
field through the pointer. So the hypothesis: with the DaemonSet read-only for good (`dsAt`
discarded, as every cached object the controller formats) and `err` formattable, `Errorf`
returns an error with an `Error()` spec; the arguments come back. The general change (a `fmt`
model of `%#v` of a pointer to a struct whose fields are read-only and formattable) is recorded
in `notes/perennial-changes.md`, "`%#v` of a struct pointer in `fmt.Errorf`".

Who rests on it: `updateDaemonSetStatus` (its error path), so `updateDaemonSet`, `syncDaemonSet`,
`processNextWorkItem`.
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.daemon.SyncDefs

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI apimodel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.fmt.Assumptions]

/-- **`fmt.Errorf(format, ds, err)`, `ds` a read-only `*DaemonSet`**: see the file header. -/
abbrev ErrorfDaemonSetV.spec : Prop :=
  ∀ (format : GoString) (args_sl : GoSlice) (dq : DFrac) (ds : Loc) (d : kd.apps.DaemonSet)
    (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗
      args_sl ↦*{dq} [interface.mkOk (go.GoType.PointerType k8s_io.api.apps.v1.DaemonSet.ty) #ds, err] ∗
      □ dsAt ds DFrac.discard d ∗ fmt.argOk (hG := hG) err }}
    (App (App (Val (@! _root_.Perennial.fmt.Errorf)) (Val #format)) (Val #args_sl))
  {{ (e : GoInterfaceOk), RET #(interface.ok e);
      args_sl ↦*{dq} [interface.mkOk (go.GoType.PointerType k8s_io.api.apps.v1.DaemonSet.ty) #ds, err] ∗
      fmt.stringMethodSpec (hG := hG) e go!"Error" }}

end spec

end dsctl
end EtcdGrove
end Perennial
