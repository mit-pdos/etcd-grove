/-
**`fmt.Errorf(format, labels)` with `labels` a `map[string]string` formatted by `%+v`**: **a local
trust-boundary hypothesis, pending approval** (the DaemonSet autoverify run, track C, 2026-11-04;
review 1 (API), M3). `getDaemonSetsForPod` calls `utilruntime.HandleError(fmt.Errorf("user error!
more than one daemon is selecting pods with labels: %+v", pod.Labels))` (`daemon_controller.go:451`)
when two DaemonSets select a pod's labels; reachable (its callers `addPod`/`updatePod` have no
`sceneOk` that would exclude overlapping selectors).

`fmt.Errorf.spec` takes arguments of predeclared basic types or with an `Error()`/`String()` spec
(`fmt.argOk`). A `map[string]string` is neither: under `%+v` Go calls no method (the keys and
values are strings) and prints the map's entries, in key order, reading the map. So the
hypothesis: with the map read-only for good (the cached pod's labels), `Errorf` returns an error with
an `Error()` spec; the arguments come back. The general change (a `fmt` model of `%v`/`%+v` of a map
of basic types) is recorded in `notes/perennial-changes.md`, beside "`%#v` of a struct pointer in
`fmt.Errorf`" (track B's `ErrorfDaemonSetV.lean`, the same class).

Who rests on it: `getDaemonSetsForPod` (its two-DaemonSets path), so `addPod`, `updatePod`.
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

/-- **`fmt.Errorf(format, labels)`, `labels` a read-only `map[string]string`**: see the file
header. -/
abbrev ErrorfLabelsMap.spec : Prop :=
  ∀ (format : GoString) (args_sl : GoSlice) (dq : DFrac) (m : GoMap)
    (M : GMap GoString GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗
      args_sl ↦*{dq} [interface.mkOk (go.GoType.MapType go.string go.string) #m] ∗
      m ↦${DFrac.discard} M }}
    (App (App (Val (@! _root_.Perennial.fmt.Errorf)) (Val #format)) (Val #args_sl))
  {{ (e : GoInterfaceOk), RET #(interface.ok e);
      args_sl ↦*{dq} [interface.mkOk (go.GoType.MapType go.string go.string) #m] ∗
      fmt.stringMethodSpec (hG := hG) e go!"Error" }}

end spec

end dsctl
end EtcdGrove
end Perennial
