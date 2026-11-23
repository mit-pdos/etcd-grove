/-
`klog.Warningf(format, args...)` (proved over its translated body since klog-printf, 2026-11-23,
etcd-grove#25, as `klog.Errorf`; until then names-only; k8s 7f-5a, T5-f: the etcd3 watcher's
`logWatchChannelErr`, compaction branch, `watcher.go:428-437`): logging, a no-op for the program's
results, in the restricted form of `klog.Errorf.spec` (`notes/klog-args-fix.md`; the same
`printfDepth` path; Go refuted "any arguments"): the arguments' slice, at any fraction, and
`klog.argsOk f xs`, both given back. The watcher's call (`"watch chan error: %v"`, one error whose
`Error()` returns) discharges it with `klog_args_intro`, `klog.argOkAt_of_argOk` from `fmt.argOk err`.
Lean-first.

Assumed configuration: klog's default flags (`-logtostderr`, output to stderr), no
`klog.SetLogger`/`SetOutput`. Otherwise klog can end the process (an unwritable
`-log_file`/`-log_dir`, a full disk: `os.Exit(2)`; a broken stderr pipe: `SIGPIPE`) or run the
installed logger's code; an exit does not break a safety result, a foreign logger would.
-/
module

public import Spec.k8s_io.klog.v2.Errorf

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
abbrev klog.Warningf.spec : Prop :=
  ∀ (f : GoString) (args : GoSlice) (xs : List GoInterface) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.klog.v2 ∗ args ↦*{dq} xs ∗ klog.argsOk f xs }}
    (App (App (Val (@! k8s_io.klog.v2.Warningf)) (Val #f)) (Val #args))
  {{ RET #(); args ↦*{dq} xs ∗ klog.argsOk f xs }}

end spec

end EtcdGrove
end Perennial
