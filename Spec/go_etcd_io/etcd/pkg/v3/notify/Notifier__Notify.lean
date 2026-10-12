/-
`notify.Notifier.Notify` (`notify.go`: it installs a fresh channel under the write lock and
closes the previous one). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.notify.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `n.Notify()` on a notifier `n` returns (it wakes up the waiters). -/
abbrev notify.Notifier.Notify.spec : Prop :=
  ∀ (n : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.notify ∗ isNotifier n }}
    (App (Val (n @!! go.GoType.PointerType notify.Notifier.ty @!! go!"Notify")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
