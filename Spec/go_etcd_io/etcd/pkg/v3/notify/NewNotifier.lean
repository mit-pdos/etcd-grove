/-
`notify.NewNotifier()` (`notify.go`). Lean-first (no Rocq counterpart); the request path's unit 4b (2026-10-13).
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

/-- `notify.NewNotifier()`: a notifier (`isNotifier`, the writer guard of its mutex) and the
mutex's reader slots (`notifyReader`; Perennial's `RWMutex` admits a bounded number of readers). -/
abbrev notify.NewNotifier.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.notify }}
    (App (Val (@! notify.NewNotifier)) (Val #()))
  {{ (n : Loc), RET #n; isNotifier n ∗
      [∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), notifyReader n }}

end spec

end EtcdGrove
end Perennial
