/-
`newNotifier()`. Lean-first (no Rocq counterpart); see `InvNotifier.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvNotifier

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `newNotifier()`: a `notifier` with count `0`, and the `RWMutex`'s tokens
(`notifierHandle`). -/
abbrev newNotifier.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 }}
    (App (Val (@! newNotifier)) (Val #()))
  {{ (n : Loc) (γ : NotifierNames), RET #n;
      notifierLb γ 0 ∗
      [∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
        notifierHandle n γ }}

end spec

end EtcdGrove
end Perennial
