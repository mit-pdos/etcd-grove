/-
`closeNotifier.Close` (`http.go`; rafthttp stage 5e-2). Lean-first; the notifier: `rafthttp/CloseNotifier.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.CloseNotifier

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`n.Close()`** with the right to close it and `P`: closes `done`, handing `P` over. -/
abbrev rafthttp.closeNotifier.Close.spec : Prop :=
  ∀ (n : Loc) (γ : GName) (P : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      cnClose n γ P ∗ P }}
    (App (Val (n @!! go.GoType.PointerType rafthttp.closeNotifier.ty @!! go!"Close")) (Val #()))
  {{ RET #GoInterface.nil; True }}

end spec

end EtcdGrove
end Perennial
