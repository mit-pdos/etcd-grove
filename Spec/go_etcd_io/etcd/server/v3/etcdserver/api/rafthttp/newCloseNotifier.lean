/-
`newCloseNotifier` (`http.go`; rafthttp stage 5e-2). Lean-first; the notifier: `rafthttp/CloseNotifier.lean`.
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

/-- **`newCloseNotifier()`**, for a resource `P` its `Close` will hand over: the notifier, to wait
on and to close (once), and the token to take `P` with. -/
abbrev rafthttp.newCloseNotifier.spec : Prop :=
  ∀ (P : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp }}
    (App (Val (@! rafthttp.newCloseNotifier)) (Val #()))
  {{ (n : Loc), RET #n; ∃ γ, cnRecv n γ P ∗ cnClose n γ P ∗ cnTok γ }}

end spec

end EtcdGrove
end Perennial
