/-
`(*Transport).Get(id)` (`transport.go`; rafthttp stage 6b). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.TransportInv

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

/-- **`t.Get(id)`** with a reader's token of the transport's mutex: `nil`, or the started peer of
`id` (`peerOk`); the token back. -/
abbrev rafthttp.Transport.Get.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (t : Loc) (lid : w64) (γd : GName) (R : IProp GF) (γs γr : GName) (pid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      trReadTok Rh t lid γd R γs γr }}
    (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"Get")) (Val #pid))
  {{ (pi : GoInterface), RET #pi; trReadTok Rh t lid γd R γs γr ∗
      (⌜pi = GoInterface.nil⌝ ∨ ∃ p : Loc,
        ⌜pi = interface.mkOk (go.GoType.PointerType rafthttp.peer.ty) #p⌝ ∗
        peerOk Rh lid pid γd R p) }}

end spec

end EtcdGrove
end Perennial
