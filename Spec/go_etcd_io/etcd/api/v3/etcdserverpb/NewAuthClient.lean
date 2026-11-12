/-
`etcdserverpb.NewAuthClient(cc)` (`api/etcdserverpb/rpc_grpc.pb.go`, the generated Auth stub;
translated for the auth plan's E2h). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvAuthConn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `NewAuthClient(cc)`: a new `*authClient` whose `cc` is `cc` (read-only), as an `AuthClient`. -/
abbrev NewAuthClient.spec : Prop :=
  ∀ (cc : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb }}
    (App (Val (@! etcdserverpb.NewAuthClient)) (Val #cc))
  {{ (v : GoInterface), RET #v; ∃ ac : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType etcdserverpb.authClient.ty) #ac⌝ ∗
      structFieldRef etcdserverpb.authClient go!"cc" ac ↦□ cc }}

end spec

end EtcdGrove
end Perennial
