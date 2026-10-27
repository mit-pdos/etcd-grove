/-
`etcdserverpb.NewWatchClient(cc)` (`api/etcdserverpb/rpc_grpc.pb.go`, the generated Watch stub's
constructor; the watch slice's unit W-W). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvKVConn

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

/-- `NewWatchClient(cc)`: a new `*watchClient` whose `cc` is `cc` (read-only), as a
`WatchClient`. -/
abbrev NewWatchClient.spec : Prop :=
  ∀ (cc : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb }}
    (App (Val (@! etcdserverpb.NewWatchClient)) (Val #cc))
  {{ (v : GoInterface), RET #v; ∃ wc : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType etcdserverpb.watchClient.ty) #wc⌝ ∗
      structFieldRef etcdserverpb.watchClient go!"cc" wc ↦□ cc }}

end spec

end EtcdGrove
end Perennial
