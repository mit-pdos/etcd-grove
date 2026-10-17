/-
`clientv3.NewKVFromKVClient(remote, c)` (`client/v3/kv.go`, translated for PR etcd-io/etcd#21809:
how `v3client.New` builds the `KV` of a `NewCtxClient` client). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvCtxClient

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `NewKVFromKVClient(remote, c)` on a non-nil client whose call options are `sl`: a new `*kv`
over `remote` whose every call passes `sl` (`kv.Do`'s `kv.callOpts...`), as a `KV`. Over a
`NewCtxClient` client, `sl` is `defaultCallOpts` (`NewCtxClient.spec`). -/
abbrev NewKVFromKVClient.spec : Prop :=
  ∀ (remote : GoInterface) (cl : Loc) (sl : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ ⌜cl ≠ null⌝ ∗
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"callOpts" cl ↦□ sl }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.NewKVFromKVClient)) (Val #remote)) (Val #cl))
  {{ (v : GoInterface), RET #v; ∃ api : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty) #api⌝ ∗
      structFieldRef go_etcd_io.etcd.client.v3.kv go!"remote" api ↦□ remote ∗
      structFieldRef go_etcd_io.etcd.client.v3.kv go!"callOpts" api ↦□ sl }}

end spec

end EtcdGrove
end Perennial
