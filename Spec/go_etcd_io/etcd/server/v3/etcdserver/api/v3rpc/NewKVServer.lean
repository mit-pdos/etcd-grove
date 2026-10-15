/-
`v3rpc.NewKVServer` (`key.go`). Lean-first (no Rocq counterpart); the vocabulary is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvKV.lean` and `Defs.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvKV

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`NewKVServer(s)`**: a `KVServer` holding a `*kvServer` over the server `s` (its header,
`s` as its `RaftKV`, `s.Cfg.MaxTxnOps` as its budget). -/
abbrev v3rpc.NewKVServer.spec : Prop :=
  ∀ (s : Loc) (A : v3rpc.KVAns GF) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ v3rpc.raftKV s A ∗
      structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"MaxTxnOps"
        (structFieldRef EtcdServer go!"Cfg" s) ↦□ n }}
    (App (Val (@! v3rpc.NewKVServer)) (Val #s))
  {{ (kv : GoInterface), RET #kv; ∃ (p : Loc) (cid mid : w64),
      ⌜kv = interface.mkOk (go.GoType.PointerType v3rpc.kvServer.ty) #p⌝ ∗
      v3rpc.kvServerIs p s A cid mid n }}

end spec

end EtcdGrove
end Perennial
