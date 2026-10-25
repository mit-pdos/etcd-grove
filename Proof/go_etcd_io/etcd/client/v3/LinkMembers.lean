/-
**The members' lemmas of the `*kv`'s calls, linked** (D43, 2026-10-25): `kv.Do.wp_members`,
`kv.Put.wp_members`, ... (`KVMembers.lean`'s statements, proved in the functions' `Proof` files)
instantiated with their callees' results (`Link.lean`'s), as `etc/gen-link.py` does for the
functions' specs. What the results about the server's own model use (`ServerKV*.lean`,
`Results.lean`'s `client_*_any`): a member's reply, with what it says of its server. Lean-first
(no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI go_etcd_io.etcd.client.v3 go_etcd_io.etcd.api.v3

section links_members
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem v3.kv.wp_DoM :
    EtcdGrove.kv.Do.specM (GF := GF) (hG := hG) :=
  EtcdGrove.kv.Do.wp_members v3.Op.wp_IsSortOptionValid v3.Op.wp_toRangeRequest
    v3.retryKVClient.wp_Range v3.retryKVClient.wp_Put v3.retryKVClient.wp_DeleteRange
    v3.wp_ContextError

theorem v3.kv.wp_DeleteM :
    EtcdGrove.kv.Delete.specM (GF := GF) (hG := hG) :=
  EtcdGrove.kv.Delete.wp_members v3.wp_OpDelete v3.kv.wp_DoM v3.wp_ContextError

theorem v3.kv.wp_GetM :
    EtcdGrove.kv.Get.specM (GF := GF) (hG := hG) :=
  EtcdGrove.kv.Get.wp_members v3.wp_NewOp v3.kv.wp_DoM v3.wp_ContextError

theorem v3.kv.wp_PutM :
    EtcdGrove.kv.Put.specM (GF := GF) (hG := hG) :=
  EtcdGrove.kv.Put.wp_members v3.wp_OpPut v3.kv.wp_DoM v3.wp_ContextError

theorem v3.txn.wp_CommitM :
    EtcdGrove.txn.Commit.specM (GF := GF) (hG := hG) :=
  EtcdGrove.txn.Commit.wp_members v3.retryKVClient.wp_Txn v3.wp_ContextError

end links_members

end client
end EtcdGrove
end Perennial
