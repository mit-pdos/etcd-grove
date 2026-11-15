/-
`(*store).HashStorage()` (`kvstore.go:548`).

**Users**: `KV.HashStorage` on the server's store (promoted): the corruption checker
(`server.go:367`), the maintenance server (`v3rpc/maintenance.go:101`). Snippet `ReqHash`.

**Proof sketch**: the read-only field `s.hashes` (`NewStore`'s `NewHashStorage`; `isHashStorage`
from the handle).

**Changes** from `specs-ref`'s `store__HashStorage.lean`: `isHashStorage` (the hash storage's
contracts) in place of `hashStoreOk` (only `Store`).

**Margin**: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `KV.HashStorage`'s contract at `*store`. -/
def store.HashStorage.spec : Prop :=
  ∀ s : Loc, KV.HashStorage.contract (GF := GF) (go.GoType.PointerType store.ty) #s

end spec
end Mvcc
end EtcdGrove
end Perennial
