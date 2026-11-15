/-
`(*hashStorage).Hash` (`hash.go:135`): the backend's hash after a forced commit (`store.hash`; its unlocked read of `currentRev` races every write: `issues/etcd-mvcc-hash-currentrev-race.md`). **Trusted**: hash.go is translated names-only; the
contract (`Api.lean`'s `HashStorage.Hash.contract`) claims only that it returns (the reader token
back where it takes one).

**Users**: the corruption checker (`etcdserver/corrupt.go`: `HashByRev`, `Hashes`), the
maintenance server (`v3rpc/maintenance.go`: `Hash`, `HashByRev`), the compaction job (`Store`).

**Changes** from `specs-ref`'s files: `Store` was an axiom over `hashStorageOk`; `Hash`, `HashByRev`,
`Hashes` had no spec (their callers' sketches need one).
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

/-- `HashStorage.Hash`'s contract at `*hashStorage`. -/
def hashStorage.Hash.spec : Prop :=
  ∀ hs : Loc, HashStorage.Hash.contract (GF := GF) (go.GoType.PointerType hashStorage.ty) #hs

end spec
end Mvcc
end EtcdGrove
end Perennial
