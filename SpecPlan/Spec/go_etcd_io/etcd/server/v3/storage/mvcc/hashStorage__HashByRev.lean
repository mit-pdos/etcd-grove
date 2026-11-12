/-
`(*hashStorage).HashByRev` (`hash.go:139`): a stored hash for the revision, or `store.hashByRev` (`s.mu`, `s.revMu`, a read transaction of the storage; its current revision may be `1` during a `Restore`: `issues/etcd-mvcc-hashbyrev-restore-rev1.md`; a hash stored at revision `0`: `issues/etcd-mvcc-hashbyrev-zero-stored.md`). **Trusted**: hash.go is translated names-only; the
contract (`Api.lean`'s `HashStorage.HashByRev.contract`) claims only that it returns (the reader token
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

/-- `HashStorage.HashByRev`'s contract at `*hashStorage`. -/
def hashStorage.HashByRev.spec : Prop :=
  ∀ hs : Loc, HashStorage.HashByRev.contract (GF := GF) (go.GoType.PointerType hashStorage.ty) #hs

end spec
end Mvcc
end EtcdGrove
end Perennial
