/-
`newKVHasher(compactRev, rev, keep)` (`hash.go:49`). Internal: `scheduleCompaction`, `hashByRev`.
**Trusted** (hash.go is translated names-only): a `kvHasher` over crc32-Castagnoli (seeded with the
`Key` bucket's name) of the given revisions and keep map; nothing about the crc's value.

**Changes** from `specs-ref`'s file: `hasherVal` in place of `kvHasherOk`.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalStore

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

/-- `newKVHasher(prev, rev, keep)`: a hasher value of `(prev, rev]` and `keep`. -/
def newKVHasher.spec : Prop :=
  ∀ (prev rev : w64) (keep : GoMap),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.newKVHasher)) (Val #prev))
      (Val #rev)) (Val #keep))
  {{ (h : kvHasher), RET #h; hasherVal h prev rev keep }}

end spec
end Mvcc
end EtcdGrove
end Perennial
