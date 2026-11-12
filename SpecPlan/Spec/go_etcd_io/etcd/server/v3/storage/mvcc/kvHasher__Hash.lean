/-
`(*kvHasher).Hash()` (`hash.go:92`). Internal: `scheduleCompaction`, `unsafeHashByRev`.
**Trusted** (names-only): the hash of what was written, with the hasher's revisions.

**Changes** from `specs-ref`'s file: `hasherAt`; the fields stated, the crc not.
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

/-- `h.Hash()`: a `KeyValueHash` of the hasher's compaction revision and revision. -/
def kvHasher.Hash.spec : Prop :=
  ∀ (hp : Loc) (c r : w64) (keep : GoMap),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      hasherAt hp c r keep }}
    (App (Val (hp @!! go.GoType.PointerType kvHasher.ty @!! go!"Hash")) (Val #()))
  {{ (kh : KeyValueHash), RET #kh; hasherAt hp c r keep ∗
      ⌜kh.CompactRevision' = c ∧ kh.Revision' = r⌝ }}

end spec
end Mvcc
end EtcdGrove
end Perennial
