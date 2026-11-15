/-
`(*kvHasher).WriteKeyValue(k, v)` (`hash.go:60`). Internal: `scheduleCompaction`, `unsafeHashByRev`.
**Trusted** (names-only): reads the keep map, hashes the entry or skips it; the key must be a
revision's bytes (`BytesToRev`, `BytesToBucketKey` panic otherwise).

**Changes** from `specs-ref`'s file: `hasherAt`, `keepMap`, `revOfBytes` in place of `kvHasherOk`,
`ownMap`, `bucketKeyOk`.
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

/-- `h.WriteKeyValue(k, v)` of a revision's key: no panic, the hasher's revisions unchanged. -/
def kvHasher.WriteKeyValue.spec : Prop :=
  ∀ (hp : Loc) (c r : w64) (keep : GoMap) (dq : DFrac) (K : Rev → Prop) (key val : GoSlice)
    (k v : GoString) (dk dv : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      hasherAt hp c r keep ∗ keepMap keep dq K ∗ key ↦*{dk} k ∗ val ↦*{dv} v ∗
      ⌜(revOfBytes k).isSome⌝ }}
    (App (App (Val (hp @!! go.GoType.PointerType kvHasher.ty @!! go!"WriteKeyValue")) (Val #key))
      (Val #val))
  {{ RET #(); hasherAt hp c r keep ∗ keepMap keep dq K ∗ key ↦*{dk} k ∗ val ↦*{dv} v }}

end spec
end Mvcc
end EtcdGrove
end Perennial
