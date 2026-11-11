/-
`Interface.NoSyncReload` (bbolt/internal/freelist, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U2; used by U10 (`rollback` without a synced freelist). Proof:
`Proof/go_etcd_io/bbolt/internal/freelist/Interface__NoSyncReload.lean` (a `sorry` until U2).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Freelist
public import Proof.go_etcd_io.bbolt.PkgInit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs
namespace internal
namespace freelist

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common go_etcd_io.bbolt.internal.freelist

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- `f.NoSyncReload(ids)` of increasing ids (`freepages`'): the free ids are `ids` but the
pending ones (`FLPg.noSyncReload`); `ids` only read.
Stated over `ifaceCall fli m`, what the call steps to (U2 fix, 2026-11-04: Go's `fl.M(args)`
resolves the interface value's dynamic method; `methods Interface.ty m` has no semantics).
The premises ids at least 2, the length bound with the pending ids (else the result is not
`FLPg.WF`) and `(fl.noSyncReload ids).free ≠ [] ∨ fl.free = []` (`hashMap.Init` of no ids keeps
the old cache) are U2's fix: false without them. -/
abbrev Interface.NoSyncReload.spec : Prop :=
  ∀ (fli : GoInterface) (fl : FLPg) (s : GoSlice) (ids : List w64) (dq : DFrac),
  PgidsIncr ids → (∀ x ∈ ids, 2 ≤ x.toNat) → ids.length + fl.pendingIds.length < 2 ^ 63 →
  ((fl.noSyncReload ids).free ≠ [] ∨ fl.free = []) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flPgOwn fli fl ∗
      s ↦*{dq} ids }}
    (App (ifaceCall fli go!"NoSyncReload") (Val #s))
  {{ RET #(); flPgOwn fli (fl.noSyncReload ids) ∗ s ↦*{dq} ids }}

end spec

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
