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
namespace internal
namespace freelist

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common go_etcd_io.bbolt.internal.freelist

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- `f.NoSyncReload(ids)` of increasing ids (`freepages`'): the free ids are `ids` but the
pending ones (`FLPg.noSyncReload`); `ids` only read. -/
abbrev Interface.NoSyncReload.spec : Prop :=
  ∀ (fli : GoInterface) (fl : FLPg) (s : GoSlice) (ids : List w64) (dq : DFrac),
  PgidsIncr ids →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flPgOwn fli fl ∗
      s ↦*{dq} ids }}
    (App (Val (fli @!! go_etcd_io.bbolt.internal.freelist.Interface.ty @!! go!"NoSyncReload"))
      (Val #s))
  {{ RET #(); flPgOwn fli (fl.noSyncReload ids) ∗ s ↦*{dq} ids }}

end spec

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
