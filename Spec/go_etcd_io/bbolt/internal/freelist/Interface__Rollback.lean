/-
`Interface.Rollback` (bbolt/internal/freelist, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U2; used by U5 (`Tx.Rollback` of a writer), U10 (`rollback`). Proof:
`Proof/go_etcd_io/bbolt/internal/freelist/Interface__Rollback.lean` (a `sorry` until U2).
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

/-- `f.Rollback(txid)`: `txid`'s pending pages are not pending, its allocations forgotten
(`FLPg.rollback`). It panics if a page pending for `txid` was allocated by `txid`: excluded by
the premise. -/
abbrev Interface.Rollback.spec : Prop :=
  ∀ (fli : GoInterface) (fl : FLPg) (txid : w64),
  (∀ pd, fl.pending !! txid = some pd → txid ∉ pd.alloctx) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flPgOwn fli fl }}
    (App (Val (fli @!! go_etcd_io.bbolt.internal.freelist.Interface.ty @!! go!"Rollback"))
      (Val #txid))
  {{ RET #(); flPgOwn fli (fl.rollback txid) }}

end spec

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
