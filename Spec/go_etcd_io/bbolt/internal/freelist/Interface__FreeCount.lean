/-
`Interface.FreeCount` (bbolt/internal/freelist, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U2; used by U5 (`Tx.close`), U11 (`loadFreelist`). Proof:
`Proof/go_etcd_io/bbolt/internal/freelist/Interface__FreeCount.lean` (a `sorry` until U2).
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

/-- `f.FreeCount()`: the number of free ids. -/
abbrev Interface.FreeCount.spec : Prop :=
  ∀ (fli : GoInterface) (fl : FLPg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flPgOwn fli fl }}
    (App (Val (fli @!! go_etcd_io.bbolt.internal.freelist.Interface.ty @!! go!"FreeCount"))
      (Val #()))
  {{ RET #(W64 (fl.free.length : Int)); flPgOwn fli fl }}

end spec

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
