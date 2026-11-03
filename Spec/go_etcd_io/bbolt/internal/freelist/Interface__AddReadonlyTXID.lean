/-
`Interface.AddReadonlyTXID` (bbolt/internal/freelist, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U2; used by U5 (`beginTx`). Proof:
`Proof/go_etcd_io/bbolt/internal/freelist/Interface__AddReadonlyTXID.lean` (a `sorry` until U2).
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

/-- `f.AddReadonlyTXID(tid)`: `tid` appended to the readers' txids. -/
abbrev Interface.AddReadonlyTXID.spec : Prop :=
  ∀ (fli : GoInterface) (ro : List w64) (tid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flRoOwn fli ro }}
    (App (Val (fli @!! go_etcd_io.bbolt.internal.freelist.Interface.ty @!! go!"AddReadonlyTXID"))
      (Val #tid))
  {{ RET #(); flRoOwn fli (ro ++ [tid]) }}

end spec

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
