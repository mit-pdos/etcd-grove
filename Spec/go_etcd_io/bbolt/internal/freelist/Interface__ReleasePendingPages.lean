/-
`Interface.ReleasePendingPages` (bbolt/internal/freelist, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U2; used by U5 (`beginRWTx`). Proof:
`Proof/go_etcd_io/bbolt/internal/freelist/Interface__ReleasePendingPages.lean` (a `sorry` until U2).
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

/-- `f.ReleasePendingPages()` (under `metalock`, which holds the read-only part `flRoOwn`): the
pages pending for transactions no reader can see are free (`FLPg.releasePending` with the
readers' txids `ro`, which it sorts in place). -/
abbrev Interface.ReleasePendingPages.spec : Prop :=
  ∀ (fli : GoInterface) (fl : FLPg) (ro : List w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flPgOwn fli fl ∗
      flRoOwn fli ro }}
    (App (Val (fli @!! go_etcd_io.bbolt.internal.freelist.Interface.ty @!!
      go!"ReleasePendingPages")) (Val #()))
  {{ RET #(); flPgOwn fli (fl.releasePending ro) ∗ flRoOwn fli (sortPgids ro) }}

end spec

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
