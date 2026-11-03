/-
`Interface.Reload` (bbolt/internal/freelist, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U2; used by U10 (`rollback` with a synced freelist). Proof:
`Proof/go_etcd_io/bbolt/internal/freelist/Interface__Reload.lean` (a `sorry` until U2).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Freelist
public import Proof.go_etcd_io.bbolt.PkgInit
public import Proof.go_etcd_io.bbolt.Model.Mvcc

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

/-- `f.Reload(p)`: the free ids are the freelist page `pg`'s (at `p`, read at any fraction) but
the pending ones (`FLPg.reload`). It panics on a page of another type or a count above `2^63`:
excluded by the premises (the ids within the page). -/
abbrev Interface.Reload.spec : Prop :=
  ∀ (fli : GoInterface) (fl : FLPg) (p : Loc) (pg : List w8) (dq : DFrac),
  pageFlags pg = freelistPageFlag →
  16 + 8 * (flCountIdx pg).2 + 8 * (flCountIdx pg).1 ≤ pg.length →
  (flCountIdx pg).1 < 2 ^ 63 → 0 < p.addr → p.addr + pg.length ≤ maxAddr →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flPgOwn fli fl ∗
      bytesPointsto p dq pg }}
    (App (Val (fli @!! go_etcd_io.bbolt.internal.freelist.Interface.ty @!! go!"Reload"))
      (Val #p))
  {{ RET #(); flPgOwn fli (fl.reload (flIds pg)) ∗ bytesPointsto p dq pg }}

end spec

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
