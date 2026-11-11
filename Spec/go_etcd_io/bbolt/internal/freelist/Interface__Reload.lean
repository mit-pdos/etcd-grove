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

/-- `f.Reload(p)`: the free ids are the freelist page `pg`'s (at `p`, read at any fraction) but
the pending ones (`FLPg.reload`). It panics on a page of another type or a count above `2^63`:
excluded by the premises (the ids within the page).
Stated over `ifaceCall fli m`, what the call steps to (U2 fix, 2026-11-04: Go's `fl.M(args)`
resolves the interface value's dynamic method; `methods Interface.ty m` has no semantics).
The premises `(flIds pg).Nodup`, ids at least 2, the length bound with the pending ids (else
`fl.reload (flIds pg)` is not `FLPg.WF`, which `flPgOwn` requires) and `flIds pg ≠ [] ∨ fl.free
= []` (an empty page makes `hashMap.Init` of no ids return before `reindex`, keeping the old
cache) are U2's fix: false without them. -/
abbrev Interface.Reload.spec : Prop :=
  ∀ (fli : GoInterface) (fl : FLPg) (p : Loc) (pg : List w8) (dq : DFrac),
  pageFlags pg = freelistPageFlag →
  16 + 8 * (flCountIdx pg).2 + 8 * (flCountIdx pg).1 ≤ pg.length →
  (flCountIdx pg).1 < 2 ^ 63 → 0 < p.addr → p.addr + pg.length ≤ maxAddr →
  (flIds pg).Nodup → (∀ x ∈ flIds pg, 2 ≤ x.toNat) →
  (flIds pg).length + fl.pendingIds.length < 2 ^ 63 → (flIds pg ≠ [] ∨ fl.free = []) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flPgOwn fli fl ∗
      bytesPointsto p dq pg }}
    (App (ifaceCall fli go!"Reload") (Val #p))
  {{ RET #(); flPgOwn fli (fl.reload (flIds pg)) ∗ bytesPointsto p dq pg }}

end spec

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
