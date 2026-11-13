/-
`Interface.EstimatedWritePageSize` (bbolt/internal/freelist, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U2; used by U5 (`Tx.close`), U10 (`commitFreelist`). Proof:
`Proof/go_etcd_io/bbolt/internal/freelist/Interface__EstimatedWritePageSize.lean` (a `sorry` until U2).
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

/-- `f.EstimatedWritePageSize()`: the bytes `Write` needs: a header, and 8 bytes per free or
pending id, plus one for the count when there are `0xFFFF` or more.
Stated over `ifaceCall fli m`, what the call steps to (U2 fix, 2026-11-04: Go's `fl.M(args)`
resolves the interface value's dynamic method; `methods Interface.ty m` has no semantics). -/
abbrev Interface.EstimatedWritePageSize.spec : Prop :=
  ∀ (fli : GoInterface) (fl : FLPg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flPgOwn fli fl }}
    (App (ifaceCall fli go!"EstimatedWritePageSize") (Val #()))
  {{ RET #(W64 ((16 + 8 * (fl.allIds.length +
        (if 0xFFFF ≤ fl.allIds.length then 1 else 0)) : Nat) : Int)); flPgOwn fli fl }}

end spec

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
