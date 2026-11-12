/-
`Interface.Init` (bbolt/internal/freelist, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U2; used by U11 (`loadFreelist`, without a synced freelist). Proof:
`Proof/go_etcd_io/bbolt/internal/freelist/Interface__Init.lean` (a `sorry` until U2).
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

/-- `f.Init(ids)` of a fresh freelist, with increasing ids from 2 on (the hash map panics on
unsorted ones): the free ids are `ids` (`FLPg.ofInit`); the array keeps the slice.
Stated over `ifaceCall fli m`, what the call steps to (U2 fix, 2026-11-04: Go's `fl.M(args)`
resolves the interface value's dynamic method; `methods Interface.ty m` has no semantics). -/
abbrev Interface.Init.spec : Prop :=
  ∀ (fli : GoInterface) (s : GoSlice) (ids : List w64),
  PgidsIncr ids → (∀ x ∈ ids, 2 ≤ x.toNat) → ids.length < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗
      flPgOwn fli FLPg.empty ∗ s ↦* ids ∗ ownSliceCap w64 s (DFrac.own 1) }}
    (App (ifaceCall fli go!"Init") (Val #s))
  {{ RET #(); flPgOwn fli (FLPg.ofInit ids) }}

end spec

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
