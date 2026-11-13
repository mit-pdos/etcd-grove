/-
`Interface.RemoveReadonlyTXID` (bbolt/internal/freelist, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U2; used by U5 (`removeTx`). Proof:
`Proof/go_etcd_io/bbolt/internal/freelist/Interface__RemoveReadonlyTXID.lean` (a `sorry` until U2).
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

/-- `f.RemoveReadonlyTXID(tid)`: one occurrence of `tid` removed from the readers' txids (the
last moved into its place: the order is a permutation's).
Stated over `ifaceCall fli m`, what the call steps to (U2 fix, 2026-11-04: Go's `fl.M(args)`
resolves the interface value's dynamic method; `methods Interface.ty m` has no semantics). -/
abbrev Interface.RemoveReadonlyTXID.spec : Prop :=
  ∀ (fli : GoInterface) (ro : List w64) (tid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flRoOwn fli ro }}
    (App (ifaceCall fli go!"RemoveReadonlyTXID") (Val #tid))
  {{ RET #(); ∃ ro', flRoOwn fli ro' ∗ ⌜ro'.Perm (ro.erase tid)⌝ }}

end spec

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
