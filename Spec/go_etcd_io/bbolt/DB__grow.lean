/-
`DB.grow` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U4; used by U10 (`Commit`). Proof:
`Proof/go_etcd_io/bbolt/DB__grow.lean` (a `sorry` until U4).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx
public import Spec.fmt.ErrorOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `db.grow(sz)` by the live writer: the file truncated up to (about) `sz` and synced unless
`NoGrowSync` (`wdbGrown`: only the file's size and the `W` slots it adds change); an error is a
`fmtErrorOk` one, the file's size possibly changed. -/
abbrev DB.grow.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (v : View) (w : WDb) (sz : w64),
  0 ≤ sint.Z sz →
  {{ K.core (GF := GF) ∗ wdbW K tx v w }}
    (App (Val (K.db @!! go.GoType.PointerType DB.ty @!! go!"grow")) (Val #sz))
  {{ (err : GoInterface), RET #err; ∃ w' : WDb, wdbW K tx v w' ∗ ⌜wdbGrown w w'⌝ ∗
      (⌜err = interface.nil⌝ ∨ ⌜err ≠ interface.nil⌝ ∗ fmtErrorOk err) }}

end spec

end bbolt
end EtcdGrove
end Perennial
