/-
`newFreelist` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U2; used by U11 (`loadFreelist`). Proof:
`Proof/go_etcd_io/bbolt/newFreelist.lean` (a `sorry` until U2).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Freelist
public import Proof.go_etcd_io.bbolt.PkgInit

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

/-- `newFreelist(t)`: a fresh freelist (an array, or a hash map for `FreelistMapType`), empty,
with no read-only transaction. -/
abbrev newFreelist.spec : Prop :=
  ∀ (t : FreelistType),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt }}
    (App (Val #(functions newFreelist [])) (Val #t))
  {{ (fli : GoInterface), RET #fli; ⌜fli ≠ interface.nil⌝ ∗ flPgOwn fli FLPg.empty ∗
      flRoOwn fli [] }}

end spec

end bbolt
end EtcdGrove
end Perennial
