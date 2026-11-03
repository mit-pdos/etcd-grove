/-
`Interface.Allocate` (bbolt/internal/freelist, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U2; used by U4 (`DB.allocate`). Proof:
`Proof/go_etcd_io/bbolt/internal/freelist/Interface__Allocate.lean` (a `sorry` until U2).
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

/-- `f.Allocate(txid, n)` (`n > 0`): `0`, nothing changed; or the first id `r` of `n` free ids
in a row, now allocated by `txid` (`FLPg.alloc`). Which run the implementation picks is left
open (the array picks the first, the hash map any). -/
abbrev Interface.Allocate.spec : Prop :=
  ∀ (fli : GoInterface) (fl : FLPg) (txid n : w64),
  0 < sint.Z n →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flPgOwn fli fl }}
    (App (App (Val (fli @!! go_etcd_io.bbolt.internal.freelist.Interface.ty @!! go!"Allocate"))
      (Val #txid)) (Val #n))
  {{ (r : w64), RET #r;
      (⌜r = W64 0⌝ ∗ flPgOwn fli fl) ∨
      (⌜r ≠ W64 0 ∧ fl.canAlloc r (sint.nat n)⌝ ∗ flPgOwn fli (fl.alloc txid r (sint.nat n))) }}

end spec

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
