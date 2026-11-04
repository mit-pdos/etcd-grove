/-
`DB.mmapSize` (U4, `notes/bbolt-proof-plan.md`): the mapping size for a database of `size`
bytes. Stated; the proof (a `for` loop over `i ∈ [15, 30]`, then `int64` rounding) is to do.

Note: above 1 GiB the size is rounded up to a whole GiB and then capped at `MaxMapSize`
(`0xFFFFFFFFFFFF`), which is not a multiple of 4096: a mapping need not end on a page
(`mmapSizeOf` below), so an invariant `l % 4096 = 0` on the mapping's length is false for sizes
in `(2^48 - 2^30, 2^48 - 1]` (U4 finding).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Locks
public import Proof.go_etcd_io.bbolt.PkgInit
public import Spec.fmt.ErrorOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

/-- `DB.mmapSize`'s result for `size` (page size 4096): the least power of two from 32 KiB to
1 GiB at least `size`; above that `size` rounded up to a whole GiB, at most `MaxMapSize`; `none`
(an error) above `MaxMapSize`. -/
def mmapSizeOf (size : Nat) : Option Nat :=
  match (List.range 16).find? (fun i => decide (size ≤ 2 ^ (15 + i))) with
  | some i => some (2 ^ (15 + i))
  | none =>
    if size > 0xFFFFFFFFFFFF then none
    else some (min (if size % 0x40000000 > 0 then size + 0x40000000 - size % 0x40000000 else size)
      0xFFFFFFFFFFFF)

section msz
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`db.mmapSize(size)`**: `mmapSizeOf size`, or an `errors.New` error. -/
abbrev DB.mmapSize.spec : Prop :=
  ∀ (db : Loc) (size : w64),
  0 ≤ sint.Z size →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ db.[DB, go!"pageSize"] ↦□ W64 4096 }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"mmapSize")) (Val #size))
  {{ (r : w64) (err : GoInterface), RET (PairV #r #err);
      match mmapSizeOf (sint.nat size) with
      | some s => ⌜err = interface.nil ∧ sint.nat r = s⌝
      | none => ⌜err ≠ interface.nil⌝ ∗ fmtErrorOk err }}

theorem DB.mmapSize.wp_proof : DB.mmapSize.spec (GF := GF) (hG := hG) := by
  sorry

end msz

end bbolt
end EtcdGrove
end Perennial
