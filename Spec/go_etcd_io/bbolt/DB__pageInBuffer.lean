/-
`db.pageInBuffer(b, id)` (`db.go`): the page header at `id · pageSize` of a buffer.
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)

**Users.** `getPageSizeFromFirstMeta`/`SecondMeta` (a local 4 KiB array, id 0, while `db.pageSize`
may still be the option's), `init` (ids 0-3 of a `4 · pageSize` buffer, under `dbRaw`),
`Tx.writeMeta` (id 0 of a `pageSize` buffer, the writer under `isBolt`): each holds `db.pageSize`
(`dbRaw`'s or `isBolt`'s realization, read-only after `Open`).

**Changes** (integration I7): was `isBolt` and any buffer and id, post `True`: false for an id past
the buffer (`b[id*pageSize]` panics) and unusable by `init` (no `isBolt` yet). Now the field and
the bound, and the address returned.
-/
module

public import Spec.go_etcd_io.bbolt.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- (internal) the address of page `id` in the buffer `b` (`&b[id * pageSize]`), inside it. -/
def DB.pageInBuffer.spec : Prop :=
  ∀ (db : Loc) (dq : DFrac) (ps : w64) (b : GoSlice) (id : w64),
  {{ (structFieldRef go_etcd_io.bbolt.DB go!"pageSize" db ↦{dq} ps : IProp GF) ∗
      ⌜uint.nat id * uint.nat ps < uint.nat b.len⌝ }}
    (App (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"pageInBuffer")) (Val #b)) (Val #id))
  {{ RET #(sliceIndexRef w8 ((uint.nat id * uint.nat ps : Nat) : Int) b);
      structFieldRef go_etcd_io.bbolt.DB go!"pageSize" db ↦{dq} ps }}

end spec

end Bbolt
end EtcdGrove
end Perennial
