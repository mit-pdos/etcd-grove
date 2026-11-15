/-
`tx.allocate(count)` (`tx.go`): `db.allocate`, the page recorded in `tx.pages`, stats.
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)

**Changes (integration I7).** `0 < sint.Z cnt < 2 ^ 32` (was `0 < uint.nat cnt`): `count` is an
`int`; `DB.allocate.spec`'s premise. Verify-round (A11 F9): the page's buffer is stated (in
`C'.bufs`, a `freshPage` of the run: what `node.write` and `freelist.Write` need, lent by
`wtxCore_buf`), and the cache keeps the abstraction relation (`repKept`).
-/
module

public import SpecPlan.Spec.go_etcd_io.bbolt.Internal

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

/-- (internal) a fresh run of `count` pages below the new high-water mark, or an error. -/
def Tx.allocate.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (C : TxCore) (cnt : w64),
  {{ wtxCore (GF := GF) tx γ C ∗ ⌜0 < sint.Z cnt ∧ sint.Z cnt < 2 ^ 32⌝ }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"allocate")) (Val #cnt))
  {{ (pg : Loc) (err : GoInterface), RET (PairV #pg #err); ∃ C' : TxCore, wtxCore tx γ C' ∗
      ⌜repKept C C' ∧ (err = GoInterface.nil → ∃ id bs, id ∈ C'.pages ∧ id ∉ C.pages ∧
        uint.nat id + uint.nat cnt ≤ uint.nat C'.hwm ∧ C'.bufs id = some (pg, bs) ∧
        freshPage id cnt bs)⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
