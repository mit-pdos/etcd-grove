/-
`db.allocate(txid, count)` (`db.go`): a page buffer, its id from the freelist (4d's `Allocate`) or past the high-water mark, remapping (`mmap`) when the file must grow.
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)

**Proof sketch.** The buffer: `pagePool.Get()` (a zeroed page) or `make([]byte, count*pageSize)`;
`SetOverflow(uint32(count - 1))`; 4d's `Interface.Allocate.spec` (`0 < count` as an `int`) under
`rwlock` (`flOwn` in `wtxCore`): `0` or a free run (`canAlloc`, now `txid`'s in `allocs`), else
the high-water mark and a remap.

**Changes (integration I7).** `count` is an `int`: the premise was `0 < uint.nat cnt`, which a
negative `int` meets (then `make` panics and `Allocate`'s `0 < sint.Z n` fails); now
`0 < sint.Z cnt < 2 ^ 32` (`make`'s size, and the overflow stored as a `uint32`). Callers meet
it: a spilled node is below `2 ^ 32` bytes, the freelist page below `2 ^ 36 * 8` bytes.
Verify-round (A11 F9): the post gives the buffer (`freshPage`: the id, the overflow, an empty
header; a pooled page is zeroed when `tx.write` returns it to the pool) to `Tx.allocate`, which
records it in `tx.pages` (`C.bufs`), and keeps the abstraction relation (`repKept`).
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

/-- (internal) a page run for the writer, or an error (a remap's). -/
def DB.allocate.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (db : Loc) (γ : BoltName) (C : TxCore) (txid cnt : w64),
  {{ wtxCore (GF := GF) tx γ C ∗ txDB tx db ∗ ⌜0 < sint.Z cnt ∧ sint.Z cnt < 2 ^ 32⌝ }}
    (App (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"allocate")) (Val #txid)) (Val #cnt))
  {{ (pg : Loc) (err : GoInterface), RET (PairV #pg #err); ∃ C' : TxCore, wtxCore tx γ C' ∗
      ⌜uint.nat C.hwm ≤ uint.nat C'.hwm ∧ repKept C C' ∧ C'.pages = C.pages ∧ C'.bufs = C.bufs⌝ ∗
      (⌜err ≠ GoInterface.nil⌝ ∨
       (⌜err = GoInterface.nil⌝ ∗ ∃ (id : w64) (bs : List w8), bytesPointsto pg (DFrac.own 1) bs ∗
         ⌜freshPage id cnt bs ∧ id ∉ C.pages ∧ 2 ≤ uint.nat id ∧
           uint.nat id + uint.nat cnt ≤ uint.nat C'.hwm⌝)) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
