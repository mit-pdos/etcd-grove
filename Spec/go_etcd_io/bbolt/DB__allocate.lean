/-
`db.allocate(txid, count)` (`db.go`): a page buffer, its id from the freelist (4d's `Allocate`) or past the high-water mark, remapping (`mmap`) when the file must grow.
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)
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
  {{ wtxCore (GF := GF) tx γ C ∗ txDB tx db ∗ ⌜0 < uint.nat cnt⌝ }}
    (App (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"allocate")) (Val #txid)) (Val #cnt))
  {{ (pg : Loc) (err : GoInterface), RET (PairV #pg #err); ∃ C' : TxCore, wtxCore tx γ C' ∗ ⌜uint.nat C.hwm ≤ uint.nat C'.hwm⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
