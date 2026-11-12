/-
The proof of `Spec/go_etcd_io/bbolt/Tx__write_ext.lean` (maintainer 12, item 3 of
`notes/bbolt-proof-plan.md`): `Commit/WriteExtRun.Tx.write_ext_gen` (U10w, U10w2), `Tx.write`'s
loops with the target slots held relative to the file's current size, the pages inside the file
and past its end alike.
-/
module

public import Spec.go_etcd_io.bbolt.Tx__write_ext
public import Proof.go_etcd_io.bbolt.Commit.WriteExtRun

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`tx.write()` with the pages anywhere in the mapping** (see the file header). -/
theorem Tx.write_ext.wp_proof (hLogger : DB.Logger.spec (GF := GF) (hG := hG))
    (hSort : sort.«Sort».anyLessSpec (GF := GF) (hG := hG))
    (hOv : internal.common.Page.Overflow.spec (GF := GF) (hG := hG))
    (hId : internal.common.Page.Id.spec (GF := GF) (hG := hG))
    (hUBS : internal.common.UnsafeByteSlice.spec (GF := GF) (hG := hG))
    (hWriteAt : os.File.WriteAt.spec (GF := GF) (hG := hG))
    (hSync : fdatasync.spec (GF := GF) (hG := hG))
    (hInc : TxStats.IncWrite.spec (GF := GF) (hG := hG)) :
    Tx.write_ext.spec (GF := GF) (hG := hG) :=
  Tx.write_ext_gen hLogger hSort hOv hId hUBS hWriteAt hSync hInc

end proof

end bbolt
end EtcdGrove
end Perennial
