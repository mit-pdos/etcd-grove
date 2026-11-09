/-
`tx.WriteTo(w)` (`tx.go`): the database as of the transaction, as a file image: two meta pages
(the current at page `txid % 2`, the fork's D21), then the data pages `[2, hwm)` read from the
file (`io.CopyN` of a section reader of the database's fd).

**Users.** etcd's backend snapshot (`backend.Snapshot`, `backend.go:386`; `snapshot` embeds the
`*bolt.Tx`, so `s.WriteTo(w)` is this method), streamed through a pipe by the server's snapshot
sender (2d's `newSnapshotReaderCloser`) and the maintenance service. Snippet: `ReqSnapshot`.

**Proof sketch.** `WriteFlag = 0` (`boltTx` owns it): the database's own fd. The meta pages from
`tx.meta` (4d's `Meta.Copy`, `DecTxid`, `Sum64`, `SetChecksum`), each one `Write` by `writerOk`;
then `io.CopyN(w, sr, size - 2·pageSize)`, whose reads (`pread` of pages below the transaction's
high-water mark) see the pages of the transaction's meta (no commit frees them while it is live:
pending for its txid) and whose writes go through `Write` (`writerPlain`: no `ReadFrom`). What is
written, all of it, is an image of `T.base` (`boltImage`): a write transaction writes its base (its
changes are in nodes until `Commit`).

**Changes.** New (the old API left it out).

**Margin.** The `int64` count is the bytes written (stated as `uint.nat n`). `io.CopyN`'s spec is
Perennial's `io` model's (a need recorded in the report).
-/
module

public import Spec.go_etcd_io.bbolt.Api

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

/-- `tx.WriteTo(w)`: streams the database as of the transaction to `w` (`writerOk`): the bytes
written are a prefix of an image of `T.base`, all of it unless there is an error. -/
def Tx.WriteTo.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (w : GoInterface)
    (W : List w8 → IProp GF) (bs : List w8),
  {{ boltTx (GF := GF) tx γ q T ∗ writerOk w W ∗ W bs }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"WriteTo")) (Val #w))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err); boltTx tx γ q T ∗
      ∃ (ys img : List w8), W (bs ++ ys) ∗
        ⌜boltImage img T.base ∧ ys <+: img ∧ uint.nat n = ys.length ∧
          (err = GoInterface.nil → ys = img)⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
