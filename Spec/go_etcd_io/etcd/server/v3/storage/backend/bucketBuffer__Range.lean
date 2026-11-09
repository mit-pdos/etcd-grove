/-
`bb.Range(key, endKey, limit)` (`tx_buffer.go:164-187`): translated; internal. A binary search
(`sort.Search`) over the sorted used entries, then the key alone or the range up to `limit`.
Changes: the sortedness a premise. Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Backend

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **`bb.Range(k, e, limit)`** on a sorted buffer: `bbRangeOk`. -/
def bucketBuffer.Range.spec : Prop :=
  ∀ (bb : Loc) (l : List (GoString × GoString)) (w : Bool) (ks es : GoSlice) (dk de : DFrac)
    (k e : GoString) (limit : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ bbAt bb l w ∗ ⌜l.Pairwise (fun a b => go.GoStringLt a.1 b.1) ∧ 0 < sint.Z limit⌝ ∗
      ks ↦*{dk} k ∗ es ↦*{de} e }}
    (App (App (App (Val (bb @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.bucketBuffer.ty @!! go!"Range")) (Val #ks)) (Val #es)) (Val #limit))
  {{ (kl vl : GoSlice), RET (PairV #kl #vl); bbAt bb l w ∗ ks ↦*{dk} k ∗ es ↦*{de} e ∗
      ∃ r, ⌜bbRangeOk l k e (sint.Z limit) r⌝ ∗
        bytesListAt kl (r.map Prod.fst) DFrac.discard ∗ bytesListAt vl (r.map Prod.snd) DFrac.discard }}

end spec

end Backend
end EtcdGrove
end Perennial
