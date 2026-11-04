/-
The `*array` freelist implementation meets `FLImpl.Contract` (the methods `shared` calls
back: `FreeCount`, `freePageIds`, `Init`, `mergeSpans`) and `FLImpl.AllocateSpec` (U2).
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.shared__reindex
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Callees
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Sorters
public import Spec.go_etcd_io.bbolt.internal.common.Pgids__Merge

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt
namespace internal
namespace freelist

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

theorem arrayImpl_contract
    (hVerify : bbolt.common.Verify.spec (GF := GF) (hG := hG))
    (hMerge : _root_.Perennial.EtcdGrove.bbolt.internal.common.Pgids.Merge.spec (GF := GF) (hG := hG))
    (a : Loc) : (arrayImpl (GF := GF) a).Contract := by
  sorry

theorem arrayImpl_allocate (a : Loc) : (arrayImpl (GF := GF) a).AllocateSpec := by
  sorry

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
