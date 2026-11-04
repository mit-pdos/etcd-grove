/-
The two implementations' contracts, for any implementation of `flPgOwn` (`FLImpl.IsImpl`), from
the callee specs U2's proofs take as hypotheses (`FLCallees`).
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.ArrayContract
public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.HashContract
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Open
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Callees
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Sorters
public import Spec.go_etcd_io.bbolt.internal.common.Pgids__Merge
public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.array.Basic
public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.array.mergeSpans
public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.array.Allocate

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

/-- The callee specs (and the Perennial gap `PidSetDeleteUnfold`) U2's freelist proofs rest on:
U1's `internal/common` specs and the trust-boundary specs of `Lemmas/Callees.lean`. -/
structure FLCallees : Prop where
  verify : bbolt.common.Verify.spec (GF := GF) (hG := hG)
  merge : _root_.Perennial.EtcdGrove.bbolt.internal.common.Pgids.Merge.spec (GF := GF) (hG := hG)
  sliceIsSorted : bbolt.sort.SliceIsSorted.spec (GF := GF) (hG := hG)
  deepEqual : bbolt.reflect.DeepEqual_pgidSet.spec (GF := GF) (hG := hG)
  delUnfold : PidSetDeleteUnfold (GF := GF)

theorem impl_contract (h : FLCallees (GF := GF) (hG := hG)) :
    ∀ (I : FLImpl (GF := GF)) a, I.IsImpl a → I.Contract := by
  intro I a hI
  rcases hI with rfl | rfl
  · exact arrayImpl_contract h.verify h.merge a
  · exact hashImpl_contract h.delUnfold h.verify h.sliceIsSorted h.deepEqual a

theorem impl_allocate (h : FLCallees (GF := GF) (hG := hG)) :
    ∀ (I : FLImpl (GF := GF)) a, I.IsImpl a → I.AllocateSpec := by
  intro I a hI
  rcases hI with rfl | rfl
  · exact arrayImpl_allocate a
  · exact hashImpl_allocate h.delUnfold a

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
