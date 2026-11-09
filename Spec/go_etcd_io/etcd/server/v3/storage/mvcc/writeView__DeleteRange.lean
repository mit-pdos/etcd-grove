/-
`(*writeView).DeleteRange(key, end)` (`kv_view.go:46`): `rv.kv.Write(traceutil.TODO())`, its
`DeleteRange`, its `End` (deferred). Internal: the body of the store's promoted `DeleteRange`
(`KV.DeleteRange.contract`). Proof sketch: as `writeView.Put`, with `Txn.DeleteRange.contract` (the
range's present keys `ds` of `σ.kv.store`, the outer update's `∀∀ ds` instantiated at them).

**Changes** from `specs-ref`'s file: `KV.DeleteRange.contract`'s statement at the view's store.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI EtcdModel EtcdWire go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `KV.DeleteRange`'s behaviour for the store the view writes. -/
def writeView.DeleteRange.spec : Prop :=
  ∀ (wv : Loc) (kv : GoInterface) (γ : MvccName) (γl : Lease.Names) (key endk : GoSlice)
    (kk e : Bytes) (dk de : DFrac) (n : Nat) (ls : Lease.LessorState) (q : Qp) (B : MvccStorage)
    (Pk Pre Q' Post : IProp GF) (f : GoFunc) (Q : MvccState → List Key → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      wv.[writeView, go!"kv"] ↦□ kv ∗ isMvcc kv γ ∗ mvccLessorIs γ γl ∗ mvccReaders γ 1 ∗
      key ↦*{dk} kk ∗ endk ↦*{de} e ∗ Lease.lessorState γl n ls ∗
      mvccBackend γ q B Pk ∗ hookIs B f ∗ Pre ∗ hookRun Pk f Pre Q' ∗ (Q' ={⊤}=∗ Pk ∗ Post) ∗
      AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅
        <{ ∀∀ (ds : List Key), ⌜σ.pending = [] ∧ rangeKeys σ.kv.store (mrange kk endk e) ds⌝ ∗
            mvccState γ (σ.notify (ds.map .delete)) ∗
            ⧖ (evCount (σ.kv.commit (ds.map .delete))), COMM
            AU <{ ∃∃ (σ' : MvccState), mvccState γ σ' }> @ ⊤ \ ↑mvccN, ∅
              <{ ⌜σ' = σ.notify (ds.map .delete)⌝ ∗ mvccState γ σ'.commitPending,
                 COMM Q σ ds }> }> }}
    (App (App (Val (wv @!! go.GoType.PointerType writeView.ty @!! go!"DeleteRange")) (Val #key))
      (Val #endk))
  {{ (nd rev : w64), RET (PairV #nd #rev); mvccReaders γ 1 ∗ mvccBackend γ q B Pk ∗ Post ∗
      key ↦*{dk} kk ∗ endk ↦*{de} e ∗
      ∃ (σ : MvccState) (ds : List Key) (n' : Nat), Q σ ds ∗ Lease.lessorState γl n' (delsLs ls ds) ∗
        ⌜nd = W64 ds.length ∧ rev = W64 (if ds = [] then σ.rev else σ.rev + 1)⌝ }}

end spec
end Mvcc
end EtcdGrove
end Perennial
