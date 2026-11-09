/-
`(*writeView).Put(key, value, lease)` (`kv_view.go:52`): `rv.kv.Write(traceutil.TODO())`, its `Put`,
its `End` (deferred). Internal: the body of the store's promoted `Put` (`KV.Put.contract`). Proof
sketch: `KV.Write.contract` at `kv` (the caller's update's atomic precondition read there, nothing
pending: the write transaction pinned at `σ`), `Txn.Put.contract` (`putLs` over `txnStore σ [] =
σ.kv.store`), `Txn.End.contract` (`.write σ [ev σ]`: the caller's two nested updates).

**Changes** from `specs-ref`'s file: `KV.Put.contract`'s statement at the view's store.
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

/-- `KV.Put`'s behaviour for the store the view writes. -/
def writeView.Put.spec : Prop :=
  ∀ (wv : Loc) (kv : GoInterface) (γ : MvccName) (γl : Lease.Names) (key value : GoSlice)
    (kk vv : Bytes) (lid : w64) (n : Nat) (ls : Lease.LessorState) (q : Qp) (B : MvccStorage)
    (Pk Pre Q' Post : IProp GF) (f : GoFunc) (Q : MvccState → IProp GF),
  let ev (σ : MvccState) := putEv σ [] kk vv (sint.Z lid)
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      wv.[writeView, go!"kv"] ↦□ kv ∗ isMvcc kv γ ∗ mvccLessorIs γ γl ∗ mvccReaders γ 1 ∗
      key ↦*□ kk ∗ value ↦*□ vv ∗
      Lease.lessorState γl n ls ∗ ⌜sint.Z lid = 0 ∨ ls.leases (sint.Z lid) ≠ none⌝ ∗
      mvccBackend γ q B Pk ∗ hookIs B f ∗ Pre ∗ hookRun Pk f Pre Q' ∗ (Q' ={⊤}=∗ Pk ∗ Post) ∗
      AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅
        <{ ⌜σ.pending = []⌝ ∗ mvccState γ (σ.notify [ev σ]) ∗ ⧖ (evCount (σ.kv.commit [ev σ])), COMM
            AU <{ ∃∃ (σ' : MvccState), mvccState γ σ' }> @ ⊤ \ ↑mvccN, ∅
              <{ ⌜σ' = σ.notify [ev σ]⌝ ∗ mvccState γ σ'.commitPending, COMM Q σ }> }> }}
    (App (App (App (Val (wv @!! go.GoType.PointerType writeView.ty @!! go!"Put")) (Val #key))
      (Val #value)) (Val #lid))
  {{ (rev : w64), RET #rev; mvccReaders γ 1 ∗ mvccBackend γ q B Pk ∗ Post ∗
      ∃ (σ : MvccState) (n' : Nat), Q σ ∗
        Lease.lessorState γl n' (putLs ls (σ.kv.store kk).isSome kk (sint.Z lid)) ∗
        ⌜rev = W64 (σ.rev + 1)⌝ }}

end spec
end Mvcc
end EtcdGrove
end Perennial
