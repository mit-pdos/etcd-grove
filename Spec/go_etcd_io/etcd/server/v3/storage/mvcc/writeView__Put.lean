/-
`writeView.Put` (kv_view.go). Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `wv.Put(key, value, lease)`: a write transaction of one put, committed: the new revision
(`ilog`'s length, for the committed log `ilog` the transaction found) is certified. Under the
batch lock, by the critical-section contract (`csContract`: the store's hook on `Pre`, the
caller's update to `Post` before `Unlock`). For a store without watchers (`γ.watchQ = false`, unit
W-K: the watchable store replaces the views). (Unit T3, L2b, 2026-10-25) The lease owner's item
map `I` is that of every log the store certifies (the caller does not know which log the
transaction finds: satisfiable by a store whose keys never had a lease, `I = ∅`); after, the
committed state's. -/
abbrev mvcc.writeView.Put.spec : Prop :=
  ∀ (wv s : Loc) (γ : mvcc.StoreNames) (P Pre Q Post : IProp GF) (f : val)
    (key value : GoSlice) (k v : GoString) (leaseID : w64) (L : List w64)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWriteView wv s γ ∗ mvcc.storeReader s γ ∗ mvcc.revToken γ ∗ mvcc.storeWT γ ∗
      mvcc.hookIs γ P f ∗ mvcc.csContract P f Pre Q Post ∗ mvcc.certFree γ ∗ key ↦*□ k ∗
      value ↦*□ v ∗ ⌜(k.length : Int) < 2 ^ 63 - 1⌝ ∗ lease.leaseOwn γ.leases L I ∗
      □ (∀ ilog : mvcc.Log, mvcc.idxCert γ.idx ilog -∗ ⌜mvcc.pendItems ilog [] = I⌝) ∗
      ⌜leaseID = W64 0 ∨ leaseID ∈ L⌝ ∗
      ⌜γ.watchQ = false⌝ }}
    (App (App (App (Val (wv @!! go.GoType.PointerType writeView.ty @!! go!"Put")) (Val #key))
      (Val #value)) (Val #leaseID))
  {{ (rev : w64), RET #rev; mvcc.storeReader s γ ∗ Post ∗
      ∃ ilog : mvcc.Log, mvcc.idxCert γ.idx (ilog ++ [[.put k v leaseID]]) ∗
        lease.leaseOwn γ.leases L (mvcc.pendItems ilog [.put k v leaseID]) ∗
        ⌜rev = W64 (ilog.length : Int)⌝ }}

/-- **Candidate** (round 8, 2026-11-02, `notes/mvcc-api-candidate.md`; over `Api.lean`, not proved). `wv.Put(key, value, lease)` (the store's `Put`): a write transaction of the put at the
store's state `σ` (revision `σ`'s next, returned), committed by the caller's updates (the commit's two steps: the
notification, then the bump; through the watchable store when the store has watchers, else both at
the bump). The lessor's item map, the caller's (the lease owner), is the state's (the first update
says so: the store reads it when it attaches the lease, before it commits), and after the commit's.
The hook as in `Write` (the critical-section contract: `Pre` to `Q'` by `hookRun`,
`Q' ={⊤}=∗ P ∗ Post` before the lock is released). -/
abbrev mvcc.writeView.Put.specC : Prop :=
  ∀ (wv : Loc) (γ : mvcc.MvccName) (key value : GoSlice) (k v : GoString) (leaseID : w64)
    (L : List w64) (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (P Pre Q' Post : IProp GF)
    (f : GoFunc) (Q : mvcc.MvccState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isMvccView (interface.mkOk (go.GoType.PointerType writeView.ty) #wv) γ ∗ threadTok ∗ key ↦*□ k ∗ value ↦*□ v ∗
      ⌜(k.length : Int) < 2 ^ 63 - 1⌝ ∗
      lease.leaseOwn (mvcc.mvccLeases γ) L I ∗ ⌜leaseID = W64 0 ∨ leaseID ∈ L⌝ ∗ mvcc.mvccHook γ P f ∗ Pre ∗ mvcc.hookRun P f Pre Q' ∗ (Q' ={⊤}=∗ P ∗ Post) ∗
      AU <{ ∃∃ (σ : mvcc.MvccState), mvcc.mvccState γ σ ∗ ⌜mvcc.pendItems σ.log [] = I⌝ }> @ ⊤ \ ↑mvcc.mvccN, ∅
        <{ mvcc.mvccState γ (σ.notify [.put k v leaseID]), COMM
            AU <{ ∃∃ (σ' : mvcc.MvccState), mvcc.mvccState γ σ' }> @ ⊤ \ ↑mvcc.mvccN, ∅
              <{ mvcc.mvccState γ σ'.commitPending, COMM Q σ }> }> }}
    (App (App (App (Val (wv @!! go.GoType.PointerType writeView.ty @!! go!"Put")) (Val #key))
      (Val #value)) (Val #leaseID))
  {{ (rev : w64), RET #rev; threadTok ∗ Post ∗ ∃ σ : mvcc.MvccState, Q σ ∗
      lease.leaseOwn (mvcc.mvccLeases γ) L (mvcc.pendItems σ.log [.put k v leaseID]) ∗
      ⌜rev = W64 (σ.log.length : Int)⌝ }}

end spec

end EtcdGrove
end Perennial
