/-
**mvcc over etcd's backend** (the design "mvcc's API over its storage abstraction", approved by the
user, 2026-11-06; `notes/mvcc-api-invariants.md`): mvcc's API (`Api.lean`) is stated over its
storage abstraction (`MvccStorage`, `mvccStorageFor`, `storageHook`, `storageReq`, `storageRest`,
`mvccReaderN`); this module makes etcd's backend one storage (`etcdStorage`) and states what is
etcd's backend's: the equations of the abstraction at it, the backend's open (`etcdStorage_open.law`,
with the store's layout `bridgeParams`), the backend data's image of a history (`mvccImage`), the
snapshot (`mvccImage_snapshot.law`: mvcc's code takes none, the server does, on its backend), the
registration of the store's write resource (`mvccW`), the client's rest of an opened backend
(`backendRest`) and the lease bucket's delete inside a write transaction. What the server imports;
inside mvcc's tree because it reads the abstraction's sealed definitions. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__Snapshot
import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.SnapImage

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

/-- **etcd's backend of the real instance `bk`, as a storage.** -/
@[no_expose] def etcdStorage (bk : KBReal) : MvccStorage := bk

theorem etcdStorage_inj {bk bk' : KBReal} (h : etcdStorage bk = etcdStorage bk') : bk = bk' := h

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-! ### The abstraction at etcd's backend -/

theorem etcdStorage_val (bk : KBReal) :
    storageVal (etcdStorage bk) =
      interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
        #bk.be := by rfl

theorem etcdStorage_hook (bk : KBReal) (dq : DFrac) (f : GoFunc) :
    storageHook (GF := GF) (etcdStorage bk) dq f = backend.plHookAt bk.γB dq f := by rfl

theorem etcdStorage_hookIs (bk : KBReal) (f : GoFunc) :
    hookIs (GF := GF) (etcdStorage bk) f = backend.plHookRO bk.γB f := by rfl

theorem etcdStorage_req (bk : KBReal) (Pk X Y : IProp GF) :
    storageReq (etcdStorage bk) Pk X Y = backend.commitReq bk.γB bk.P Pk bk.be X Y := by rfl

theorem etcdStorage_rest (bk : KBReal) :
    storageRest (GF := GF) (etcdStorage bk) =
      iprop([∗list] _x ∈ List.replicate (backend.rdStockN - 2) (), backend.bOpen bk.γB backend.rdOpen) :=
  by rfl

theorem mvccReaderN_eq : mvccReaderN = backend.rdStockN - 5 := by rfl

/-! ### etcd's backend's own vocabulary -/

/-- **The write invariant a store's backend must be opened with**, at the registration name `gx`
(the `W` of `backend.New`/`storage.OpenSnapshotBackend`; sealed: the batch lock's late-bound
resource `lateW gx`, defined at stage 2, M3, 2026-11-05). -/
@[no_expose] def mvccW (gx : GName) : IProp GF := lateW gx

/-- **The right to register a store at `gx`** (exclusive; sealed: `lateReg gx`, defined at stage 2,
M3, 2026-11-05), allocated before the backend is opened (`mvccW_alloc`). -/
@[no_expose] def mvccWReg (gx : GName) : IProp GF := lateReg gx

/-- **The backend data `D` is the image of the history `L` compacted at `c`, recording an unfinished
compaction iff `u`** (the scheduled compaction above the finished one), **and every change of `L` was
made by a step of the program** (round 16, the user: the receipt `⧖ (logCh L)` hidden in this
predicate, traced from the sender's store, `mvccImage_snapshot`, through the server's image
certificate, to the receiver's `etcdStorage_open`; persistent; opaque; on adoption: the image
`keyImage L D` when `c = -1`, else `lean`'s restore image, with the receipt. Formerly the pure
`imageOf`). Its obligations (the review of round
13, `restore`, `kvstore.go:365-423`): when the scheduled compaction is above the finished one, `c`
is the scheduled revision (the restore resumes it, so the Key bucket may be partly compacted); and
`L`'s last revision is the largest of the Key bucket's last revision and the two compaction
revisions. (Defined at stage 2, M2, 2026-11-05: the receipt and the image's facts,
`Api/SnapImage.lean`'s `imageOk`.) -/
@[no_expose] def mvccImage (D : backend.Data) (L : Log) (c : Int) (u : Bool) : IProp GF :=
  iprop(⧖ (logCh L) ∗ ⌜snap.imageOk D L c u⌝)

/-- **What the client keeps of an opened backend** after the store's part: its stop channels, its
hook's exclusive half at `nil` (to set, or to freeze at `nil`), its other buckets' rights (lease,
alarm, auth, membership), the reader pool (`rdPool`), and `K`. (The store's reader slots' open
shares come back at the `Restore` that replaces the backend; not at `Close`, shutdown being out of
scope.) Sealed; its parts by `backendRest_open.law` (the tester's migration, 2026-11-06, G1: until
then opaque at `True`, which left the client no hook to set, no lessor and no `K`). -/
@[no_expose] def backendRest (γB : backend.BNames) (P : backend.BParams) (K : backend.BNames → IProp GF)
    (b : Loc) (D : backend.Data) : IProp GF :=
  iprop(backend.isStopChans γB b ∗ K γB ∗ backend.plHook γB func.nil ∗
    backend.rbOwn γB (backend.rbData P D) ∗ backend.rdPool γB P b)

instance mvccImage_persistent (D : backend.Data) (L : Log) (c : Int) (u : Bool) :
    Persistent (mvccImage (GF := GF) D L c u) := by
  unfold mvccImage; infer_instance

end vocab

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **A registration name**, before the backend is opened, with the store's write invariant the
backend is opened at (`backend.New`'s `W := mvccW gx`; stage 2, 2026-11-05: the registration alone
left the client no `mvccW gx` to open the backend with). -/
abbrev mvccW_alloc.law : Prop := ⊢ |==> ∃ gx : GName, mvccWReg (GF := GF) gx ∗ mvccW gx

/-- **A backend share's backend is open at the store's write invariant** (the server's migration,
2026-11-05: decided by the coordinator, for `lessor.Revoke`'s batch-transaction calls): `B`'s
persistent `isBackend` at `mvccW bk.gx` (the registration name the backend was opened with) and the
batch lock's invariant `Pk`. -/
abbrev mvccBackend_isBackend.law : Prop :=
  ∀ (γ : MvccName) (q : Qp) (bk : KBReal) (Pk : IProp GF),
    mvccBackend (GF := GF) γ q (etcdStorage bk) Pk ⊢ □ backend.isBackend bk.γB bk.P (mvccW bk.gx) Pk bk.be

/-- **What the client keeps of an opened backend, opened** (the tester's migration, 2026-11-06, G1:
decided by the coordinator): `backendRest`'s parts, `newPostKP`'s beyond the store's: the stop
channels, `K`, the hook's exclusive half at `nil` (`SetTxPostLockInsideApplyHook`, or freezing it),
the tracked buckets' rights (`NewLessor`'s `rbPart`) and the reader pool. -/
abbrev backendRest_open.law : Prop :=
  ∀ (γB : backend.BNames) (P : backend.BParams) (K : backend.BNames → IProp GF) (b : Loc)
    (D : backend.Data),
    backendRest (GF := GF) γB P K b D ⊢
      backend.isStopChans γB b ∗ K γB ∗ backend.plHook γB func.nil ∗
        backend.rbOwn γB (backend.rbData P D) ∗ backend.rdPool γB P b

/-- **The store's part of an opened backend** (decision 2, the user, 2026-11-03: over the store's
needs, at any opener; the review of round 13's decisions: at the pooled post): what a backend's
opener returns with its reader slots pooled (`backend.newPostKP`, at whatever the client
keeps, `K`: `backend.New`'s at boot, `K := bFresh`; `storage.OpenSnapshotBackend`'s when applying a
snapshot, `K := snapOpenK`), opened at the store's write invariant `W := mvccW gx` over data `D` that
is the image of the history `L` compacted at `c` (`mvccImage`, with its receipt), with the
registration, and the
store's part of the backend's payment rights, in the backend's own terms: two write-back tokens (for
`NewStore`'s own writes) and the receipt-paid supply every later write-back and the compaction's job
draw on (`□ (⧗ 1 ={⊤}=∗ wbTok)`: on `lean` one stock, shared with the server's own writes, backs
it), and the open shares of the store's counted reader slots (`rdStockN - 2` of `bOpen rdOpen`; the
pool, `rdPool`, stays the client's), gives the store's resources and the client's rest, and two of
the counted slots' tokens (`rdTok`) for the client's own long-lived readers (the server's request,
2026-11-06, decided by the coordinator: its apply thread's writes and its storage-version monitor,
each `rdTok ∗ bOpen rdOpen` with an open share the client keeps). At boot they
come from `bFresh`; the snapshot path supplies them from where its proof holds them. `keySized` (fewer than `2 ^ 62` keys) stays an assumption,
as today. (The design "mvcc's API over its storage abstraction", approved by the user,
2026-11-06: in place of the API's `mvccBackendFor_open.law`, here, at a real instance `bk` in
compaction mode whose configuration has mvcc's layout, `bridgeParams bk.P`, which the server
holds.) -/
abbrev etcdStorage_open.law : Prop :=
  ∀ (bk : KBReal) (Pk K : backend.BNames → IProp GF) (D : backend.Data) (L : Log) (c : Int) (u : Bool),
  bridgeParams bk.P → leaseParams bk.P → bk.cm = true →
  □ (∀ γ b', keySized (GF := GF) γ bk.P b') ∗ mvccImage D L c u ∗
    backend.newPostKP bk.γB bk.P (fun _ => mvccW bk.gx) Pk K bk.be D ∗ mvccWReg bk.gx ∗
    backend.wbTok bk.γB ∗ backend.wbTok bk.γB ∗ □ (⧗ 1 ={⊤}=∗ backend.wbTok bk.γB) ∗
    ([∗list] _x ∈ List.replicate (backend.rdStockN - 2) (), backend.bOpen bk.γB backend.rdOpen) ={⊤}=∗
    mvccStorageFor (etcdStorage bk) (Pk bk.γB) L c u ∗ backendRest bk.γB bk.P K bk.be D ∗
    backend.rdTok bk.γB bk.P bk.be ∗ backend.rdTok bk.γB bk.P bk.be

/-- **A fresh backend's data is the image of the empty history** (round 16: `New`'s and
`NewStore`'s backend, `etcdStorage_open` at `mvccStart`): no change, so the receipt `⧖ 0`,
which Perennial allocates under an update (`preceipt_zero`; the review of round 16, F3). -/
abbrev mvccImage_fresh.law : Prop :=
  ∀ D : backend.Data, (∀ k, backend.dget D mvcc.keyName k = none) →
    backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName mvcc.schedKeyBytes = none →
    backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName mvcc.finKeyBytes = none →
    ⊢ |==> mvccImage (GF := GF) D mvccStart.log mvccStart.crev false


/-- **The lease bucket's delete inside a write transaction** (round 14, A5: `lessor.Revoke` deletes
the lease's record on the backend's batch transaction between the range deleter's `Write` and the
transaction's `End`, so that the keys' deletes and the lease's commit together): while the write
transaction is open (it holds the batch lock), an `UnsafeDelete` of the Lease bucket on the
backend's batch transaction, over the bucket rights the client owns (`backend.rbPart`, the
lessor's), leaves the store's backend as it was and the transaction able only to end (the
backend's batch session admits only `Unlock` after an `UnsafeDelete`, and the delete forces a commit
at `End`: the review of round 14): what comes back is `End` for the transaction, as
`Txn.End.contract` states it at a write view, **once** (2026-11-06: a one-shot wand, until then a
Hoare triple, which is persistent: it would let `End` run twice on one transaction, whose second
`Unlock` of the batch lock panics, so the law was false; `lessor.Revoke` calls it once). -/
abbrev mvccTxn_leaseDelete.law : Prop :=
  ∀ (tw : GoInterfaceOk) γ trace σ pend (q : Qp) (bk : KBReal) (Pk : IProp GF) (t : Loc)
    (b : GoInterface) (key : GoSlice) (k : GoString) (dq : DFrac) (S : GoString → Prop)
    (r : GMap GoString backend.BktData) (Φ : val → IProp GF),
  S leaseName →
  mvccTxn (GF := GF) (GoInterface.ok tw) γ trace (.write σ pend) ∗ mvccBackend γ q (etcdStorage bk) Pk ∗
    backend.bF go!"batchTx" bk.be ↦□ t ∗
    globalAddr go_etcd_io.etcd.server.v3.storage.schema.Lease ↦□ b ∗ key ↦*{dq} k ∗
    backend.rbPart bk.γB S r ∗
    ▷ (mvccBackend γ q (etcdStorage bk) Pk -∗ key ↦*{dq} k -∗ backend.rbPart bk.γB S (rbDel r leaseName k) -∗
        (∀ (Q : IProp GF) (Ψ : val → IProp GF),
          isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
              mvccBackend γ q (etcdStorage bk) Pk ∗ Pk ∗
              AU <{ ∃∃ (σ1 : MvccState), mvccState γ σ1 }> @ ⊤ \ ↑mvccN, ∅
                <{ ⌜σ1 = σ⌝ ∗ mvccState γ (σ1.notify pend) ∗ ⧖ (logCh (σ1.log ++ [pend])), COMM
                    AU <{ ∃∃ (σ2 : MvccState), mvccState γ σ2 }> @ ⊤ \ ↑mvccN, ∅
                      <{ ⌜σ2 = σ.notify pend⌝ ∗ mvccState γ σ2.commitPending, COMM Q }> }> -∗
            ▷ (threadTok ∗ mvccBackend γ q (etcdStorage bk) Pk ∗ Q -∗ Ψ #()) -∗
            WP (App (Val #(methods tw.ty go!"End" tw.v)) (Val #())) {{ Ψ }}) -∗ Φ #()) ⊢
  WP (App (App (Val #(methods (go.GoType.PointerType
      go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty) go!"UnsafeDelete" #t))
      (Val #b)) (Val #key)) {{ Φ }}

end laws

section snapshot
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [bk_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **A snapshot of the store's backend is the image of the store's history** (round 16, G3: the
sender's side of `mvccImage`, `createMergedSnapshotMessage`'s `s.be.Snapshot()`; derived from
`backend.Snapshot`'s triple). With the whole backend share held through the call (no step that
changes the history runs: each takes a share), by the caller's update at the state (nothing
pending; the state unchanged), the snapshot's data `D` is the image of that state's history and
compaction, with the store's receipt inside (`mvccImage`), recording an unfinished compaction iff
`u`; and the caller's own observation `Q` of the backend's hook keys `d` and tracked buckets `r`,
from its `R` and the batch lock's invariant `Pk`, as `backend.Snapshot`'s. Not a pin predicate (the
server draft's proposal): the update at the state is the API's one shape for reading it.

**A compacted store too** (the user's decision, 2026-11-04, on the review of round 16's F1):
`backend.Snapshot`'s observation is handed the compaction keys' committed values (`fkdOwn`, the
client's half inside `fkOwn`, which the store's compaction keeps), so the image's compaction
revisions and `u` are the store's. -/
abbrev mvccImage_snapshot.law : Prop :=
  backend.backend.Snapshot.spec (GF := GF) (hG := hG) →
  ∀ (kv : GoInterface) (γ : MvccName) (bk : KBReal) (Pk : IProp GF) (qo : Qp) (R : IProp GF)
    (Q : GMap (GoString × GoString) GoString → GMap GoString backend.BktData → Prop)
    (Φ : MvccState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isMvcc kv γ ∗ mvccBackend γ 1 (etcdStorage bk) Pk ∗ backend.bOpen bk.γB qo ∗ backend.wbTok bk.γB ∗ R ∗
      □ (∀ (d : GMap (GoString × GoString) GoString) (r : GMap GoString backend.BktData),
        R -∗ Pk -∗ backend.hkOwn bk.γB d -∗ backend.rbOwn bk.γB r -∗ ⌜Q d r⌝) ∗
      AU <{ ∃∃ (σ : MvccState), mvccState γ σ ∗ ⌜σ.pending = none⌝ }>
        @ ⊤ \ ↑mvccN, ∅ <{ mvccState γ σ, COMM Φ σ }> }}
    (App (Val (bk.be @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty
      @!! go!"Snapshot")) (Val #()))
  {{ (sp : Loc) (D : backend.Data),
      RET #(interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.snapshot.ty) #sp);
      backend.snapOpen sp D ∗ backend.bOpen bk.γB qo ∗ R ∗ mvccBackend γ 1 (etcdStorage bk) Pk ∗
      ⌜Q (backend.hkData bk.P D) (backend.rbData bk.P D)⌝ ∗
      ∃ (σ : MvccState) (u : Bool), Φ σ ∗ mvccImage D σ.log σ.crev u }}

end snapshot


end api
end mvcc
end EtcdGrove
end Perennial
