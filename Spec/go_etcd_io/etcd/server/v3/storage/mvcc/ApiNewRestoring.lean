/-
**DRAFT (B3, mvccfull's F1): `mvcc.New`/`mvcc.NewStore` on a storage that already holds a
history.** Candidate restatements of the API's `New.spec`/`NewStore.spec` (`Api.lean`), from the
empty history `mvccStart` to any image `mvccStorageFor B Pk σ.log σ.crev u`, as
`KV.Restore.contract` takes it (Go: `NewStore` runs the same `s.restore()` as `store.Restore`,
`kvstore.go:127-132`). Scratch: not imported, not linked, not proved.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

local notation "pkgInit" => isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc
local notation "PS" => go.GoType.PointerType store.ty
local notation "PW" => go.GoType.PointerType watchableStore.ty

/-- **The resumed compaction's resources** (`New`'s, `NewStore`'s): when the image records an
unfinished compaction (`u`), `restore()` resumes it (`compactLockfree`): under the storage's batch
lock its post-lock hook `f` at the share `dq` runs once (`Pre` to `Q'`, giving `Pk` back), and the
storage commits once (`X` to `Y`); as `KV.Restore.contract`'s, at the storage the store is made
over. Otherwise nothing. -/
def newResumePre (B : MvccStorage) (Pk : IProp GF) (u : Bool) (dq : DFrac) (f : GoFunc)
    (Pre Q' Post X Y : IProp GF) : IProp GF :=
  if u then
    iprop(storageHook B dq f ∗ ⌜f = func.nil ∨ dq = DFrac.discard⌝ ∗
      Pre ∗ hookRun Pk f Pre Q' ∗ (Q' ={⊤}=∗ Pk ∗ Post) ∗ X ∗ storageReq B Pk X Y)
  else iprop(True)

/-- What the resumed compaction gives back: the hook's share, `Post` and `Y`. -/
def newResumePost (B : MvccStorage) (u : Bool) (dq : DFrac) (f : GoFunc) (Post Y : IProp GF) :
    IProp GF :=
  if u then iprop(storageHook B dq f ∗ Post ∗ Y) else iprop(True)

/-- **`mvcc.New(lg, be, le, cfg)`** over a storage `B` holding the history `σ.log` compacted at
`σ.crev`, recording an unfinished compaction iff `u` (`mvccStorageFor`, from the storage's
provider: `etcdStorage_open.law` at an image, a fresh file's `mvccImage_fresh.law` or a stopped
store's `mvccImage_stop.law`): the watchable store at the state `σ` (nothing pending, reachable),
with the open token, the whole backend share, the reader tokens and the range deleter, as at a fresh
storage; the lessor's items re-attached (each restored key with a lease attached through the lessor,
`restore()`'s `Attach`, from the owner's part at the live leases `Ls`, each restored item's lease
among them and its key short; the owner's map becomes `pendItems σ.log []`); a resumed compaction
(`u`) as `Restore`'s (`newResumePre`). At `σ = mvccStart`, `u = false`: today's `New.spec`, with the
lessor's owner part (at any `Ls`, the empty map) lent and given back unchanged
(`pendItems mvccStart.log [] = ∅`). -/
abbrev New.specR : Prop :=
  ∀ [ReceiptBoundLe GF (2 ^ 48)] (lg : Loc) (le : GoInterface) (cfg : StoreConfig) (B : MvccStorage)
    (Pk : IProp GF) (γl : GName) (rd0 : GoFunc) (σ : MvccState) (u : Bool) (Ls : List w64)
    (dq : DFrac) (f : GoFunc) (Pre Q' Post X Y : IProp GF),
  batchLimitOk cfg.CompactionBatchLimit' → MvccReachable σ → σ.pending = none →
  {{ pkgInit ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      mvccStorageFor B Pk σ.log σ.crev u ∗
      lease.lessorRdOf γl ∗ isLessor le γl ∗ lease.rdOwn γl rd0 ∗
      lease.leaseOwn γl Ls ∅ ∗
      ⌜∀ it lid, (pendItems σ.log []).lookup it = some lid →
        lid ∈ Ls ∧ (it.Key'.length : Int) < 2 ^ 63 - 1⌝ ∗
      newResumePre B Pk u dq f Pre Q' Post X Y }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.New)) (Val #lg))
      (Val #(storageVal B)))
      (Val #le)) (Val #cfg))
  {{ (ws : Loc), RET #(interface.mkOk PW #ws);
      ∃ γ : MvccName, ⌜mvccLeases γ = γl⌝ ∗
        isMvcc (interface.mkOk PW #ws) γ ∗ mvccState γ σ ∗ mvccOpen γ ∗
        mvccBackend γ 1 B Pk ∗ mvccReaders γ mvccReaderN ∗
        (∃ rd : GoFunc, lease.rdOwn γl rd ∗ mvccDeleter rd γ) ∗
        lease.leaseOwn γl Ls (pendItems σ.log []) ∗
        newResumePost B u dq f Post Y }}

/-- **`mvcc.NewStore(lg, be, le, cfg)`**: as `New.specR`, a store without watchers. -/
abbrev NewStore.specR : Prop :=
  ∀ [ReceiptBoundLe GF (2 ^ 48)] (lg : Loc) (le : GoInterface) (cfg : StoreConfig) (B : MvccStorage)
    (Pk : IProp GF) (γl : GName) (rd0 : GoFunc) (σ : MvccState) (u : Bool) (Ls : List w64)
    (dq : DFrac) (f : GoFunc) (Pre Q' Post X Y : IProp GF),
  batchLimitOk cfg.CompactionBatchLimit' → MvccReachable σ → σ.pending = none →
  {{ pkgInit ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      mvccStorageFor B Pk σ.log σ.crev u ∗
      lease.lessorRdOf γl ∗ isLessor le γl ∗ lease.rdOwn γl rd0 ∗
      lease.leaseOwn γl Ls ∅ ∗
      ⌜∀ it lid, (pendItems σ.log []).lookup it = some lid →
        lid ∈ Ls ∧ (it.Key'.length : Int) < 2 ^ 63 - 1⌝ ∗
      newResumePre B Pk u dq f Pre Q' Post X Y }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.NewStore)) (Val #lg))
      (Val #(storageVal B)))
      (Val #le)) (Val #cfg))
  {{ (s : Loc), RET #s;
      ∃ γ : MvccName, ⌜mvccLeases γ = γl⌝ ∗
        isMvcc (interface.mkOk PS #s) γ ∗ mvccState γ σ ∗ mvccOpen γ ∗
        mvccBackend γ 1 B Pk ∗ mvccReaders γ mvccReaderN ∗
        (∃ rd : GoFunc, lease.rdOwn γl rd ∗ mvccDeleter rd γ) ∗
        lease.leaseOwn γl Ls (pendItems σ.log []) ∗
        newResumePost B u dq f Post Y }}

/-- The fresh instance's pure side conditions: the empty history attaches no lease item, and its
state has nothing pending. -/
-- (`pendItems mvccStart.log [] = ∅`: mvccrand's `pendItems_start`, `RunChecksWriter.lean:32`.)
example : mvccStart.pending = none := rfl
example : MvccReachable mvccStart := .start

end specs

end api
end mvcc
end EtcdGrove
end Perennial
