/-
**DRAFT (B3, mvccfull's F1): `mvcc.New`/`mvcc.NewStore` on a storage that already holds a
history.** Candidate restatements of the API's `New.spec`/`NewStore.spec` (`Api.lean`), from the
empty history `mvccStart` to any image `mvccStorageFor B Pk σ.log σ.crev u`, as
`KV.Restore.contract` takes it (Go: `NewStore` runs the same `s.restore()` as `store.Restore`,
`kvstore.go:127-132`). Imported by the tester (`examples/mvccfull`'s `Writer.lean`), linked as a
hypothesis (`ApiNewRestoring+R: ?`); the corollaries below are proved, `specR` is not (its proof
from the internal candidate, `NewR.lean`'s `api.New.specR_of_internal`, waits on R1).

**Repair round 1** (`notes/review/mvccfull-f1-api-r1.md`): the pure premises inside the triples
(F1.2); the resumed compaction's resources inline, as `Restore`'s (F1.3: no `newResumePre`/`Post`);
the post's receipt `⧖ (logCh σ.log)` (F1.4: `Restore`'s update is given it; here the client cannot
get it otherwise, `mvccStorageFor` and `mvccImage` being sealed; provable: `mvccStorageFor` holds
it, persistent); today's specs as corollaries with the lessor's owner part lent (F1.1,
`New.spec_of_specR`, `NewStore.spec_of_specR`).

**The exported statements that change when `specR` replaces `New.spec`/`NewStore.spec`** (the
Freeze list): the corollaries take `lease.leaseOwn γl [] ∅` in the pre and give it back, so the
results stated over today's specs gain it in pre and post:
- etcdserver `Results.lean`: `server_kv_backend` (l.914), `server_kv_watchable` (l.973),
  `server_kv_backend_hooks` (l.1103);
- mvcc `ApiResults.lean`: `mvccApi_New_wp_proof`, `mvccApi_NewStore_wp_proof` (l.103-108),
  re-stated as `specR`'s (or the corollaries');
- callers' proofs (one line each, lending the part they hold): `NewServer.lean` l.845 (holds
  `Hlown` from l.724 to l.2599), mvccrand's `runChecks.lean` l.172.
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

/-- **`mvcc.New(lg, be, le, cfg)`** over a storage `B` holding the history `σ.log` compacted at
`σ.crev`, recording an unfinished compaction iff `u` (`mvccStorageFor`, from the storage's
provider: `etcdStorage_open.law` at an image, a fresh file's `mvccImage_fresh.law` or a stopped
store's `mvccImage_stop.law`): the watchable store at the state `σ` (nothing pending, reachable),
with the open token, the whole backend share, the reader tokens and the range deleter, as at a fresh
storage; the lessor's items re-attached (each restored key with a lease attached through the lessor,
`restore()`'s `Attach`, from the owner's part at the live leases `Ls`, each restored item's lease
among them and its key short; the owner's map becomes `pendItems σ.log []`); the restored history's
receipt `⧖ (logCh σ.log)` (`mvccStorageFor`'s, as `Restore` gives it to its update); when the image
records an unfinished compaction (`u`), `restore()` resumes it (`compactLockfree`), as `Restore`
does: under the storage's batch lock its post-lock hook `f` at the share `dq` runs once (`Pre` to
`Q'`, giving `Pk` back) and the storage commits once (`X` to `Y`), the hook's share, `Post` and `Y`
given back; otherwise nothing is asked or given. At `σ = mvccStart`, `u = false`: today's
`New.spec`, with the lessor's owner part at `[]` lent and given back (`New.spec_of_specR`). -/
abbrev New.specR : Prop :=
  ∀ [ReceiptBoundLe GF (2 ^ 48)] (lg : Loc) (le : GoInterface) (cfg : StoreConfig) (B : MvccStorage)
    (Pk : IProp GF) (γl : GName) (rd0 : GoFunc) (σ : MvccState) (u : Bool) (Ls : List w64)
    (dq : DFrac) (f : GoFunc) (Pre Q' Post X Y : IProp GF),
  {{ pkgInit ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      mvccStorageFor B Pk σ.log σ.crev u ∗
      ⌜batchLimitOk cfg.CompactionBatchLimit' ∧ MvccReachable σ ∧ σ.pending = none⌝ ∗
      lease.lessorRdOf γl ∗ isLessor le γl ∗ lease.rdOwn γl rd0 ∗
      lease.leaseOwn γl Ls ∅ ∗
      ⌜∀ it lid, (pendItems σ.log []).lookup it = some lid →
        lid ∈ Ls ∧ (it.Key'.length : Int) < 2 ^ 63 - 1⌝ ∗
      (if u then iprop(storageHook B dq f ∗ ⌜f = func.nil ∨ dq = DFrac.discard⌝ ∗
        Pre ∗ hookRun Pk f Pre Q' ∗ (Q' ={⊤}=∗ Pk ∗ Post) ∗ X ∗ storageReq B Pk X Y)
       else iprop(True)) }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.New)) (Val #lg))
      (Val #(storageVal B)))
      (Val #le)) (Val #cfg))
  {{ (ws : Loc), RET #(interface.mkOk PW #ws);
      ∃ γ : MvccName, ⌜mvccLeases γ = γl⌝ ∗
        isMvcc (interface.mkOk PW #ws) γ ∗ mvccState γ σ ∗ mvccOpen γ ∗
        mvccBackend γ 1 B Pk ∗ mvccReaders γ mvccReaderN ∗
        (∃ rd : GoFunc, lease.rdOwn γl rd ∗ mvccDeleter rd γ) ∗
        lease.leaseOwn γl Ls (pendItems σ.log []) ∗ ⧖ (logCh σ.log) ∗
        (if u then iprop(storageHook B dq f ∗ Post ∗ Y) else iprop(True)) }}

/-- **`mvcc.NewStore(lg, be, le, cfg)`**: as `New.specR`, a store without watchers. -/
abbrev NewStore.specR : Prop :=
  ∀ [ReceiptBoundLe GF (2 ^ 48)] (lg : Loc) (le : GoInterface) (cfg : StoreConfig) (B : MvccStorage)
    (Pk : IProp GF) (γl : GName) (rd0 : GoFunc) (σ : MvccState) (u : Bool) (Ls : List w64)
    (dq : DFrac) (f : GoFunc) (Pre Q' Post X Y : IProp GF),
  {{ pkgInit ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      mvccStorageFor B Pk σ.log σ.crev u ∗
      ⌜batchLimitOk cfg.CompactionBatchLimit' ∧ MvccReachable σ ∧ σ.pending = none⌝ ∗
      lease.lessorRdOf γl ∗ isLessor le γl ∗ lease.rdOwn γl rd0 ∗
      lease.leaseOwn γl Ls ∅ ∗
      ⌜∀ it lid, (pendItems σ.log []).lookup it = some lid →
        lid ∈ Ls ∧ (it.Key'.length : Int) < 2 ^ 63 - 1⌝ ∗
      (if u then iprop(storageHook B dq f ∗ ⌜f = func.nil ∨ dq = DFrac.discard⌝ ∗
        Pre ∗ hookRun Pk f Pre Q' ∗ (Q' ={⊤}=∗ Pk ∗ Post) ∗ X ∗ storageReq B Pk X Y)
       else iprop(True)) }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.NewStore)) (Val #lg))
      (Val #(storageVal B)))
      (Val #le)) (Val #cfg))
  {{ (s : Loc), RET #s;
      ∃ γ : MvccName, ⌜mvccLeases γ = γl⌝ ∗
        isMvcc (interface.mkOk PS #s) γ ∗ mvccState γ σ ∗ mvccOpen γ ∗
        mvccBackend γ 1 B Pk ∗ mvccReaders γ mvccReaderN ∗
        (∃ rd : GoFunc, lease.rdOwn γl rd ∗ mvccDeleter rd γ) ∗
        lease.leaseOwn γl Ls (pendItems σ.log []) ∗ ⧖ (logCh σ.log) ∗
        (if u then iprop(storageHook B dq f ∗ Post ∗ Y) else iprop(True)) }}

/-- The empty history attaches no lease item (mvccrand's `pendItems_start`). -/
theorem pendItems_mvccStart : pendItems mvccStart.log [] = ∅ := by
  rw [pendItems_nil]
  exact GMap.ext (fun _ => rfl)

/-- **Today's `New.spec` from the candidate, with the lessor's owner part lent** (review round 1's
F1.1): the instance at `σ = mvccStart`, `u = false`, `Ls = []`; the pre and post of `New.spec`
with `lease.leaseOwn γl [] ∅` added to both (`pendItems mvccStart.log [] = ∅`), the receipt
(`⧖ 0`) dropped. Not `New.spec` itself: `specR` re-attaches the restored items through the owner's
part, so it takes it even when there is none. Every caller holds it: the server from
`NewLessor`'s post (`NewServer.lean`'s `Hlown`, held from l.724 across the call at l.845), mvccrand
likewise (`runChecks.lean` l.172), the tester from `NewLessor.specR`'s (`leaseOwn γl Lr ∅`). -/
theorem New.spec_of_specR (h : New.specR (GF := GF) (hG := hG)) [ReceiptBoundLe GF (2 ^ 48)]
    (lg : Loc) (le : GoInterface) (cfg : StoreConfig) (B : MvccStorage) (Pk : IProp GF)
    (γl : GName) (rd0 : GoFunc) (hcfg : batchLimitOk cfg.CompactionBatchLimit') :
  {{ pkgInit ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      mvccStorageFor B Pk mvccStart.log mvccStart.crev false ∗
      lease.lessorRdOf γl ∗ isLessor le γl ∗ lease.rdOwn γl rd0 ∗ lease.leaseOwn γl [] ∅ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.New)) (Val #lg))
      (Val #(storageVal B)))
      (Val #le)) (Val #cfg))
  {{ (ws : Loc), RET #(interface.mkOk PW #ws);
      ∃ γ : MvccName, ⌜mvccLeases γ = γl⌝ ∗
        isMvcc (interface.mkOk PW #ws) γ ∗ mvccState γ mvccStart ∗ mvccOpen γ ∗
        mvccBackend γ 1 B Pk ∗ mvccReaders γ mvccReaderN ∗
        (∃ rd : GoFunc, lease.rdOwn γl rd ∗ mvccDeleter rd γ) ∗ lease.leaseOwn γl [] ∅ }} := by
  iintro %Φ ⟨Hpkg, Hbe, Hsch, Hst, Hrd, Hle, Hrd0, Hown⟩ HΦ
  iapply (h lg le cfg B Pk γl rd0 mvccStart false [] (DFrac.own 1) func.nil
    iprop(True) iprop(True) iprop(True) iprop(True) iprop(True)) $$
    [Hpkg Hbe Hsch Hst Hrd Hle Hrd0 Hown]
  · iframe
    isplitr
    · ipureintro; exact ⟨hcfg, .start, rfl⟩
    isplitr
    · ipureintro; intro it lid hl; rw [pendItems_mvccStart] at hl; cases hl
    simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  iintro !> %ws ⟨%γ, %Hγ, Hmv, Hst, Ho, Hb, Hrs, Hdel, Hown, -, -⟩
  iapply HΦ
  rw [pendItems_mvccStart]
  iexists γ
  iframe
  ipureintro; exact Hγ

/-- **Today's `NewStore.spec` from the candidate, with the lessor's owner part lent**: as
`New.spec_of_specR`. -/
theorem NewStore.spec_of_specR (h : NewStore.specR (GF := GF) (hG := hG))
    [ReceiptBoundLe GF (2 ^ 48)]
    (lg : Loc) (le : GoInterface) (cfg : StoreConfig) (B : MvccStorage) (Pk : IProp GF)
    (γl : GName) (rd0 : GoFunc) (hcfg : batchLimitOk cfg.CompactionBatchLimit') :
  {{ pkgInit ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      mvccStorageFor B Pk mvccStart.log mvccStart.crev false ∗
      lease.lessorRdOf γl ∗ isLessor le γl ∗ lease.rdOwn γl rd0 ∗ lease.leaseOwn γl [] ∅ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.NewStore)) (Val #lg))
      (Val #(storageVal B)))
      (Val #le)) (Val #cfg))
  {{ (s : Loc), RET #s;
      ∃ γ : MvccName, ⌜mvccLeases γ = γl⌝ ∗
        isMvcc (interface.mkOk PS #s) γ ∗ mvccState γ mvccStart ∗ mvccOpen γ ∗
        mvccBackend γ 1 B Pk ∗ mvccReaders γ mvccReaderN ∗
        (∃ rd : GoFunc, lease.rdOwn γl rd ∗ mvccDeleter rd γ) ∗ lease.leaseOwn γl [] ∅ }} := by
  iintro %Φ ⟨Hpkg, Hbe, Hsch, Hst, Hrd, Hle, Hrd0, Hown⟩ HΦ
  iapply (h lg le cfg B Pk γl rd0 mvccStart false [] (DFrac.own 1) func.nil
    iprop(True) iprop(True) iprop(True) iprop(True) iprop(True)) $$
    [Hpkg Hbe Hsch Hst Hrd Hle Hrd0 Hown]
  · iframe
    isplitr
    · ipureintro; exact ⟨hcfg, .start, rfl⟩
    isplitr
    · ipureintro; intro it lid hl; rw [pendItems_mvccStart] at hl; cases hl
    simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  iintro !> %s ⟨%γ, %Hγ, Hmv, Hst, Ho, Hb, Hrs, Hdel, Hown, -, -⟩
  iapply HΦ
  rw [pendItems_mvccStart]
  iexists γ
  iframe
  ipureintro; exact Hγ

end specs

end api
end mvcc
end EtcdGrove
end Perennial
