/- Lean-first (no Rocq counterpart).

# The server's WAL after a crash: `srvFilesC` and `walReadFacts` (etcd-dist D6, task T5)

`notes/etcd-dist-d6.md` §2 (the rows "`srvFiles` from the crash frame", "`walReadFacts σ` of a crash
image") and §6 (T5); `notes/wal-p8-handoff.md`. What a crashed member's data directory gives the
restart's `bootstrap` (`bootstrapCrashContract`, `InvCrashImage.lean` on the D6 branches) of its WAL:

* **the files** (`srvFilesC`): `srvFiles` (`InvRestart.lean`) with the WAL's files as a crash leaves them
  (`walFilesC`, `storage/WalRecsCrash.lean`: no synced mark; see that file's header for why). The
  graceful image's files are an instance (`srvFiles_srvFilesC`). **Proposed** for the crash image
  (`srvCrashImageAt`) and `bootstrapCrashContract`'s pre in place of `srvFiles`; made by
  `walFilesC_crash` from the WAL's crash (`walCrashWal`, whose relation is `walStCrashS` since P8) and the backend's
  (interim axiom A1);
* **the read facts** (`walReadFacts σ`, `WalApi.lean`'s I1-I4) of what the restart reads, `σ = walRead I`
  for the crash image `I` (a prefix of the WAL's history): `walReadFacts_of_read`, from two conditions on
  the history that pass to prefixes (`walIdxLe`, `walCommitLe`: `storage/WalCrashRead.lean`), which the
  server's durability invariant must keep along its `Save`s.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRestart
public import Proof.go_etcd_io.etcd.server.v3.storage.WalRecsCrash
public import Proof.go_etcd_io.etcd.server.v3.storage.WalCrashRead

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

/-! ## The read facts of a crash image -/

section facts
variable [GooseExts]

/-- **What a restart reads meets I1-I4** (`walReadFacts`): a read `walRead I = some σ` of a history
whose indexes are within raft's room (`walIdxLe (2^61 - 1) I`) and whose read's fold never has its commit
above its last index (`walCommitLe I`). -/
theorem walReadFacts_of_read {I : WalHist} {σ : StorContents} (h : walRead I = some σ)
    (hB : walIdxLe (2 ^ 61 - 1) I) (hc : walCommitLe I) : walReadFacts σ :=
  ⟨walRead_wf h, walRead_last_le hB h, walRead_b_le_commit h, walRead_commit_le_last hc h,
    walRead_snapBase h⟩

/-- **… of a crash image `H.take j`**, from the conditions kept of the whole history `H`: the indexes
bounded, and raft's `committed ≤ lastIndex` along the eager fold, whose state at the prefix has its
base at or below its commit. -/
theorem walReadFacts_of_take {H : WalHist} {j : Nat} {σ τ : StorContents}
    (h : walRead (H.take j) = some σ) (hB : walIdxLe (2 ^ 61 - 1) H)
    (hc : walCommitLeFrom walFresh H) (hf : walFoldChkFrom walFresh (H.take j) = some τ)
    (hb : τ.b ≤ τ.commit) : walReadFacts σ :=
  walReadFacts_of_read h (walIdxLe_take hB j) (walCommitLe_take hc hf hb)

end facts

/-! ## The files of a crashed member's data directory -/

section files
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The files of a crashed member's data directory hold `σ` and `D`** (`srvFiles` with the WAL's
files as a crash leaves them, `walFilesC`; see the file header). -/
def srvFilesC (dd : GoString) (id : w64) (σ : StorContents) (D : backend.Data) : IProp GF :=
  iprop((∃ (a : WalA GF) (cid : w64), ⌜a.dir = srvWalDirOf dd⌝ ∗ walFilesC a id cid σ true) ∗
    backend.fileHolds (config.backendPathOf dd) D)

/-- **A stopped member's files are files a crash may leave.** -/
theorem srvFiles_srvFilesC (dd : GoString) (id : w64) (σ : StorContents) (D : backend.Data) :
    srvFiles (GF := GF) dd id σ D ⊢ srvFilesC dd id σ D := by
  unfold srvFiles srvFilesC
  iintro ⟨⟨%a, %cid, %ha, Hw⟩, Hb⟩
  iframe Hb
  iexists a, cid
  isplitr
  · ipureintro; exact ha
  iapply walFiles_walFilesC
  iexact Hw

/-- **The data directory of a crashed member's files is shorter than `2^60` bytes**
(`srvFiles_dataDir_len`'s). -/
theorem srvFilesC_dataDir_len (dd : GoString) (id : w64) (σ : StorContents) (D : backend.Data) :
    srvFilesC (GF := GF) dd id σ D ⊢ ⌜dd.length < 2 ^ 60⌝ ∗ srvFilesC dd id σ D := by
  unfold srvFilesC
  iintro ⟨⟨%a, %cid, %ha, Hw⟩, Hb⟩
  have hf := a.fits
  rw [ha] at hf
  have hl : (srvWalDirOf dd).length < 3800 := hf.1
  simp only [srvWalDirOf, walAreaOf, List.length_append, List.length_drop] at hl
  have hdb : dataBase.length = 20 := by decide
  isplitr
  · ipureintro; omega
  iframe Hb
  iexists a, cid
  iframe Hw
  ipureintro; exact ha

end files

end EtcdGrove
end Perennial
