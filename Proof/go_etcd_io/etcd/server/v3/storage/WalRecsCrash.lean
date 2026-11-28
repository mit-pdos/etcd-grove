/- Lean-first (no Rocq counterpart).

# The WAL's files after a crash (etcd-dist D6, task T5)

`notes/etcd-dist-d6.md` §2 (the row "`srvFiles` from the crash frame") and §6 (T5);
`notes/wal-p8-handoff.md`. A member machine that crashes restarts `NewServer` on its data directory,
whose WAL `bootstrap` opens and reads. The graceful restart takes the closed WAL's files
`walFiles a id cid σ true` (`WalRecs.lean`, what `WAL.Close` leaves); after a crash this module makes
the same files from the WAL's crash (`walCrashWal` over `walStCrashS`, `wal/CrashS.lean`), with one difference:

**`walFilesC`, the files a crash left** (`walFiles` without its synced mark `walSyncedLb a.dir |H|`).
A crash keeps the abstract state's synced mark (`walCrash`: `m` unchanged, `{d with H := I, ..}`), so
the new generation's state is synced up to the old mark only, although every byte on disk is durable
(the crash's `fileStart`). Raising the mark at boot is a ghost step of the WAL's invariant that no
lemma provides yet (`notes/wal-p8-handoff.md`, "The synced mark after a crash"); nothing on the
restart path needs it: `ReadAll` in write mode syncs and returns the mark (`WAL__ReadAll`'s post), and
`Open`/`ReadAll` take no mark. The graceful files give the crash ones (`walFiles_walFilesC`), so a
contract stated over `walFilesC` covers both.

**`walFilesC_crash`**: from the crash view, the old generation's `walDiskAt` at the WAL's directory
(given back), its synced mark `n` and name, and the new generation's lock token and the directory's
call permission's half (what the program's boot holds): a position `j` with `n ≤ j ≤ |H|` such that
the files hold whatever the prefix `H.take j` reads as (`walRead`), as `walFilesC` of the same area at
the new generation's WAL names. Whether the read succeeds is the caller's (the server's durability
invariant says what every prefix from the synced mark reads as: T2's `CrashReadsHold`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.WalRecs
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CrashS
import all Proof.go_etcd_io.etcd.server.v3.storage.WalRecs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section pure
variable [GooseExts]

theorem walSrvHist_take_eq (H : List (WalOpG WalEnt)) (j : Nat) :
    walSrvHist (H.take j) = (walSrvHist H).take j := by
  unfold walSrvHist; rw [List.map_take, List.map_take]

theorem walEntsSized_take {H : List (WalOpG WalEnt)} (h : walEntsSized H) (j : Nat) :
    walEntsSized (H.take j) := by
  intro hs es ho
  rw [List.map_take] at ho
  exact h hs es (List.mem_of_mem_take ho)

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- **The files of the WAL in the area and directory `a`, as a crash left them, hold the records `σ`,
its metadata the member `id` of the cluster `cid`** (exclusive, timeless): `walFiles` without the
synced mark (see the file header): the durable state `d`, its name durable, the generation's lock
free, the call permission's half of the directory, what a restart reads from it `σ` (`walRead`), its
metadata, `sized` as `walFiles`'. -/
@[no_expose] def walFilesC (a : WalA GF) (id cid : w64) (σ : StorContents) (sized : Bool := false) :
    IProp GF :=
  letI := a.ext; letI := a.semOk; letI := a.has; letI := a.W
  iprop(∃ (i : Nat) (d : WalDur), WalFs.walDiskAtI a.dir i d ∗ WalFs.walNamed a.dir i ∗
    WalFs.walUnlockedTok ∗ Fs.osCallPerm (Fs.callKey a.R a.dir) (1 : Qp).half ∗
    ⌜walRead (walSrvHist d.H) = some σ ∧ d.metadata = walMetaEnc id cid ∧ d.sized = true ∧
      (sized = true → walEntsSized d.H)⌝)

instance walFilesC_timeless (a : WalA GF) (id cid : w64) (σ : StorContents) (sized : Bool) :
    Timeless (walFilesC (GF := GF) a id cid σ sized) := by
  unfold walFilesC; infer_instance

/-- **A closed WAL's files are files a crash may leave** (the synced mark forgotten). -/
theorem walFiles_walFilesC (a : WalA GF) (id cid : w64) (σ : StorContents) (sized : Bool) :
    walFiles (GF := GF) a id cid σ sized ⊢ walFilesC a id cid σ sized := by
  unfold walFiles walFilesC
  iintro ⟨%i, %d, Hd, -, Hn, Hu, Hc, %hf⟩
  iexists i, d
  iframe Hd Hn Hu Hc
  ipureintro; exact ⟨hf.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1⟩

/-- **The WAL's files after a crash** (see the file header): the area `a` of the old generation's WAL
names `a.W`, the new generation's `W'`; the old state `d` given back. -/
theorem walFilesC_crash (a : WalA GF) (W' : WalFs.WalGS GF) (i : Nat) (d : WalDur) (n : Nat) (id cid : w64)
    (hmd : d.metadata = walMetaEnc id cid) (hsz : d.sized = true) (hes : walEntsSized d.H) :
    letI := a.ext; letI := a.semOk; letI := a.has
    WalFs.walCrashWal a.W W' ∗ WalFs.walDiskAtI (W := a.W) a.dir i d ∗
      WalFs.walSyncedLb (W := a.W) a.dir i n ∗ WalFs.walNamed (W := a.W) a.dir i ∗
      WalFs.walUnlockedTok (W := W') ∗ Fs.osCallPerm (Fs.callKey a.R a.dir) (1 : Qp).half ⊢
      WalFs.walDiskAtI (W := a.W) a.dir i d ∗ ∃ j : Nat, ⌜n ≤ j ∧ j ≤ d.H.length⌝ ∗
        ∀ σ : StorContents, ⌜walRead ((walSrvHist d.H).take j) = some σ⌝ -∗
          walFilesC { a with W := W' } id cid σ true := by
  letI := a.ext; letI := a.semOk; letI := a.has
  iintro ⟨Hcs, Hd, #Hs, #Hn, Hu, Hc⟩
  icases WalFs.walDiskAt_crash_keepS a.W W' a.dir i d n $$ Hcs Hd Hs Hn with
    ⟨Hd, %I, %k, ⟨%hI, -⟩, Hd', -, #Hn'⟩
  obtain ⟨j, hj1, hj2, rfl⟩ := hI
  iframe Hd
  iexists j
  isplitr
  · ipureintro; exact ⟨hj1, hj2⟩
  iintro %σ %hr
  unfold walFilesC
  iexists 0, { d with H := d.H.take j, cut := k, unl := min d.unl (d.H.take j).length, pur := min d.pur (d.H.take j).length }
  iframe Hd' Hn' Hu Hc
  ipureintro
  refine ⟨?_, hmd, hsz, fun _ => walEntsSized_take hes j⟩
  show walRead (walSrvHist (d.H.take j)) = some σ
  rw [walSrvHist_take_eq]; exact hr

end defs

end EtcdGrove
end Perennial
