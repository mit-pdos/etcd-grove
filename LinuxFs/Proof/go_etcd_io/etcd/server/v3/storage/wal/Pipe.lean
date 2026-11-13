/- Lean-first (no Rocq counterpart).

# The WAL's file pipeline (W2 of `notes/wal-fsext-plan.md`)

`filePipeline` (S/file_pipeline.go): a goroutine (`run`) that makes the WAL's next segment ahead
of time. Round `n` (`fp.count = n`): `alloc` opens `pipeTmp n` (`fmt.Sprintf("%d.tmp", n % 2)`)
in the WAL directory with `O_CREAT|O_TRUNC|O_WRONLY`, locks it and preallocates it to `fp.size`
zeros; then `run` offers the file on `filec` (unbuffered) until `Open` takes it, or `Close` closes
`donec` (the file is removed and closed). An `alloc` error goes to `errc` (buffered, one value),
which `run` closes when it returns.

* **`filec`, an indexed handshake** (`HandshakeN.lean`): the `n`-th exchange hands `Open` the file
  `n` (`pipeFile`: the locked file, its offset 0, its `OsMeta` and zero bytes whole, the whole claim
  on its name), and hands `run` back the claim on `pipeTmp (n + 1)` (`pipeQ`): the name of file
  `n - 1`, which the caller renamed away in its previous cut (at `n = 0`, the caller's from the
  start). With the claim comes the bound `n + 1 < 2^63` (`count % 2` is a signed remainder).
* **`errc`, an SPSC channel** (Perennial's `Spsc`): its one value is an error with the pipeline's
  resources (`pipeLeft`: its half of the call permission, its fraction of the directory's path,
  its claim); closed without a value only after `Close` closed `donec`, with the same resources
  and the witness that `Close` ran (`pipeClosedW`).
* **`donec`, a broadcast** (Perennial's `Broadcast`), closed by `Close` with `pipeClosedW`.
* **The caller's token** `pipeMain γ n`: `n` files received, the consumer side of `errc` (nothing
  received), the right to close `donec`, and the alive flag (`dghostVar γ.a (own 1) false`;
  `Close` turns it into the persistent `pipeClosedW`). An `Open` that received the error leaves
  `pipeDead γ e`.
* **The goroutine's state** `pipeRun γ n`: `n` files sent, `fp.count = n`, the claim on
  `pipeTmp n`, the producer side of `errc`, `pipeRes`.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.HandshakeN
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Cut
public import LinuxFs.Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.LockDefs
public import LinuxFs.Proof.os.Off
public import LinuxFs.Proof.os.SharedAu
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.createNewWALFile
public import LinuxFs.GeneratedProof.go_etcd_io.etcd.server.v3.storage.wal
public import Spec.go_uber_org.zap.Defs
public import Perennial.Golang.Theory.Chan.Idioms.Spsc
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast
public import Perennial.Ghost.DGhostVar

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Fs

/-- The pipeline's `n`-th file name: `fmt.Sprintf("%d.tmp", n % 2)` (file_pipeline.go:77). -/
def pipeTmp (n : Nat) : GoString := if n % 2 = 0 then go!"0.tmp" else go!"1.tmp"

theorem pipeTmp_mem (n : Nat) : pipeTmp n ∈ walTmps := by
  unfold pipeTmp walTmps; split <;> simp

theorem pipeTmp_add_two (n : Nat) : pipeTmp (n + 2) = pipeTmp n := by
  unfold pipeTmp; simp [Nat.add_mod_right]

theorem pipeTmp_ne_succ (n : Nat) : pipeTmp (n + 1) ≠ pipeTmp n := by
  unfold pipeTmp
  split <;> split <;> first | decide | omega

/-- The ghost names and channels of a pipeline. -/
structure PipeNames where
  fc : Loc
  ec : Loc
  dc : Loc
  f : HsnNames
  e : SpscNames
  d : ChanNames
  a : GName

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions]

/-- **A whole claim on the name `b` of the directory `j`, holding no directory** (absent or a
file: `alloc`'s `O_CREAT|O_TRUNC` open makes it a fresh, empty file either way). -/
def tmpClaim (j : Ino) (b : GoString) : IProp GF :=
  iprop(∃ h : NamesH, osNames j (.only [b]) (DFrac.own 1) h ∗
    ⌜∀ J, h.cur !! b ≠ some (.dir J)⌝)

/-- **The `n`-th file of the pipeline of the directory `dir` (inode `j`), at `lf`**: a locked file
on the name `pipeTmp n`, open write-only at offset 0, its `OsMeta` (no mappings) and its bytes
whole, all zeros (`osZerosA`), and the whole claim on its name, which holds it. -/
def pipeFile (j : Ino) (dir : GoString) (n : Nat) (lf : Loc) : IProp GF :=
  iprop(∃ (f : Loc) (fd : w64) (i : Ino) (m : OsMeta) (h : NamesH),
    fileutil.lockedFile lf f ∗ os.ownFile f fd (child dir (pipeTmp n)) (DFrac.own 1) ∗
    os.ownOff f (W64 0) ∗ osFd fd (DFrac.own 1) (openFd i (wal.walOpenFlag true ||| W64 0x80000)) ∗
    osMeta i (DFrac.own 1) m ∗ osZerosA i 0 m.size (DFrac.own 1) ∗
    osNames j (.only [pipeTmp n]) (DFrac.own 1) h ∗
    ⌜0 ≤ fd.toInt ∧ m.maps = ∅ ∧ h.cur !! pipeTmp n = some (.file i)⌝)

/-- What the receiver of file `n` hands back: the claim on `pipeTmp (n + 1)`, and the bound. -/
def pipeQ (j : Ino) (n : Nat) : IProp GF :=
  iprop(tmpClaim j (pipeTmp (n + 1)) ∗ ⌜n + 1 < 2 ^ 63⌝)

/-- What the pipeline holds of the file system besides its claim: half of the call permission,
the fraction `dq` of the directory's path. -/
def pipeRes (R : Roots) (dir : GoString) (dq : DFrac) (j : Ino) : IProp GF :=
  iprop(osCallPerm (1 : Qp).half ∗ osPathS R dir dq j)

/-- The pipeline's resources, back after `run` returned. -/
def pipeLeft (R : Roots) (dir : GoString) (dq : DFrac) (j : Ino) : IProp GF :=
  iprop(pipeRes R dir dq j ∗ ∃ b, ⌜b ∈ walTmps⌝ ∗ tmpClaim j b)

/-- `Close` ran (persistent). -/
def pipeClosedW (γ : PipeNames) : IProp GF := dghostVar γ.a DFrac.discard true

instance pipeClosedW_persistent (γ : PipeNames) : Persistent (pipeClosedW (GF := GF) γ) := by
  unfold pipeClosedW; infer_instance

/-- `errc`'s value: an error, with the pipeline's resources. -/
def pipeErrP (R : Roots) (dir : GoString) (dq : DFrac) (j : Ino) (_ : Int) (e : GoInterface) :
    IProp GF :=
  iprop(⌜e ≠ interface.nil⌝ ∗ pipeLeft R dir dq j)

/-- `errc` closed: after a value, nothing; without one, after `Close`, the resources. -/
def pipeErrR (γ : PipeNames) (R : Roots) (dir : GoString) (dq : DFrac) (j : Ino)
    (sent : List GoInterface) : IProp GF :=
  iprop(⌜sent ≠ []⌝ ∨ pipeLeft R dir dq j ∗ pipeClosedW γ)

/-- **The pipeline `fp` of the directory `dir` (inode `j`, path fraction `dq` under the roots
`R`)** (persistent): its read-only fields, the three channels' protocols, and the environment
`run` needs. -/
def isFilePipe (fp : Loc) (γ : PipeNames) (R : Roots) (dir : GoString) (dq : DFrac) (j : Ino)
    (sz : w64) : IProp GF :=
  iprop(∃ lg : Loc,
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.filePipeline go!"lg" fp ↦□ lg ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.filePipeline go!"dir" fp ↦□ dir ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.filePipeline go!"size" fp ↦□ sz ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.filePipeline go!"filec" fp ↦□ γ.fc ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.filePipeline go!"errc" fp ↦□ γ.ec ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.filePipeline go!"donec" fp ↦□ γ.dc ∗
    isHsn (V := Loc) γ.f γ.fc (fun n lf => pipeFile j dir n lf) (pipeQ j) ∗
    isSpsc (V := GoInterface) γ.e γ.ec (pipeErrP R dir dq j) (pipeErrR γ R dir dq j) ∗
    ownBroadcastChan γ.dc γ.d (pipeClosedW γ) .Unknown ∗
    zapLoggerOk lg ∗ osInv (GF := GF) ∗ osSharedInv R ∗
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗
    ⌜0 ≤ sz.toInt ∧ sz.toInt ≤ 0xffffffff000⌝)

instance isFilePipe_persistent (fp : Loc) (γ : PipeNames) (R : Roots) (dir : GoString) (dq : DFrac)
    (j : Ino) (sz : w64) : Persistent (isFilePipe (GF := GF) fp γ R dir dq j sz) := by
  unfold isFilePipe; infer_instance

/-- **The caller's token, `n` files received** (the file header). -/
def pipeMain (γ : PipeNames) (n : Nat) : IProp GF :=
  iprop(hsnRcv γ.f n ∗ spscConsumer γ.e ([] : List GoInterface) ∗
    ownBroadcastChan γ.dc γ.d (pipeClosedW γ) .Pending ∗ dghostVar γ.a (DFrac.own 1) false)

/-- **The caller's token after an `Open` that received the error `e`.** -/
def pipeDead (γ : PipeNames) (e : GoInterface) : IProp GF :=
  iprop(spscConsumer γ.e [e] ∗ ownBroadcastChan γ.dc γ.d (pipeClosedW γ) .Pending ∗
    dghostVar γ.a (DFrac.own 1) false)

/-- **The goroutine's state, `n` files sent** (the file header). -/
def pipeRun (fp : Loc) (γ : PipeNames) (R : Roots) (dir : GoString) (dq : DFrac) (j : Ino)
    (n : Nat) : IProp GF :=
  iprop(hsnSnd γ.f n ∗ spscProducer γ.e ([] : List GoInterface) ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.filePipeline go!"count" fp ↦ W64 n ∗
    tmpClaim j (pipeTmp n) ∗ pipeRes R dir dq j ∗ ⌜n < 2 ^ 63⌝)

end defs

end WalFs
end EtcdGrove
end Perennial
