/- Lean-first (no Rocq counterpart).

# The fdatasync of a whole-owned WAL file (W2's `cut`, W4's `Create`: `walPreSyncOk`)

Before its rename a WAL segment (`cut`'s `N.tmp`, `Create`'s first segment) is owned wholly and
written through `os.File.writerStream` from offset 0 (`os.fileW … 0 xs0`). `sync` fdatasyncs it
(`walPreSyncOk f W S`, `WAL__SaveSnapshotPre.lean`): the stream's state carries `osInv`
(`os.fileWI`, the hypothesis triple has no other place for it), and a successful fdatasync leaves
`os.fileS`: the same stream state with the `OsMeta` synced and every byte durable.

* `io.writerStream_frame`: a stream with a persistent frame is a stream.
* `os.fileWI`/`os.fileBI`/`os.fileS`, and `os.fileWI_preSyncOk` (over `fileutil.Fdatasync.spec`).
-/
module

public import LinuxFs.Proof.os.WriterStream
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.Fdatasync
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__SaveSnapshotPre

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section frame
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A stream writer with a persistent frame `R`** in each of its states. -/
theorem io.writerStream_frame (wi : GoInterfaceOk) (lim : Nat) (W : List w8 → IProp GF)
    (B : List w8 → List w8 → IProp GF) (R : IProp GF) [Persistent R] :
    □ R ∗ io.writerStream wi lim W B ⊢
      io.writerStream wi lim (fun o => iprop(W o ∗ R)) (fun a b => iprop(B a b ∗ R)) := by
  iintro ⟨#HR, #Hw⟩
  unfold io.writerStream
  iintro !> %out %p %xs %dq %hb
  iintro !> %Φ ⟨⟨HW, -⟩, Hp⟩ HΦ
  iapply Hw $$ %out %p %xs %dq %hb [$HW $Hp]
  iintro !> %n %err ⟨Hp, Hr⟩
  iapply HΦ
  simp only []
  iframe Hp
  icases Hr with (⟨%he, HW⟩ | ⟨%he, HB⟩)
  · ileft; isplitr
    · ipureintro; exact he
    iframe; iframe #
  · iright; isplitr
    · ipureintro; exact he
    iframe; iframe #

end frame

section sync
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [os.Assumptions] [os.file.FieldAssumptions]
variable [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

/-- The stream's state, with `osInv`. -/
def os.fileWI (f : Loc) (fd : w64) (name : GoString) (dqf dq : DFrac) (d : OsFd) (m0 : OsMeta)
    (xs0 : List ByteG) (out : List w8) : IProp GF :=
  iprop(os.fileW f fd name dqf dq d m0 0 xs0 out ∗ osInv (GF := GF))

/-- The stream's broken state, with `osInv`. -/
def os.fileBI (f : Loc) (fd : w64) (name : GoString) (dqf dq : DFrac) (d : OsFd) (m0 : OsMeta)
    (xs0 : List ByteG) (out xs : List w8) : IProp GF :=
  iprop(os.fileB f fd name dqf dq d m0 0 xs0 out xs ∗ osInv (GF := GF))

/-- **The stream's state after a successful fdatasync**: as `os.fileW`'s, the `OsMeta` synced and
every byte durable. -/
def os.fileS (f : Loc) (fd : w64) (name : GoString) (dqf dq : DFrac) (d : OsFd) (m0 : OsMeta)
    (xs0 : List ByteG) (out : List w8) : IProp GF :=
  iprop(∃ (m : OsMeta) (ys : List ByteG), ⌜os.StreamOk m0 0 xs0 out m ys⌝ ∗
    os.ownFile f fd name dqf ∗ osFd fd dq d ∗ os.ownOff f (W64 ((0 + out.length : Nat) : Int)) ∗
    osMeta d.ino (DFrac.own 1) m.synced ∗
    osBytes d.ino 0 (DFrac.own 1) (ys.map (fun x => durB x.1)) ∗ osInv (GF := GF))

/-- The stream from offset 0, with `osInv`. -/
theorem os.File.writerStreamI (wp_WriteAt : os.File.WriteAt.specLong (GF := GF) (hG := hG))
    (f : Loc) (fd : w64) (name : GoString) (dqf dq : DFrac) (d : OsFd) (m0 : OsMeta)
    (xs0 : List ByteG) (lim : Nat) (hfd : 0 ≤ fd.toInt) (hwr : d.writable = true)
    (hmaps : m0.maps = ∅) (hlim : lim < 2 ^ 62) :
    osInv (GF := GF) ⊢ io.writerStream (os.fileWi f) lim (os.fileWI f fd name dqf dq d m0 xs0)
      (os.fileBI f fd name dqf dq d m0 xs0) := by
  iintro #Hinv
  ihave Hw := os.File.writerStream wp_WriteAt f fd name dqf dq d m0 0 xs0 lim hfd hwr hmaps
    (by omega) $$ Hinv
  unfold os.fileWI os.fileBI
  iapply io.writerStream_frame (R := osInv (GF := GF))
  iframe Hinv Hw

/-- **The fdatasync of the stream's file** (`walPreSyncOk`): from the state after `out`, success
gives `os.fileS`, failure the state back. -/
theorem os.fileWI_preSyncOk
    (wp_Fdatasync : go_etcd_io.etcd.client.pkg.v3.fileutil.Fdatasync.spec (GF := GF) (hG := hG))
    (f : Loc) (fd : w64) (name : GoString) (dqf dq : DFrac) (d : OsFd) (m0 : OsMeta)
    (xs0 : List ByteG) :
    walPreSyncOk (hG := hG) f (os.fileWI f fd name dqf dq d m0 xs0) (os.fileS f fd name dqf dq d m0 xs0) := by
  intro out
  iintro %Φ HW HΦ
  iunfold os.fileWI at HW
  icases HW with ⟨HW, #Hinv⟩
  iunfold os.fileW at HW
  icases HW with ⟨%m, %ys, %Hok, Hf, Hfd, Ho, Hm, Hbs⟩
  have hyl : ys.length = m.size := by have := Hok.2.2.2.2.2.2.1; omega
  wp_apply (wp_Fdatasync f fd name dqf dq d m 0 ys (OsMeta.covers_whole m hyl))
    $$ [$Hinv $Hf $Hfd $Hm $Hbs] as %e ⟨Hf, Hfd, Hr⟩
  iapply HΦ
  icases Hr with (⟨%he, Hm, Hbs⟩ | ⟨%he, Hm, Hbs⟩)
  · ileft
    isplitr
    · ipureintro; exact he
    iunfold os.fileS
    iexists m, ys
    iframe
    iframe #
    ipureintro; exact Hok
  · iright
    isplitr
    · ipureintro; exact he.1
    iunfold os.fileWI
    iframe Hinv
    iunfold os.fileW
    iexists m, ys
    iframe
    ipureintro; exact Hok

end sync

end EtcdGrove
end Perennial

end
