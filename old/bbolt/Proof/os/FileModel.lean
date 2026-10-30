/-
The model of files and memory maps that bbolt's proof rests on (the trust boundary: `os`,
`syscall` and `golang.org/x/sys/unix` are translated names-only, so their functions have no
semantics and their specs, in `Spec/os/`, `Spec/syscall/`, `Spec/golang_org/x/sys/unix/`,
are axioms; `etc/tcb-report.py` lists them).

The state is abstract (the operating system's, not the heap's): predicates declared here,
with no lemmas assumed about them. There are no crashes (`Sync` and `Fdatasync` change
nothing), and the process is the file's only user (bbolt takes an `flock`).

* `fsFile path o`: the file system holds the file `path` with contents `o` (`none`: absent).
* `osFile f fd`: the `*os.File` `f` is open with descriptor `fd` (persistent).
* `fileBytes fd bs`: the open file `fd` holds the bytes `bs`.
* `filePath fd path`: `fd` was opened from `path` (`Close` gives back `fsFile path`).
* `fileMap fd m`: the read-only shared mapping of `fd`, if any: `some (p, n)`, the first `n`
  bytes of the file at `p` (`unix.Mmap(fd, 0, n, PROT_READ, MAP_SHARED|_)`).
* `fileInfo fi n`: the `os.FileInfo` `fi` reports size `n` (persistent).

**The mapping.** Its cells are ordinary heap cells, and they hold the file's bytes: `Mmap`
gives the caller *half* of each mapped cell's points-to (`mapRange`), the other half being
the operating system's (held in `fileMap`, notionally). A write to the file (`WriteAt`,
`Truncate`) takes the caller's half of the mapped cells it changes and gives it back with
the new bytes, so a reader of the mapping sees what was written, and keeps seeing it while
it holds (part of) the half; and since the caller never has the whole points-to, it cannot
store into the mapping (which is `PROT_READ`: a store would fault). Only the cells of the
mapping inside the file exist (reading past the end of the file faults).
-/
module

public import GeneratedProof.go_etcd_io.bbolt
public import Perennial.Golang.Theory.Bytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI

/-- `MAP_SHARED|flags` has the `MAP_SHARED` bit. -/
theorem or_one_and_one (x : BitVec 64) : (1#64 ||| x) &&& 1#64 = 1#64 := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or]
  by_cases h : i = 0 <;> simp [h]

section model
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

axiom fsFile (path : GoString) (o : Option (List w8)) : IProp GF
axiom osFile (f : Loc) (fd : w64) : IProp GF
axiom osFile_persistent (f : Loc) (fd : w64) : Persistent (osFile (GF := GF) f fd)
axiom fileBytes (fd : w64) (bs : List w8) : IProp GF
axiom filePath (fd : w64) (path : GoString) : IProp GF
axiom fileMap (fd : w64) (m : Option (Loc × Nat)) : IProp GF
axiom fileInfo (fi : GoInterface) (n : Nat) : IProp GF
axiom fileInfo_persistent (fi : GoInterface) (n : Nat) : Persistent (fileInfo (GF := GF) fi n)

attribute [instance] osFile_persistent fileInfo_persistent

/-- `bs` with `ds` written at `off`, the gap after the end (if any) zeros (`pwrite`). -/
def writeBytes (bs : List w8) (off : Nat) (ds : List w8) : List w8 :=
  bs.take off ++ List.replicate (off - bs.length) 0 ++ ds ++ bs.drop (off + ds.length)

/-- `bs` truncated or extended with zeros to `n` bytes (`ftruncate`). -/
def truncBytes (bs : List w8) (n : Nat) : List w8 :=
  bs.take n ++ List.replicate (n - bs.length) 0

/-- The caller's half of the cells of the mapping `m` (of a file holding `bs`) for the file
offsets `[lo, hi)`: the bytes of the file there that the mapping covers. -/
def mapRange (m : Option (Loc × Nat)) (bs : List w8) (lo hi : Nat) : IProp GF :=
  match m with
  | none => emp
  | some (p, n) => bytesPointsto (p +ₗ (lo : Int)) (DFrac.own (Qp.half 1)) (((bs.take n).take hi).drop lo)

end model

end bbolt
end EtcdGrove
end Perennial
