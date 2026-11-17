/-
`unix.Mmap(fd, 0, length, PROT_READ, MAP_SHARED[|MAP_POPULATE])` with no error of the environment
(`Mmap.spec` over a semantics whose steps satisfy **no error of `flock`, `mmap`, `munmap` on chosen
files**, `FsStepSat (NoMapLockErr Sio)`, pending the user's review; every inode covered): a slice of
fresh cells, whose client halves hold the file's bytes, then holes past its end, the mapping
recorded in the `OsMeta`, and errno 0. With no room left in the address space for the mapping, the
call does not return (`MmapStall`, pending the user's review): the spec covers the executions that
do not run out of it, as a Go allocation's. bbolt's `mmap`. Proved in
`Proof/golang_org/x/sys/unix/MmapNoErr.lean`. Lean-first.
-/
module

public import Spec.golang_org.x.sys.unix.Mmap
public import GooseLang.Ext.Fs.Premises
public import GooseLang.Ext.Fs.FilteredSem

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [golang_org.x.sys.unix.Assumptions]

/-- See the file header. -/
abbrev golang_org.x.sys.unix.Mmap.specNoErr : Prop :=
  ∀ (Sio : IoSet) [FsStepSat (NoMapLockErr Sio)], (∀ st i, Sio.ino st i) →
  ∀ (fd off len prot fl : w64) (dq : DFrac) (d : OsFd) (m : OsMeta),
  d.readable = true → off = 0 → 0 < len.toInt → prot.toNat = PROT_READ →
  (fl.toNat = MAP_SHARED ∨ fl.toNat = MAP_SHARED + MAP_POPULATE) →
  {{ osInv (GF := GF) ∗ osFd (GF := GF) fd dq d ∗
      osMeta (GF := GF) d.ino (DFrac.own 1) m }}
    (App (App (App (App (App (Val (@! golang_org.x.sys.unix.Mmap)) (Val #fd)) (Val #off))
      (Val #len)) (Val #prot)) (Val #fl))
  {{ (base : Loc), RET (PairV #(⟨base, len, len⟩ : GoSlice) #(errnoErr 0)); osFd fd dq d ∗
      osMeta d.ino (DFrac.own 1) ({ m with maps := <[base := len.toNat]> m.maps }) ∗
      ∃ bs : List w8, ⌜bs.length = m.size⌝ ∗
        cellsR base 0 len.toNat (fun i => toCellVal bs[i]?) }}

end spec

end EtcdGrove
end Perennial
