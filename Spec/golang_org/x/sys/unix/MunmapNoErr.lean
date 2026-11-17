/-
`unix.Munmap(b)` of a whole mapping with no error of the environment (`Munmap.spec` over a semantics
whose steps satisfy **no error of `flock`, `mmap`, `munmap` on chosen files**,
`FsStepSat (NoMapLockErr Sio)`, pending the user's review; every inode covered): `nil`, the mapping
gone from the `OsMeta`. Proved in `Proof/golang_org/x/sys/unix/MunmapNoErr.lean`. Lean-first.
-/
module

public import Spec.golang_org.x.sys.unix.Munmap
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
abbrev golang_org.x.sys.unix.Munmap.specNoErr : Prop :=
  ∀ (Sio : IoSet) [FsStepSat (NoMapLockErr Sio)], (∀ st i, Sio.ino st i) →
  ∀ (base : Loc) (len : w64) (p : Ino) (m : OsMeta) (vf : Nat → val),
  0 < len.toInt → m.maps !! base = some len.toNat →
  {{ osInv (GF := GF) ∗ osMeta (GF := GF) p (DFrac.own 1) m ∗
      cellsR (GF := GF) base 0 len.toNat vf }}
    (App (Val (@! golang_org.x.sys.unix.Munmap)) (Val #(⟨base, len, len⟩ : GoSlice)))
  {{ RET #(errnoErr 0); osMeta p (DFrac.own 1) ({ m with maps := GMap.delete base m.maps }) }}

end spec

end EtcdGrove
end Perennial
