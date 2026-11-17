/-
`syscall.Fdatasync(fd)`, byte-less, with no I/O error (`Fdatasync.specB` over a semantics whose
steps satisfy **no I/O error on chosen files**, `FsStepSat (NoIoErr Sio)`; every inode covered):
errno 0, the `OsMeta` `m.bsynced c` for some change number `c`. bbolt's `fdatasync`. Proved in
`Proof/syscall/FdatasyncNoErr.lean`. Lean-first.
-/
module

public import Spec.syscall.Fdatasync
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
variable [syscall.Assumptions]

/-- See the file header. -/
abbrev syscall.Fdatasync.specBNoErr : Prop :=
  ∀ (Sio : IoSet) [FsStepSat (NoIoErr Sio)], (∀ st i, Sio.ino st i) →
  ∀ (fd : w64) (dq : DFrac) (d : OsFd) (m : OsMeta),
  {{ osInv (GF := GF) ∗ osFd (GF := GF) fd dq d ∗
      osMeta (GF := GF) d.ino (DFrac.own 1) m }}
    (App (Val (@! syscall.Fdatasync)) (Val #fd))
  {{ RET #(errnoErr 0); osFd fd dq d ∗ ∃ c, osMeta d.ino (DFrac.own 1) (m.bsynced c) }}

end spec

end EtcdGrove
end Perennial
