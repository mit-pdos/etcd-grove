/-
`f.Stat()` on an open `*os.File` with no I/O error (`File.Stat.spec` over a semantics whose steps
satisfy **no I/O error on chosen files**, `FsStepSat (NoIoErr Sio)`; every inode covered): a nil
error and the `*fileStat` holding the size as a `FileInfo` (bbolt's `Open` reads the file's size so).
Proved in `Proof/os/File__StatNoErr.lean`. Lean-first.
-/
module

public import Spec.os.File__Stat
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
variable [os.Assumptions]

/-- See the file header. -/
abbrev os.File.Stat.specNoErr : Prop :=
  ∀ (Sio : IoSet) [FsStepSat (NoIoErr Sio)], (∀ st i, Sio.ino st i) →
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf dq dqm : DFrac) (d : OsFd) (m : OsMeta),
  {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ osFd (GF := GF) fd dq d ∗
      osMeta (GF := GF) d.ino dqm m }}
    (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Stat")) (Val #()))
  {{ (fi : GoInterface), RET (PairV #fi #(interface.nil : GoInterface));
      os.ownFile f fd name dqf ∗ osFd fd dq d ∗ osMeta d.ino dqm m ∗
      ∃ fs : Loc, ⌜fi = interface.mkOk (go.GoType.PointerType os.fileStat.ty) #fs⌝ ∗
        os.ownFileStat fs (W64 m.size) }}

end spec

end EtcdGrove
end Perennial
