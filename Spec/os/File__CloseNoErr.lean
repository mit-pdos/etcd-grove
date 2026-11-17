/-
`f.Close()` on an open `*os.File` with no I/O error (`File.Close.spec` over a semantics whose steps
satisfy **no I/O error on chosen files**, `FsStepSat (NoIoErr Sio)`; every inode covered): `nil`.
Proved in `Proof/os/File__CloseNoErr.lean`. Lean-first.
-/
module

public import Spec.os.File__Close
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
abbrev os.File.Close.specNoErr : Prop :=
  ∀ (Sio : IoSet) [FsStepSat (NoIoErr Sio)], (∀ st i, Sio.ino st i) →
  ∀ (f : Loc) (fd : w64) (name : GoString) (d : OsFd),
  {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name (DFrac.own 1) ∗
      osFd (GF := GF) fd (DFrac.own 1) d ∗ lockToks (GF := GF) fd d }}
    (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Close")) (Val #()))
  {{ RET #(interface.nil : GoInterface); os.ownFile f (-1 : w64) name (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
