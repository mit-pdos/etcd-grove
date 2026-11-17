/-
`f.Sync()` on an open `*os.File`, byte-less, with no I/O error (`File.Sync.specB` over a semantics
whose steps satisfy **no I/O error on chosen files**, `FsStepSat (NoIoErr Sio)`; every inode
covered): `nil`, the `OsMeta` `m.bsynced c` for some change number `c` (bbolt's `DB.grow`). Proved
in `Proof/os/File__SyncNoErr.lean`. Lean-first.
-/
module

public import Spec.os.File__Sync
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
abbrev os.File.Sync.specBNoErr : Prop :=
  ∀ (Sio : IoSet) [FsStepSat (NoIoErr Sio)], (∀ st i, Sio.ino st i) →
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf dq : DFrac) (d : OsFd) (m : OsMeta),
  {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ osFd (GF := GF) fd dq d ∗
      osMeta (GF := GF) d.ino (DFrac.own 1) m }}
    (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Sync")) (Val #()))
  {{ RET #(interface.nil : GoInterface); os.ownFile f fd name dqf ∗ osFd fd dq d ∗
      ∃ c, osMeta d.ino (DFrac.own 1) (m.bsynced c) }}

end spec

end EtcdGrove
end Perennial
