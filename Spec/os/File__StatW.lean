/-
`f.Stat()` whose error witnesses that **the file system can fail** (`File.Stat.spec` with
`⌜¬ FsNoErr⌝` in its error arm; session S3f of `notes/bbolt-integration-plan.md`): under the premises
`FsNoErr` names, `Stat` has no error (`specNoErr`). Proved in `Proof/os/File__StatW.lean`, from the two.
-/
module

public import Spec.os.File__Stat
public import GooseLang.Ext.Fs.FsNoErr

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
abbrev os.File.Stat.specW : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf dq dqm : DFrac) (d : OsFd) (m : OsMeta),
  {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ osFd (GF := GF) fd dq d ∗
      osMeta (GF := GF) d.ino dqm m }}
    (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Stat")) (Val #()))
  {{ (fi : GoInterface) (err : GoInterface), RET (PairV #fi #err);
      os.ownFile f fd name dqf ∗ osFd fd dq d ∗ osMeta d.ino dqm m ∗
      ((∃ fs : Loc, ⌜err = interface.nil ∧
          fi = interface.mkOk (go.GoType.PointerType os.fileStat.ty) #fs⌝ ∗
          os.ownFileStat fs (W64 m.size)) ∨
       ⌜err ≠ interface.nil ∧ fi = interface.nil ∧ ¬ FsNoErr⌝) ∗
      fmtErrorOkOrNil err ∗
      (⌜err = GoInterface.nil⌝ ∨ ∃ e : w64, ⌜e ≠ 0⌝ ∗ os.errnoPathErr err e) }}

end spec

end EtcdGrove
end Perennial
