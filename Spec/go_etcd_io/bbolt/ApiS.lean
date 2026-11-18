/-
bbolt's vocabulary over the **shared mode of the tree** (S3a, `notes/bbolt-integration-plan.md`, D-I5):
what `Open_shared.spec` (`Spec/go_etcd_io/bbolt/Open_shared.lean`) takes of the database file's name, a claim on
it (`osNames j (.only [b]) _ h`, `GooseLang/Ext/Fs/TreeShared.lean`) in place of the whole tree. Over
`Api.lean`'s sealed `fileHolds`; nothing of bbolt's internals.
-/
module

public import Spec.go_etcd_io.bbolt.Api
public import GooseLang.Ext.Fs.NamesGhost

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI go_etcd_io.bbolt

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **What `Open(d/b)` needs of the name `b`** in the shared mode, over the claim's history `h` on
`b`: `b` names a file that holds a database with the data `D` (`fileHolds`), or nothing, and then
`D = ∅` (`Open` creates the file there: bbolt always passes `O_CREATE`). The shared mode's
`pathHolds`. -/
def nameHolds [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (h : NamesH) (b : GoString)
    (D : Data) : IProp GF :=
  iprop((∃ i, ⌜h.cur !! b = some (.file i)⌝ ∗ fileHolds i D) ∨ ⌜h.cur !! b = none ∧ D = ∅⌝)

/-- **A file just created holds the empty database, at the name** (the claim after the create). -/
theorem nameHolds_new [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (h : NamesH) (b : GoString)
    (i : Ino) (hb : h.cur !! b = some (.file i)) :
    osMeta (GF := GF) i (DFrac.own 1) newMeta ⊢ nameHolds h b ∅ := by
  iintro H
  unfold nameHolds
  ileft
  iexists i
  isplitr
  · ipureintro; exact hb
  iapply fileHolds_new $$ H

/-- **What `Open(d/b)` with no error needs at the name** (session S3f): `nameHolds` with a mappable
file (`fileHoldsM`), or nothing (and `D = ∅`). -/
def nameHoldsM [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (h : NamesH) (b : GoString)
    (D : Data) : IProp GF :=
  iprop((∃ i, ⌜h.cur !! b = some (.file i)⌝ ∗ fileHoldsM i D) ∨ ⌜h.cur !! b = none ∧ D = ∅⌝)

/-- A mappable file at the name holds its data there. -/
theorem nameHoldsM_nameHolds [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (h : NamesH)
    (b : GoString) (D : Data) :
    nameHoldsM (GF := GF) h b D ⊢ nameHolds h b D := by
  unfold nameHoldsM nameHolds
  iintro (⟨%i, %hi, H⟩ | %hn)
  · ileft; iexists i; isplitr
    · ipureintro; exact hi
    · iapply fileHoldsM_fileHolds $$ H
  · iright; ipureintro; exact hn

/-- **A file just created holds the empty database, mappable, at the name**. -/
theorem nameHoldsM_new [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (h : NamesH) (b : GoString)
    (i : Ino) (hb : h.cur !! b = some (.file i)) :
    osMeta (GF := GF) i (DFrac.own 1) newMeta ⊢ nameHoldsM h b ∅ := by
  iintro H
  unfold nameHoldsM
  ileft
  iexists i
  isplitr
  · ipureintro; exact hb
  iapply fileHoldsM_new $$ H

end vocab

end bbolt
end EtcdGrove
end Perennial
