/-
bbolt's vocabulary over the **shared mode of the tree** (S3a, `notes/bbolt-integration-plan.md`, D-I5):
what `Open.spec` (`Spec/go_etcd_io/bbolt/Open.lean`) takes of the database file's name, a claim on
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

/-- **What `Open(d/b)` needs at the name** (the shared mode; session S3f: a mappable file): `b` names
a file holding a database with the data `D`, at most `maxMapSize` bytes (`fileHoldsM`), or nothing,
and then `D = ∅` (`Open` creates the file there: bbolt always passes `O_CREATE`). -/
def nameHolds [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (h : NamesH) (b : GoString)
    (D : Data) : IProp GF :=
  iprop((∃ i, ⌜h.cur !! b = some (.file i)⌝ ∗ fileHoldsM i D) ∨ ⌜h.cur !! b = none ∧ D = ∅⌝)

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
  iapply fileHoldsM_new $$ H

end vocab

end bbolt
end EtcdGrove
end Perennial
