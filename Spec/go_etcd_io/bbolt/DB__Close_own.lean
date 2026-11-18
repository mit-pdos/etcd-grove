/-
`DB.Close` (bbolt) giving the file back (session bbolt-inv; `notes/bbolt-integration-plan.md`, D-I5,
and `notes/bbolt-spec-decisions.md`, S3a's D-S4 and "bbolt-inv"): a closer that owns the whole of
the committed data gets the database's file back as `fileHolds`, the inode `Open` named
(`boltIno`). Proof: `Proof/go_etcd_io/bbolt/DB__Close_own.lean`.
-/
module

public import Spec.go_etcd_io.bbolt.Api
public import GooseLang.Ext.Fs.FsNoErr

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `db.Close()` by the owner of the committed data `D` (all of `boltState`, so no transaction is
live: a read holds a fraction, a writer's commit takes it whole) and of the closer token (so the
database is open: session S3f): the database closed as by `DB.Close.spec`, and the file of inode `i`
(`Open`'s, `boltIno`) given back holding `D`, with `nil`; or the data's ownership back, and the file
system can fail (`¬ FsNoErr`: an `munmap`, `flock` or `close` of the file may have failed, here or in
an earlier remap, or a mapping leaked) or the file is not whole pages (`boltNoFile`: a partial last
page a failed write left), and then `nil`. -/
abbrev DB.Close_own.spec : Prop :=
  ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (db : Loc) (γ : BoltName) (i : Ino) (D : Data),
  {{ isBolt (GF := GF) db γ ∗ boltIno γ i ∗ boltState γ 1 D ∗ boltCloser γ }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ fileHolds i D) ∨
      (boltState γ 1 D ∗ (⌜¬ FsNoErr⌝ ∨ (⌜err = GoInterface.nil⌝ ∗ boltNoFile γ))) }}

end spec

end bbolt
end EtcdGrove
end Perennial
