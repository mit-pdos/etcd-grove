/-
`DB.Close` (bbolt): its spec in bbolt's API (the frozen spec of 2026-11-03; the vocabulary in
`Spec/go_etcd_io/bbolt/Api.lean`, the decisions in `notes/bbolt-spec-decisions.md`). Proof:
`Proof/go_etcd_io/bbolt/DB__Close.lean` (unfinished until bbolt's invariants are designed).
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
/- Every bbolt spec is stated over OsFs's semantics (round 11, D22: the default `osFs_semantics`,
whose `pwrite` within one aligned OS page is all-or-nothing): the binder `∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]` at
the head of each triple (a section variable is dropped from a definition that does not use it),
and in the signature of each vocabulary predicate, so that every statement carries it (checked
with `#check`). -/
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `db.Close()` by the owner of the committed data `D` (all of `boltState`, so no transaction is
live: a read holds a fraction, a writer's commit takes it whole) and of the closer token
(`boltCloser`, from `Open`: so no other thread closes the database under its owner; Go lets any
goroutine close it any number of times). It takes the three locks and closes the database (every
later `Begin` fails). Outcomes:
- `nil`, and the file of inode `i` (`Open`'s, `boltIno`) given back holding `D`, mappable
  (`fileHoldsM`: what `Open.spec` takes, so the database can be reopened; session S3g: the file never
  grows past `maxAddr + AllocSize < maxMapSize`, since every mapping fits the model's address space);
- `¬ FsNoErr`: some step of the file model failed in a way `NoIoErr`/`NoMapLockErr` exclude (here: an
  `munmap`, `flock` or `close`; or earlier: a remap's `munmap` or `madvise` that leaked a mapping, or a
  commit's write that failed part way, leaving a partial last page), which `Fs.fsNoErr_of` refutes
  under those premises. (Session S3g: under the premises a write fails only at `maxBytes`, page-aligned,
  so the file stays whole pages.) -/
abbrev DB.Close.spec : Prop :=
  ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (db : Loc) (γ : BoltName) (i : Ino) (D : Data),
  {{ isBolt (GF := GF) db γ ∗ boltIno γ i ∗ boltState γ 1 D ∗ boltCloser γ }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ fileHoldsM i D) ∨ ⌜¬ FsNoErr⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
