/-
bbolt's `Options` as the backend's constructor uses it: a trust boundary over a type Goose does
not translate. Lean-first (no Rocq counterpart); 2026-10-17, branch `construct`.

**Why axioms.** `bolt.Options` (`go.etcd.io/bbolt/db.go`) is a struct whose `OpenFile` field
has type `func(string, int, os.FileMode) (*os.File, error)`, and `os.FileMode` is an alias of
`io/fs.FileMode`. Goose axiomatizes a type that refers to an alias of another package
(`goose/util/autotypes.go`: "alias from another package os"); listing `Options` in
`bbolt.toml`'s `translate` makes Goose emit the struct, but its field type then names
`os.FileMode.ty`, which does not exist (Perennial's `Code/os.lean` declares the alias as
`axiom FileMode : go.GoType`): a translator gap, recorded in `notes/STATUS.md` (item 6). So
`Options` stays axiomatized, and its generated `TypedPointsto`/`IntoValTypedUnderlying`
instances are `sorry -- axiomatized type`, which no result may use. `newBackend` allocates an
`Options` (`&bolt.Options{}`), copies `*boltOpenOptions` into it and stores seven of its
fields; this file states those operations' effects, over an abstract points-to `optsAt`, for
the part of an `Options` value bbolt's `Open` depends on (`OptsM`).

**What is assumed** (each true of Go; `OptsM`, `optsAt` and the backend's fact
`boltOpenOptionsOk` are in `BboltOptsDefs.lean`, which the backend's `Base.lean` imports: the struct's fields and their types are as in
`db.go`, a composite literal `bolt.Options{}` is the zero value):
- `optsAt l dq o`: the `Options` at `l` (fraction `dq`) has the fields `o` (and some others);
  `optsVal v o`: the Go value `v` is such an `Options`.
- `wp_optsLit`, `wp_optsAlloc`, `wp_optsLoad`, `wp_optsStore`: `bolt.Options{}` is the zero
  value (`optsZero`: not read-only, page size 0, no `OpenFile`, no logger), allocation, load and
  store of a whole value.
- `optsAt_bool`, `optsAt_int`, `optsAt_freelist`, `optsAt_timeout`, `optsAt_logger`: the typed
  points-to of a field of the right type (the fields' names and types are `db.go`'s); storing
  another field than `ReadOnly`, `PageSize`, `OpenFile` and `Logger` keeps `o`, storing
  `Logger` sets `o.logger`.
- `boltLogger l`: `l` is a `bolt.Logger` whose methods behave as bbolt's calls need (they log;
  `Fatal`/`Panic` stop). bbolt calls its logger from `Open` on (`Infof`, `Errorf`, ...); bbolt
  being the trust boundary, the predicate is abstract, given by `newBoltLoggerZap`'s axiom.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode


section preds
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [bbolt_sem : go_etcd_io.bbolt.Assumptions]

/-- The `Options` value `v` has the fields `o`. -/
axiom optsVal (v : go_etcd_io.bbolt.Options) (o : OptsM) : Prop
/-- `l` is a `bolt.Logger` whose methods behave as bbolt's calls need. -/
axiom boltLogger (l : GoInterface) : IProp GF

@[instance] axiom boltLogger_persistent (l : GoInterface) : Persistent (boltLogger (GF := GF) l)
/-- `bolt.Options{}` is the zero value. -/
axiom wp_optsLit :
  {{ (True : IProp GF) }}
    (App (Val (GoInstruction (CompositeLiteral go_etcd_io.bbolt.Options.ty)))
      (Val (LiteralValueV [])))
  {{ (v : go_etcd_io.bbolt.Options), RET #v; ⌜optsVal v optsZero⌝ }}

/-- Allocating an `Options` value. -/
axiom wp_optsAlloc (v : go_etcd_io.bbolt.Options) (o : OptsM) (h : optsVal v o) :
  {{ (True : IProp GF) }}
    (App (Val (GoInstruction (GoAlloc go_etcd_io.bbolt.Options.ty))) (Val #v))
  {{ (l : Loc), RET #l; optsAt l (DFrac.own 1) o }}

/-- Loading an `Options` value. -/
axiom wp_optsLoad (l : Loc) (dq : DFrac) (o : OptsM) :
  {{ optsAt (GF := GF) l dq o }}
    (App (Val (GoInstruction (GoLoad go_etcd_io.bbolt.Options.ty))) (Val #l))
  {{ (v : go_etcd_io.bbolt.Options), RET #v; optsAt l dq o ∗ ⌜optsVal v o⌝ }}

/-- Storing an `Options` value. -/
axiom wp_optsStore (l : Loc) (o o' : OptsM) (v : go_etcd_io.bbolt.Options) (h : optsVal v o') :
  {{ optsAt (GF := GF) l (DFrac.own 1) o }}
    (App (Val (GoInstruction (GoStore go_etcd_io.bbolt.Options.ty))) (Val (PairV #l #v)))
  {{ RET #(); optsAt l (DFrac.own 1) o' }}

/-- A `bool` field other than `ReadOnly` (`db.go`: `NoGrowSync`, `NoFreelistSync`,
`PreLoadFreelist`, `NoSync`, `Mlock`, `NoStatistics`): storing it keeps `o`. -/
axiom optsAt_bool (l : Loc) (o : OptsM) (f : GoString)
    (hf : f = go!"NoGrowSync" ∨ f = go!"NoFreelistSync" ∨ f = go!"PreLoadFreelist" ∨
      f = go!"NoSync" ∨ f = go!"Mlock" ∨ f = go!"NoStatistics") :
  optsAt (GF := GF) l (DFrac.own 1) o ⊢
    ∃ x : Bool, structFieldRef go_etcd_io.bbolt.Options f l ↦ x ∗
      (∀ y : Bool, structFieldRef go_etcd_io.bbolt.Options f l ↦ y -∗ optsAt l (DFrac.own 1) o)

/-- An `int` field other than `PageSize` (`MmapFlags`, `InitialMmapSize`, `MaxSize`): storing it
keeps `o`. -/
axiom optsAt_int (l : Loc) (o : OptsM) (f : GoString)
    (hf : f = go!"MmapFlags" ∨ f = go!"InitialMmapSize" ∨ f = go!"MaxSize") :
  optsAt (GF := GF) l (DFrac.own 1) o ⊢
    ∃ x : w64, structFieldRef go_etcd_io.bbolt.Options f l ↦ x ∗
      (∀ y : w64, structFieldRef go_etcd_io.bbolt.Options f l ↦ y -∗ optsAt l (DFrac.own 1) o)

/-- The `FreelistType` field: storing it keeps `o`. -/
axiom optsAt_freelist (l : Loc) (o : OptsM) :
  optsAt (GF := GF) l (DFrac.own 1) o ⊢
    ∃ x : go_etcd_io.bbolt.FreelistType,
      structFieldRef go_etcd_io.bbolt.Options go!"FreelistType" l ↦ x ∗
      (∀ y : go_etcd_io.bbolt.FreelistType,
        structFieldRef go_etcd_io.bbolt.Options go!"FreelistType" l ↦ y -∗
          optsAt l (DFrac.own 1) o)

/-- The `Timeout` field: storing it keeps `o`. -/
axiom optsAt_timeout (l : Loc) (o : OptsM) :
  optsAt (GF := GF) l (DFrac.own 1) o ⊢
    ∃ x : time.Duration, structFieldRef go_etcd_io.bbolt.Options go!"Timeout" l ↦ x ∗
      (∀ y : time.Duration, structFieldRef go_etcd_io.bbolt.Options go!"Timeout" l ↦ y -∗
        optsAt l (DFrac.own 1) o)

/-- The `Logger` field: it holds `o.logger`; storing it sets it. -/
axiom optsAt_logger (l : Loc) (o : OptsM) :
  optsAt (GF := GF) l (DFrac.own 1) o ⊢
    structFieldRef go_etcd_io.bbolt.Options go!"Logger" l ↦ (o.logger : go_etcd_io.bbolt.Logger) ∗
      (∀ y : go_etcd_io.bbolt.Logger, structFieldRef go_etcd_io.bbolt.Options go!"Logger" l ↦ y -∗
        optsAt l (DFrac.own 1) { o with logger := y })

end preds


end backend
end EtcdGrove
end Perennial
