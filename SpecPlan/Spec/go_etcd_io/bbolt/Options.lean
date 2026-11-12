/-
# bbolt's `Options` (batch 4c): the trust boundary over an axiomatized type

`bolt.Options` stays axiomatized in the translation (`Code/go_etcd_io/bbolt.toml`: `translate =
["*", "!Options", "!DefaultOptions", ...]`), so the operations a client and `Open` perform on one
(the literal, allocation, whole loads and stores, field reads and stores) are stated here over the
abstract points-to `optsAt l dq o` (`Api.lean`) and the value relation `optsVal v o`, for the part
`Open` depends on (`OptsM`). **Assumed** (trust-boundary statements, restated from the old
`specs-ref/Proof/go_etcd_io/bbolt/Options.lean`, D13): each is true of Go, the struct's fields and
their types being `db.go`'s, and `bolt.Options{}` being the zero value; when `Options` is
translated with `Open`'s proof, they become lemmas of the struct. A field `OptsM` does not track
(`NoGrowSync`, `PreLoadFreelist`, `NoStatistics`, `InitialMmapSize`, `MaxSize`,
`Timeout`, `FreelistType`, ...) is read as some value and stored without changing `o`.

**Field laws (verify-round, A11 F8; re-review N4).** The field comes at `optsAt`'s own fraction `dq`
(was an unrelated `dq'`, so a store, which needs the whole field, had no source).
Each `optsAt_<kind>` law gives the field's points-to with
**two alternative** ways back, joined by `∧` (was `∗`): restoring the same value, or (with all of
`optsAt`) storing a new one. With `optsAt` the struct's points-to (the intended realization), each
wand needs the other fields' points-to, so the two cannot both be had: `∗` was false in the model.

**Keyed literals (A11 F7).** There is no spec of a keyed literal `bolt.Options{F: v, ...}`: no
translated code has one (the backend's `&bolt.Options{}` then field stores, `backend.go:216-230`;
etcd's only keyed literal, `boltOpenOptions` in `config_linux.go:29-32`, is a package variable whose
initializer the translation leaves untranslated, `boltOpenOptions.init`, so its value is the
backend's own assumed fact, its `PkgInit` law). The snippets build their options from `{}` and
field stores, as the backend does.

Users: `backend.newBackend` (`backend.go:216-230`: `&bolt.Options{}`, `*bopts = *boltOpenOptions`,
field stores), defrag (`:521-531`: a copy, `OpenFile`, `Mlock`, `NoSync`), the bank (`nil`).
Snippets: `ReqBackendOpen`, `ReqDefrag`.
-/
module

public import SpecPlan.Spec.go_etcd_io.bbolt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The `Options` value `v` has the fields `o` (assumed). -/
opaque optsVal (v : go_etcd_io.bbolt.Options) (o : OptsM) : Prop

/-- `bolt.Options{}` is the zero value (`OptsM.dflt`'s fields). -/
def optsLit.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val (GoInstruction (CompositeLiteral go_etcd_io.bbolt.Options.ty)))
      (Val (LiteralValueV [])))
  {{ (v : go_etcd_io.bbolt.Options), RET #v; ⌜optsVal v OptsM.dflt⌝ }}

/-- Allocating an `Options` value. -/
def optsAlloc.spec [HasExt osFsExt] : Prop :=
  ∀ (v : go_etcd_io.bbolt.Options) (o : OptsM), optsVal v o →
  {{ (True : IProp GF) }}
    (App (Val (GoInstruction (GoAlloc go_etcd_io.bbolt.Options.ty))) (Val #v))
  {{ (l : Loc), RET #l; optsAt l (DFrac.own 1) o }}

/-- Loading an `Options` value (`*bopts`, `options := *b.bopts`). -/
def optsLoad.spec [HasExt osFsExt] : Prop :=
  ∀ (l : Loc) (dq : DFrac) (o : OptsM),
  {{ optsAt (GF := GF) l dq o }}
    (App (Val (GoInstruction (GoLoad go_etcd_io.bbolt.Options.ty))) (Val #l))
  {{ (v : go_etcd_io.bbolt.Options), RET #v; optsAt l dq o ∗ ⌜optsVal v o⌝ }}

/-- Storing an `Options` value (`*bopts = *boltOpenOptions`). -/
def optsStore.spec [HasExt osFsExt] : Prop :=
  ∀ (l : Loc) (o o' : OptsM) (v : go_etcd_io.bbolt.Options), optsVal v o' →
  {{ optsAt (GF := GF) l (DFrac.own 1) o }}
    (App (Val (GoInstruction (GoStore go_etcd_io.bbolt.Options.ty))) (Val (PairV #l #v)))
  {{ RET #(); optsAt l (DFrac.own 1) o' }}

/-- `optsAt`'s laws: never nil; a discarded fraction is persistent; fractional. -/
def optsAt_laws.spec [HasExt osFsExt] : Prop :=
  (∀ l dq o, optsAt (GF := GF) l dq o ⊢ ⌜l ≠ Loc.null⌝) ∧
  (∀ l o, Persistent (optsAt (GF := GF) l DFrac.discard o)) ∧
  (∀ l o, optsAt (GF := GF) l (DFrac.own 1) o ⊢ |==> optsAt l DFrac.discard o)

/-- A tracked `bool` field (`ReadOnly`, `Mlock`, `NoSync`): its value and its setter. -/
def optsBoolField (f : GoString) : Option ((OptsM → Bool) × (OptsM → Bool → OptsM)) :=
  if f = go!"ReadOnly" then some (fun o => o.readOnly, fun o b => { o with readOnly := b })
  else if f = go!"Mlock" then some (fun o => o.mlock, fun o b => { o with mlock := b })
  else if f = go!"NoSync" then some (fun o => o.noSync, fun o b => { o with noSync := b })
  else if f = go!"NoFreelistSync" then
    some (fun o => o.noFreelistSync, fun o b => { o with noFreelistSync := b })
  else none

/-- A tracked `int` field (`PageSize`, `MmapFlags`): its value and its setter. -/
def optsIntField (f : GoString) : Option ((OptsM → w64) × (OptsM → w64 → OptsM)) :=
  if f = go!"PageSize" then some (fun o => o.pageSize, fun o b => { o with pageSize := b })
  else if f = go!"MmapFlags" then some (fun o => o.mmapFlags, fun o b => { o with mmapFlags := b })
  else none

/-- The untracked `bool` fields. -/
def optsBoolUntracked : List GoString :=
  [go!"NoGrowSync", go!"PreLoadFreelist", go!"NoStatistics"]

/-- The untracked `int`-like fields (`int`, `time.Duration`). -/
def optsIntUntracked : List GoString :=
  [go!"InitialMmapSize", go!"MaxSize", go!"Timeout"]

/-- **A `bool` field**: read at any fraction (a tracked field gives its value), written with all
of it (a tracked field's setter, an untracked one leaves `o`). -/
def optsAt_bool.spec [HasExt osFsExt] : Prop :=
  ∀ (l : Loc) (dq : DFrac) (o : OptsM) (f : GoString),
    (optsBoolField f).isSome ∨ f ∈ optsBoolUntracked →
    optsAt (GF := GF) l dq o ⊢ ∃ x : Bool,
      structFieldRef go_etcd_io.bbolt.Options f l ↦{dq} x ∗
      ⌜∀ g, optsBoolField f = some g → x = g.1 o⌝ ∗
      ((structFieldRef go_etcd_io.bbolt.Options f l ↦{dq} x -∗ optsAt l dq o) ∧
       (⌜dq = DFrac.own 1⌝ -∗ ∀ y : Bool,
        structFieldRef go_etcd_io.bbolt.Options f l ↦{dq} y -∗
        optsAt l dq (match optsBoolField f with | some g => g.2 o y | none => o)))

/-- **An `int` field** (`int`, `time.Duration`), as `optsAt_bool`. -/
def optsAt_int.spec [HasExt osFsExt] : Prop :=
  ∀ (l : Loc) (dq : DFrac) (o : OptsM) (f : GoString),
    (optsIntField f).isSome ∨ f ∈ optsIntUntracked →
    optsAt (GF := GF) l dq o ⊢ ∃ x : w64,
      structFieldRef go_etcd_io.bbolt.Options f l ↦{dq} x ∗
      ⌜∀ g, optsIntField f = some g → x = g.1 o⌝ ∗
      ((structFieldRef go_etcd_io.bbolt.Options f l ↦{dq} x -∗ optsAt l dq o) ∧
       (⌜dq = DFrac.own 1⌝ -∗ ∀ y : w64,
        structFieldRef go_etcd_io.bbolt.Options f l ↦{dq} y -∗
        optsAt l dq (match optsIntField f with | some g => g.2 o y | none => o)))

/-- **`FreelistType`** (a `string`, untracked). -/
def optsAt_freelist.spec [HasExt osFsExt] : Prop :=
  ∀ (l : Loc) (dq : DFrac) (o : OptsM),
    optsAt (GF := GF) l dq o ⊢ ∃ x : GoString,
      structFieldRef go_etcd_io.bbolt.Options go!"FreelistType" l ↦{dq} x ∗
      ((structFieldRef go_etcd_io.bbolt.Options go!"FreelistType" l ↦{dq} x -∗ optsAt l dq o) ∧
       (⌜dq = DFrac.own 1⌝ -∗ ∀ y : GoString,
        structFieldRef go_etcd_io.bbolt.Options go!"FreelistType" l ↦{dq} y -∗ optsAt l dq o))

/-- **`OpenFile`** (tracked). -/
def optsAt_openFile.spec [HasExt osFsExt] : Prop :=
  ∀ (l : Loc) (dq : DFrac) (o : OptsM),
    optsAt (GF := GF) l dq o ⊢
      structFieldRef go_etcd_io.bbolt.Options go!"OpenFile" l ↦{dq} o.openFile ∗
      ((structFieldRef go_etcd_io.bbolt.Options go!"OpenFile" l ↦{dq} o.openFile -∗ optsAt l dq o) ∧
       (⌜dq = DFrac.own 1⌝ -∗ ∀ y : GoFunc,
        structFieldRef go_etcd_io.bbolt.Options go!"OpenFile" l ↦{dq} y -∗
        optsAt l dq { o with openFile := y }))

/-- **`Logger`** (tracked). -/
def optsAt_logger.spec [HasExt osFsExt] : Prop :=
  ∀ (l : Loc) (dq : DFrac) (o : OptsM),
    optsAt (GF := GF) l dq o ⊢
      structFieldRef go_etcd_io.bbolt.Options go!"Logger" l ↦{dq} o.logger ∗
      ((structFieldRef go_etcd_io.bbolt.Options go!"Logger" l ↦{dq} o.logger -∗ optsAt l dq o) ∧
       (⌜dq = DFrac.own 1⌝ -∗ ∀ y : GoInterface,
        structFieldRef go_etcd_io.bbolt.Options go!"Logger" l ↦{dq} y -∗
        optsAt l dq { o with logger := y }))

end spec

end Bbolt
end EtcdGrove
end Perennial
