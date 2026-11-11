/-
bbolt's `Options` axioms: the trust boundary over a type Goose does not translate (the frozen
spec of 2026-11-03, `notes/bbolt-spec-decisions.md`, D13).

**Why axioms.** `bolt.Options` (`db.go`) stays axiomatized in the translation (`translate = ["*",
"!Options", "!DefaultOptions"]`, `notes/bbolt-v2-infra.md`): a translated struct makes
`wp_auto` run its literal itself, bypassing these axioms, and translating it belongs with `Open`'s
proof, when these axioms become lemmas of the struct. Its generated instances are `sorry --
axiomatized type`, which no result may use. So the operations clients and `Open` perform on an
`Options` (the literal, allocation, whole loads and stores, field reads and stores) are stated
here over the abstract points-to `optsAt` (`Spec/go_etcd_io/bbolt/Options.lean`), for the part of
the value `Open` depends on (`OptsM`). Each is true of Go: the struct's fields and their types are
`db.go`'s, and a composite literal `bolt.Options{}` is the zero value.

**D13** (the user's decision): `OptsM` tracks `mlock` and `mmapFlags` too (`OptsM.ok` excludes
`Mlock` and `MmapFlags` other than `0` or `MAP_POPULATE`, scope restrictions of the model), so
`optsAt_bool` and `optsAt_int` no longer cover them, and `optsAt_mlock`/`optsAt_mmapFlags` set
them. `optsVal`, `wp_optsLit`, `wp_optsAlloc`, `wp_optsLoad`, `wp_optsStore`, `optsAt_freelist`,
`optsAt_timeout`, `optsAt_logger` and `optsAt_discard_persistent` are the backend's
(`Proof/go_etcd_io/etcd/server/v3/storage/backend/BboltOptions.lean`, `BboltOptsDefs.lean`),
copied over `bbolt.OptsM`; the backend keeps its own copies until the backend switch. The read
axioms (`optsAt_*_rd`) and `optsAt_nonnull` are what `Open` needs.
-/
module

public import Spec.go_etcd_io.bbolt.Options

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section axioms
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The `Options` value `v` has the fields `o`. -/
axiom optsVal (v : go_etcd_io.bbolt.Options) (o : OptsM) : Prop

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

@[instance] axiom optsAt_discard_persistent (l : Loc) (o : OptsM) :
  Persistent (optsAt (GF := GF) l DFrac.discard o)

/-! ### The option axioms (trust boundary: `Options` is axiomatized; moved from the backend's
`BboltOptions.lean` and, round 3, **restated** for `OptsM`'s new fields; trusted, so D13's to
approve). `optsVal`, `wp_optsLit` (now giving `optsZero` above), `wp_optsAlloc`, `wp_optsLoad`,
`wp_optsStore`, `optsAt_freelist`, `optsAt_timeout`, `optsAt_logger` and
`optsAt_discard_persistent` (round 4: `boltOpenOptionsOk` needs it) are moved unchanged.
`Options` and `DefaultOptions`' initializer stay axiomatized until `Open`'s proof, as the
infrastructure keeps them (`notes/bbolt-v2-infra.md` on `worktree-bbolt-v2`); these axioms then
become lemmas of the translated struct.

Round 4 adds what `Open` itself needs (review 3, finding 2): `Open` reads every field through
`options.F` (a field reference and a typed load, `Code/go_etcd_io/bbolt.lean`'s `Open`), at the
fraction the caller lends (`boltOpenOptionsOk` holds a discarded one), and branches on
`options == nil`. -/

/-- An `Options` the axioms describe is never nil. Its producers are `wp_optsAlloc` (an
allocation) and the backend's trusted `boltOpenOptions_init` (`&bolt.Options{...}`, a composite
literal's address: `optsAt p DFrac.discard o`); both give non-nil locations (round 6 docstring). -/
axiom optsAt_nonnull (l : Loc) (dq : DFrac) (o : OptsM) :
  optsAt (GF := GF) l dq o ⊢ ⌜l ≠ Loc.null⌝

/-- Reading a tracked field at any fraction gives its `OptsM` value (round 4). One axiom per
field, by its Go type: -/
axiom optsAt_readOnly_rd (l : Loc) (dq : DFrac) (o : OptsM) :
  optsAt (GF := GF) l dq o ⊢ ∃ dq' : DFrac,
    structFieldRef go_etcd_io.bbolt.Options go!"ReadOnly" l ↦{dq'} o.readOnly ∗
    (structFieldRef go_etcd_io.bbolt.Options go!"ReadOnly" l ↦{dq'} o.readOnly -∗ optsAt l dq o)
axiom optsAt_mlock_rd (l : Loc) (dq : DFrac) (o : OptsM) :
  optsAt (GF := GF) l dq o ⊢ ∃ dq' : DFrac,
    structFieldRef go_etcd_io.bbolt.Options go!"Mlock" l ↦{dq'} o.mlock ∗
    (structFieldRef go_etcd_io.bbolt.Options go!"Mlock" l ↦{dq'} o.mlock -∗ optsAt l dq o)
axiom optsAt_pageSize_rd (l : Loc) (dq : DFrac) (o : OptsM) :
  optsAt (GF := GF) l dq o ⊢ ∃ dq' : DFrac,
    structFieldRef go_etcd_io.bbolt.Options go!"PageSize" l ↦{dq'} o.pageSize ∗
    (structFieldRef go_etcd_io.bbolt.Options go!"PageSize" l ↦{dq'} o.pageSize -∗ optsAt l dq o)
axiom optsAt_mmapFlags_rd (l : Loc) (dq : DFrac) (o : OptsM) :
  optsAt (GF := GF) l dq o ⊢ ∃ dq' : DFrac,
    structFieldRef go_etcd_io.bbolt.Options go!"MmapFlags" l ↦{dq'} o.mmapFlags ∗
    (structFieldRef go_etcd_io.bbolt.Options go!"MmapFlags" l ↦{dq'} o.mmapFlags -∗ optsAt l dq o)
axiom optsAt_openFile_rd (l : Loc) (dq : DFrac) (o : OptsM) :
  optsAt (GF := GF) l dq o ⊢ ∃ dq' : DFrac,
    structFieldRef go_etcd_io.bbolt.Options go!"OpenFile" l ↦{dq'} o.openFile ∗
    (structFieldRef go_etcd_io.bbolt.Options go!"OpenFile" l ↦{dq'} o.openFile -∗ optsAt l dq o)
axiom optsAt_logger_rd (l : Loc) (dq : DFrac) (o : OptsM) :
  optsAt (GF := GF) l dq o ⊢ ∃ dq' : DFrac,
    structFieldRef go_etcd_io.bbolt.Options go!"Logger" l ↦{dq'}
      (o.logger : go_etcd_io.bbolt.Logger) ∗
    (structFieldRef go_etcd_io.bbolt.Options go!"Logger" l ↦{dq'}
      (o.logger : go_etcd_io.bbolt.Logger) -∗ optsAt l dq o)

/-- Reading an untracked `bool` field at any fraction: some value (round 4; round 5: one axiom
per Go type, `db.go`'s declarations, in place of a type-generic placeholder). -/
axiom optsAt_bool_rd (l : Loc) (dq : DFrac) (o : OptsM) (f : GoString)
    (hf : f = go!"NoGrowSync" ∨ f = go!"NoFreelistSync" ∨ f = go!"PreLoadFreelist" ∨
      f = go!"NoSync" ∨ f = go!"NoStatistics") :
  optsAt (GF := GF) l dq o ⊢ ∃ (dq' : DFrac) (x : Bool),
    structFieldRef go_etcd_io.bbolt.Options f l ↦{dq'} x ∗
    (structFieldRef go_etcd_io.bbolt.Options f l ↦{dq'} x -∗ optsAt l dq o)

/-- Reading an untracked `int` field (`InitialMmapSize`, `MaxSize`) at any fraction. -/
axiom optsAt_int_rd (l : Loc) (dq : DFrac) (o : OptsM) (f : GoString)
    (hf : f = go!"InitialMmapSize" ∨ f = go!"MaxSize") :
  optsAt (GF := GF) l dq o ⊢ ∃ (dq' : DFrac) (x : w64),
    structFieldRef go_etcd_io.bbolt.Options f l ↦{dq'} x ∗
    (structFieldRef go_etcd_io.bbolt.Options f l ↦{dq'} x -∗ optsAt l dq o)

/-- Reading `FreelistType` at any fraction. -/
axiom optsAt_freelist_rd (l : Loc) (dq : DFrac) (o : OptsM) :
  optsAt (GF := GF) l dq o ⊢ ∃ (dq' : DFrac) (x : go_etcd_io.bbolt.FreelistType),
    structFieldRef go_etcd_io.bbolt.Options go!"FreelistType" l ↦{dq'} x ∗
    (structFieldRef go_etcd_io.bbolt.Options go!"FreelistType" l ↦{dq'} x -∗ optsAt l dq o)

/-- Reading `Timeout` at any fraction. -/
axiom optsAt_timeout_rd (l : Loc) (dq : DFrac) (o : OptsM) :
  optsAt (GF := GF) l dq o ⊢ ∃ (dq' : DFrac) (x : time.Duration),
    structFieldRef go_etcd_io.bbolt.Options go!"Timeout" l ↦{dq'} x ∗
    (structFieldRef go_etcd_io.bbolt.Options go!"Timeout" l ↦{dq'} x -∗ optsAt l dq o)


/-- A `bool` field other than `ReadOnly` and `Mlock` (`NoGrowSync`, `NoFreelistSync`,
`PreLoadFreelist`, `NoSync`, `NoStatistics`): storing it keeps `o`. (Round 3: `Mlock` moved out.) -/
axiom optsAt_bool (l : Loc) (o : OptsM) (f : GoString)
    (hf : f = go!"NoGrowSync" ∨ f = go!"NoFreelistSync" ∨ f = go!"PreLoadFreelist" ∨
      f = go!"NoSync" ∨ f = go!"NoStatistics") :
  optsAt (GF := GF) l (DFrac.own 1) o ⊢
    ∃ x : Bool, structFieldRef go_etcd_io.bbolt.Options f l ↦ x ∗
      (∀ y : Bool, structFieldRef go_etcd_io.bbolt.Options f l ↦ y -∗ optsAt l (DFrac.own 1) o)

/-- The `Mlock` field (round 3): it holds `o.mlock`; storing it sets it. -/
axiom optsAt_mlock (l : Loc) (o : OptsM) :
  optsAt (GF := GF) l (DFrac.own 1) o ⊢
    structFieldRef go_etcd_io.bbolt.Options go!"Mlock" l ↦ o.mlock ∗
      (∀ y : Bool, structFieldRef go_etcd_io.bbolt.Options go!"Mlock" l ↦ y -∗
        optsAt l (DFrac.own 1) { o with mlock := y })

/-- An `int` field other than `PageSize` and `MmapFlags` (`InitialMmapSize`, `MaxSize`): storing
it keeps `o`. (Round 3: `MmapFlags` moved out.) -/
axiom optsAt_int (l : Loc) (o : OptsM) (f : GoString)
    (hf : f = go!"InitialMmapSize" ∨ f = go!"MaxSize") :
  optsAt (GF := GF) l (DFrac.own 1) o ⊢
    ∃ x : w64, structFieldRef go_etcd_io.bbolt.Options f l ↦ x ∗
      (∀ y : w64, structFieldRef go_etcd_io.bbolt.Options f l ↦ y -∗ optsAt l (DFrac.own 1) o)

/-- The `MmapFlags` field (round 3): it holds `o.mmapFlags`; storing it sets it. -/
axiom optsAt_mmapFlags (l : Loc) (o : OptsM) :
  optsAt (GF := GF) l (DFrac.own 1) o ⊢
    structFieldRef go_etcd_io.bbolt.Options go!"MmapFlags" l ↦ o.mmapFlags ∗
      (∀ y : w64, structFieldRef go_etcd_io.bbolt.Options go!"MmapFlags" l ↦ y -∗
        optsAt l (DFrac.own 1) { o with mmapFlags := y })

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

end axioms

end bbolt
end EtcdGrove
end Perennial
