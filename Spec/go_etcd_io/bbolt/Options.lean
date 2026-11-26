/-
bbolt's `Options` as its specs see them (D13, `notes/bbolt-spec-decisions.md`): the part of an
`Options` value `Open` depends on (`OptsM`), the options under which the specs hold (`OptsM.ok`),
and the points-to `optsAt`. (2026-11-17, S2 of `notes/bbolt-integration-plan.md`, D-I4) `Options`
is translated: `optsAt` is the struct's typed points-to with fields `optsVal`, and its laws are
lemmas, in `Proof/go_etcd_io/bbolt/Options.lean` (until then an abstract points-to and
trust-boundary axioms). Part of the API (`etc/api/bbolt.txt`).
-/
module

public import GeneratedProof.go_etcd_io.bbolt
public import Perennial.Proof.ProofPrelude

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

/-- The part of a bbolt `Options` value `Open`'s behaviour depends on here (moved from the
backend's `BboltOptsDefs.lean`). -/
structure OptsM where
  readOnly : Bool
  pageSize : w64
  openFile : GoFunc
  logger : GoInterface
  /-- round 2: `Mlock` reaches `unix.Mlock`/`Munlock`, names-only (a stuck call). -/
  mlock : Bool
  /-- round 2: `mmap` passes `MAP_SHARED | MmapFlags`; OsFs's `Mmap` takes only `MAP_SHARED` and
  `MAP_SHARED | MAP_POPULATE`. -/
  mmapFlags : w64
  -- round 3: round 2's `noFreelistSync` is dropped (no spec reads it; the spare reader slot
  -- covers `freepages` whatever its value: `OptsM.ok`'s docstring).

/-- `bolt.Options{}`'s fields (round 3: restated with the new fields). -/
def optsZero : OptsM :=
  { readOnly := false, pageSize := W64 0, openFile := func.nil, logger := GoInterface.nil,
    mlock := false, mmapFlags := W64 0 }
/-- `syscall.MAP_POPULATE` (Linux). -/
@[word_unfold] def mapPopulate : Nat := 0x8000

/-- The logger is nil or of a pointer type (round 8, review 7 M2): `(*Options).String` formats it
with `%p`, which for a non-pointer-shaped dynamic type falls back to a reflective print that
iterates its maps and reads its slices (racy). A scope restriction of the model; Go accepts any
type. The backend's `*zapBoltLogger` and the nil logger meet it.

Batch 38.1 (user-approved 2026-11-04, `notes/bbolt-spec-decisions.md`): the pointer-typed value is
a location. The model's interface values pair a type with any value, so "of a pointer type" alone
does not say so; `Open` stores the logger and bbolt compares it with `discardLogger` (`lg !=
discardLogger`), a pointer comparison, which needs it (`dbFixed`'s `logPtrTyped`). -/
def loggerPtrOk : GoInterface → Prop
  | .nil => True
  | .ok li => ∃ (t : go.GoType) (l : Loc), li.ty = go.GoType.PointerType t ∧ li.v = #l

/-- Options `Open` accepts here:
- read-write (a read-only database has no write transaction);
- the default page size (`nonissues/bbolt-large-page-size.md`: from about 1 MiB `Commit`
  panics);
- the default `OpenFile` (round 6 margin: this excludes etcd's `defrag`, which reopens the
  temporary database with an `OpenFile` of its own, `backend.go:521-534`. `defrag` is names-only,
  not verified: its bbolt calls rest on no spec here, and a later proof of it needs `OptsM.ok` to
  admit a custom `OpenFile` with a contract over OsFs, the user's decision then);
- round 2, scope restrictions of the model, not of Go: `Mlock` off (its system calls are not
  modelled) and `MmapFlags` `0` or `MAP_POPULATE` (the flags OsFs's `Mmap` models). The backend
  meets the second (`MAP_POPULATE`, `config_linux.go`) and needs `Config.Mlock = false` for the
  first (`notes/bbolt-spec-decisions.md`, D13).
The other fields change no outcome the specs state: `NoSync`/`NoGrowSync` only durability;
`InitialMmapSize` (etcd's 10 GiB) at worst an `mmap` error, which OsFs always allows; `Timeout`
a `flock` that loops or fails (OsFs's `Flock` returns any errno); `NoFreelistSync` only
`Commit`'s error path (`freepages`: a read transaction on `isBolt`'s spare reader slot, and a
`recursivelyCheckBucket` that finds nothing in a well-formed tree); `FreelistType` the
freelist's implementation (both proved in the old branch). -/
def OptsM.ok (o : OptsM) : Prop :=
  o.readOnly = false ∧ o.pageSize = W64 0 ∧ o.openFile = func.nil ∧ o.mlock = false ∧
    (o.mmapFlags.toNat = 0 ∨ o.mmapFlags.toNat = mapPopulate) ∧ loggerPtrOk o.logger

omit [GooseSemantics] [GooseInterp] in
theorem optsZero_ok : optsZero.ok := by
  simp [OptsM.ok, optsZero, loggerPtrOk]

/-- The `Options` value `v` has the fields `o` (2026-11-17: a definition over the translated
struct; until then an axiom). -/
def optsVal (v : go_etcd_io.bbolt.Options) (o : OptsM) : Prop :=
  v.ReadOnly' = o.readOnly ∧ v.PageSize' = o.pageSize ∧ v.OpenFile' = o.openFile ∧
    v.Logger' = o.logger ∧ v.Mlock' = o.mlock ∧ v.MmapFlags' = o.mmapFlags

/-- The `Options` at `l`, at fraction `dq`, has the fields `o` (and some others): its typed
points-to (2026-11-17: until then abstract). -/
def optsAt (l : Loc) (dq : DFrac) (o : OptsM) : IProp GF :=
  iprop(∃ v : go_etcd_io.bbolt.Options, l ↦{dq} v ∗ ⌜optsVal v o⌝)

/-- **Options under which `Open` cannot fail but for the environment** (session S3f,
`Open.spec`): no `Timeout` (a `flock` conflict is retried forever, not reported as
`ErrTimeout`), `NoFreelistSync` (no write transaction at `Open` for a file without a synced
freelist), and an `InitialMmapSize` that `mmapSize` accepts (at most `maxMapSize`). etcd's backend
sets `NoFreelistSync` (`boltOpenOptions`, `config_linux.go`), `Timeout` from its config (`0` unless
`WithTimeout`) and `InitialMmapSize` 10 GiB by default. -/
def optsNoErr (v : go_etcd_io.bbolt.Options) : Prop :=
  v.Timeout' = W64 0 ∧ v.NoFreelistSync' = true ∧ sint.Z v.InitialMmapSize' ≤ 0xFFFFFFFFFFFF

/-- The `Options` at `l` has the fields `o` and is `optsNoErr` (session S3f). -/
def optsAtNoErr (l : Loc) (dq : DFrac) (o : OptsM) : IProp GF :=
  iprop(∃ v : go_etcd_io.bbolt.Options, l ↦{dq} v ∗ ⌜optsVal v o ∧ optsNoErr v⌝)

/-- **Options under which `Open` puts its file in crash mode** (W6, `Open.specC`): `optsNoErr`, and
`NoSync` and `NoGrowSync` off, so that every commit syncs (what `boltSyncs` records). etcd's backend
sets both off unless `UnsafeNoFsync`. -/
def optsSyncs (v : go_etcd_io.bbolt.Options) : Prop :=
  optsNoErr v ∧ v.NoSync' = false ∧ v.NoGrowSync' = false

/-- The `Options` at `l` has the fields `o` and is `optsSyncs` (W6). -/
def optsAtSyncs (l : Loc) (dq : DFrac) (o : OptsM) : IProp GF :=
  iprop(∃ v : go_etcd_io.bbolt.Options, l ↦{dq} v ∗ ⌜optsVal v o ∧ optsSyncs v⌝)

theorem optsAtNoErr_optsAt (l : Loc) (dq : DFrac) (o : OptsM) :
    optsAtNoErr (GF := GF) l dq o ⊢ optsAt l dq o := by
  unfold optsAtNoErr optsAt
  iintro ⟨%v, Hv, %h⟩
  iexists v; iframe Hv; ipureintro; exact h.1

instance optsAt_discard_persistent (l : Loc) (o : OptsM) :
    Persistent (optsAt (GF := GF) l DFrac.discard o) := by
  unfold optsAt; infer_instance

end spec

end bbolt
end EtcdGrove
end Perennial
