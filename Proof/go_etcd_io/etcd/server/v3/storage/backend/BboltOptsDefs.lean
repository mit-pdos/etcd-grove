/-
bbolt's `Options`, the part the backend's package facts need (item 8, 2026-10-17: moved here from
`BboltOptions.lean`, which keeps the rest of the trust boundary, so that the backend's `Base.lean`
can state `boltOpenOptionsOk` in `backendInit`): the model `OptsM` of an `Options` value and the
points-to `optsAt`. (2026-11-17, S2 of `notes/bbolt-integration-plan.md`, D-I4) `Options` is
translated: `optsAt` is bbolt's (`Spec/go_etcd_io/bbolt/Options.lean`), with the two fields bbolt's
`OptsM` tracks beyond the backend's (`Mlock`, `MmapFlags`) left existential; until then an axiom.
-/
module

public import Code.go_etcd_io.etcd.server.v3.storage.backend
public import GeneratedProof.go_etcd_io.bbolt
public import Spec.go_etcd_io.bbolt.Options
public import Perennial.Proof.ProofPrelude

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode

section types
variable [GooseExts]

/-- The part of a bbolt `Options` value that `Open`'s behaviour depends on here: read-only (no
write transaction then), the page size (a new file's pages: `Open` makes a `4 * PageSize` buffer,
so a negative one panics), the `OpenFile` function (called by `Open`; nil: `os.OpenFile`), and
the logger (called by `Open` and later); and (S3e, 2026-11-18) the three fields under which bbolt's
`Open` has no error of its own (`bbolt.optsNoErr`): `Timeout` (a `flock` conflict is retried, not
reported), `NoFreelistSync` (no write transaction at `Open`) and `InitialMmapSize` (what `mmapSize`
accepts). -/
structure OptsM where
  readOnly : Bool
  pageSize : w64
  openFile : GoFunc
  logger : GoInterface
  timeout : w64
  noFreelistSync : Bool
  initialMmapSize : w64

/-- `bolt.Options{}`'s fields. -/
def optsZero : OptsM := ⟨false, W64 0, func.nil, GoInterface.nil, W64 0, false, W64 0⟩

/-- bbolt's `OptsM` of the backend's `o`, with `Mlock` `m` and `MmapFlags` `f`. -/
def OptsM.toBolt (o : OptsM) (m : Bool) (f : w64) : bbolt.OptsM :=
  { readOnly := o.readOnly, pageSize := o.pageSize, openFile := o.openFile, logger := o.logger,
    mlock := m, mmapFlags := f }

end types

section ok
variable [GooseExts] [GoGlobalContext]

/-- The logger is nil, or a value of a pointer type that is a location (batch 38.1 of
`notes/bbolt-proof-plan.md`, user-approved 2026-11-04): bbolt's own `bbolt.loggerPtrOk`
(`Spec/go_etcd_io/bbolt/Options.lean`), restated here because importing bbolt's `Options` module
would make the name `OptsM` ambiguous in the backend's statements. -/
def loggerPtrOk : GoInterface → Prop
  | .nil => True
  | .ok li => ∃ (t : go.GoType) (l : Loc), li.ty = go.GoType.PointerType t ∧ li.v = #l

/-- Options `Open` accepts here: read-write, the default page size, the default `OpenFile`, and
(batch 38.1 of `notes/bbolt-proof-plan.md`, user-approved 2026-11-04) a logger nil or a value of a
pointer type that is a location (`loggerPtrOk`, bbolt's, which its `Open` spec takes: `Open`
compares the logger with `discardLogger`, a pointer comparison). -/
def OptsM.ok (o : OptsM) : Prop :=
  o.readOnly = false ∧ o.pageSize = W64 0 ∧ o.openFile = func.nil ∧ loggerPtrOk o.logger

theorem optsZero_ok : optsZero.ok := ⟨rfl, rfl, rfl, trivial⟩

/-- **Options under which bbolt's `Open` has no error of its own** (S3e, 2026-11-18; bbolt's
`optsNoErr` of the tracked fields): no `Timeout`, `NoFreelistSync`, an `InitialMmapSize` that
`mmapSize` accepts. -/
def OptsM.noErr (o : OptsM) : Prop :=
  o.timeout = W64 0 ∧ o.noFreelistSync = true ∧ sint.Z o.initialMmapSize ≤ 0xFFFFFFFFFFFF

/-- Setting a logger that is `loggerPtrOk` keeps the options acceptable. -/
theorem OptsM.ok_withLogger (o : OptsM) (l : GoInterface) (h : o.ok)
    (hl : loggerPtrOk l) : ({ o with logger := l } : OptsM).ok :=
  ⟨h.1, h.2.1, h.2.2.1, hl⟩

end ok

section preds
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The `Options` value `v` has the fields `o`: bbolt's `optsVal` with `Mlock` false and
`MmapFlags` zero or `MAP_POPULATE` (what bbolt's proved `Open` accepts, `bbolt.OptsM.ok`), and the
fields `Timeout`, `NoFreelistSync`, `InitialMmapSize` (S3e, 2026-11-18: what `bbolt.optsNoErr` asks). -/
def optsVal (v : go_etcd_io.bbolt.Options) (o : OptsM) : Prop :=
  ∃ f : w64, (f.toNat = 0 ∨ f.toNat = bbolt.mapPopulate) ∧ bbolt.optsVal v (o.toBolt false f) ∧
    v.Timeout' = o.timeout ∧ v.NoFreelistSync' = o.noFreelistSync ∧
    v.InitialMmapSize' = o.initialMmapSize

/-- The `Options` at `l`, at fraction `dq`, has the fields `o` (`optsVal`). (S3e: until then bbolt's
`optsAt` at some `Mlock` and `MmapFlags`; before S2 an axiom.) -/
def optsAt (l : Loc) (dq : DFrac) (o : OptsM) : IProp GF :=
  iprop(∃ v : go_etcd_io.bbolt.Options, l ↦{dq} v ∗ ⌜optsVal v o⌝)

instance optsAt_discard_persistent (l : Loc) (o : OptsM) :
    Persistent (optsAt (GF := GF) l DFrac.discard o) := by
  unfold optsAt; infer_instance

/-- The backend's package variable `boltOpenOptions` (`config_linux.go`:
`&bolt.Options{MmapFlags: syscall.MAP_POPULATE, NoFreelistSync: true}`; nil on other systems, but
the file model's configuration is Linux), never written: options `Open` accepts, with
`NoFreelistSync` and no `Timeout` (S3e, 2026-11-18: until then possibly nil). A package-initialization fact (the variable's initializer is translated, `boltOpenOptionsOk_intro`;
until 2026-11-21 names-only, the trust-boundary axiom `boltOpenOptions_init`); part of the backend's package facts (`backendInit`; item 8, 2026-10-17: until then a premise of
the constructor). -/
def boltOpenOptionsOk : IProp GF :=
  iprop(∃ p : Loc,
    globalAddr go_etcd_io.etcd.server.v3.storage.backend.boltOpenOptions ↦□ p ∗
    ∃ o : OptsM, optsAt p DFrac.discard o ∗
      ⌜o.ok ∧ o.noFreelistSync = true ∧ o.timeout = W64 0⌝)

instance boltOpenOptionsOk_persistent : Persistent (boltOpenOptionsOk (GF := GF)) := by
  unfold boltOpenOptionsOk; infer_instance

/-- **`boltOpenOptions`' initializer gives `boltOpenOptionsOk`** (prove-etcdint3, 2026-11-21: the
initializer translated, until then the trust-boundary axiom `boltOpenOptions_init`): the variable
holds, read-only, a pointer to `bolt.Options{MmapFlags: syscall.MAP_POPULATE, NoFreelistSync: true}`
(`config_linux.go`), whose other fields are zero. -/
theorem boltOpenOptionsOk_intro (p : Loc) (v : go_etcd_io.bbolt.Options) :
    ⊢ globalAddr go_etcd_io.etcd.server.v3.storage.backend.boltOpenOptions ↦□ p -∗ p ↦□ v -∗
      ⌜v.ReadOnly' = false ∧ v.PageSize' = W64 0 ∧ v.OpenFile' = func.nil ∧
      v.Logger' = GoInterface.nil ∧ v.Mlock' = false ∧ v.MmapFlags' = W64 32768 ∧
      v.Timeout' = W64 0 ∧ v.NoFreelistSync' = true ∧ v.InitialMmapSize' = W64 0⌝ -∗
      boltOpenOptionsOk (GF := GF) := by
  iintro #Hg #Hp %hv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hv
  unfold boltOpenOptionsOk
  iexists p
  iframe Hg
  iexists { optsZero with noFreelistSync := true }
  unfold optsAt
  isplitr
  · iexists v
    iframe Hp
    ipureintro
    refine ⟨v.MmapFlags', Or.inr (by rw [h6]; decide), ⟨h1, h2, h3, h4, h5, rfl⟩, h7, h8, h9⟩
  ipureintro
  exact ⟨⟨rfl, rfl, rfl, trivial⟩, rfl, rfl⟩

end preds

end backend
end EtcdGrove
end Perennial
