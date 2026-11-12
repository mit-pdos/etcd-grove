/-
bbolt's `Options`, the part the backend's package facts need (item 8, 2026-10-17: moved here from
`BboltOptions.lean`, which keeps the rest of the trust boundary, so that the backend's `Base.lean`
can state `boltOpenOptionsOk` in `backendInit`): the model `OptsM` of an `Options` value and the
abstract points-to `optsAt` (an axiom: `Options` is a type Goose does not translate; see
`BboltOptions.lean`).
-/
module

public import Code.go_etcd_io.etcd.server.v3.storage.backend
public import GeneratedProof.go_etcd_io.bbolt
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
the logger (called by `Open` and later). -/
structure OptsM where
  readOnly : Bool
  pageSize : w64
  openFile : GoFunc
  logger : GoInterface

/-- `bolt.Options{}`'s fields. -/
def optsZero : OptsM := ⟨false, W64 0, func.nil, GoInterface.nil⟩

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

/-- The `Options` at `l`, at fraction `dq`, has the fields `o`. -/
axiom optsAt (l : Loc) (dq : DFrac) (o : OptsM) : IProp GF

@[instance] axiom optsAt_discard_persistent (l : Loc) (o : OptsM) :
  Persistent (optsAt (GF := GF) l DFrac.discard o)

/-- The backend's package variable `boltOpenOptions` (`config_linux.go`:
`&bolt.Options{MmapFlags: syscall.MAP_POPULATE}`; nil on other systems), never written: nil, or
options `Open` accepts. A package-initialization fact (the variable's initializer is names-only:
`syscall.MAP_POPULATE` is not translated); part of the backend's package facts (`backendInit`; item 8, 2026-10-17: until then a premise of
the constructor). -/
def boltOpenOptionsOk : IProp GF :=
  iprop(∃ p : Loc,
    globalAddr go_etcd_io.etcd.server.v3.storage.backend.boltOpenOptions ↦□ p ∗
    (⌜p = Loc.null⌝ ∨ ∃ o : OptsM, optsAt p DFrac.discard o ∗ ⌜o.ok⌝))

instance boltOpenOptionsOk_persistent : Persistent (boltOpenOptionsOk (GF := GF)) := by
  unfold boltOpenOptionsOk; infer_instance

end preds

end backend
end EtcdGrove
end Perennial
