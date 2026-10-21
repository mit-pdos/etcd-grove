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
variable [FfiSyntax]

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

/-- Options `Open` accepts here: read-write, the default page size, the default `OpenFile`. -/
def OptsM.ok (o : OptsM) : Prop := o.readOnly = false ∧ o.pageSize = W64 0 ∧ o.openFile = func.nil

theorem optsZero_ok : optsZero.ok := ⟨rfl, rfl, rfl⟩

end types

section preds
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
