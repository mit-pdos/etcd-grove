/-
Lean-first (no Rocq counterpart).

# The compactor registry: `etcd3`'s package fact (Q1 (c) of `notes/k8s-compactor-plan.md`)

`compact.go`'s package variables `endpointsMapMu` and `endpointsMap` (made by its `init()`) map
each endpoint to the compactor `StartCompactorPerEndpoint` started for it: one compactor per
process and cluster, the cluster told by its endpoints.

* **The registry's name** (`CompactorRegistry`): a class holding the ghost name of the endpoint
  claims. The adequacy theorem of a program importing `etcd3` allocates the claims' authority
  (`regAuth γ ∅`, which `Main` receives) and instantiates the class with its name, before the
  package's initializer runs; the initializer builds the lock invariant at the class's name. So
  `Main`'s claims and the package fact speak of one registry, by construction: a package fact is
  persistent and cannot hand out the exclusive authority, and names allocated in two places never
  agree (`notes/decisions.md`, "The compactor registry's name").
* **A claim** (`epClaim ep Ψ`, persistent, agreeing): endpoint `ep` belongs to a cluster whose
  compactors satisfy `Ψ` (over the compactor, its client and its revision's ghost name). It
  is a saved predicate, not the cluster's `KVNames`, which are not countable (ghost maps store
  countable values).
* **The lock invariant** (`registryInv`): `endpointsMap` holds a map whose every entry `ep ↦ c`
  carries a claim of `ep` and its predicate of `c` (persistently: compactors are persistent).
* **The package fact** (`registryFact`): `endpointsMapMu` is a mutex over it.
-/
module

public import GeneratedProof.k8s_io.apiserver.pkg.storage.etcd3
public import Perennial.Proof.sync.Base
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.SavedProp
public import Perennial.Golang.Theory.Map

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI

/-- **The compactor registry's ghost name** (see the file header): the adequacy theorem of a program
importing `etcd3` allocates it and instantiates the class. -/
class CompactorRegistry : Type where
  /-- The ghost map of the endpoint claims (endpoint to the name of its saved predicate). -/
  γreg : GName

/-- What a claim's predicate is about: a compactor, its client, and its revision's ghost name
(`CompactorNames.lb`). -/
abbrev CompactorId : Type := Loc × Loc × GName

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [reg : CompactorRegistry]

/-- **The claims' authority** at the claimed endpoints `M` (exclusive): what `Main` receives,
at `∅`, from the adequacy theorem. -/
def regAuth (M : GMap GoString GName) : IProp GF :=
  ghostMapAuth (K := GoString) (V := GName) reg.γreg 1 M

/-- **Endpoint `ep` is claimed for the compactors satisfying `Ψ`** (persistent; see the file
header). -/
def epClaim (ep : GoString) (Ψ : CompactorId → IProp GF) : IProp GF :=
  iprop(∃ γa : GName, ghostMapElem (K := GoString) reg.γreg ep DFrac.discard γa ∗
    savedPredOwn γa DFrac.discard Ψ)

instance epClaim_persistent (ep : GoString) (Ψ : CompactorId → IProp GF) :
    Persistent (epClaim ep Ψ) := by
  unfold epClaim; infer_instance

/-- **The registry's lock invariant** (see the file header). -/
def registryInv : IProp GF :=
  iprop(∃ (mref : Loc) (m : GMap GoString Loc),
    globalAddr k8s_io.apiserver.pkg.storage.etcd3.endpointsMap ↦ mref ∗ mref ↦$ m ∗
    [∗map] ep ↦ c ∈ m, ∃ (Ψ : CompactorId → IProp GF) (x : CompactorId),
      epClaim ep Ψ ∗ ⌜x.1 = c⌝ ∗ □ Ψ x)

/-- **`etcd3`'s package fact** (see the file header). -/
def registryFact : IProp GF :=
  sync.isMutex (globalAddr k8s_io.apiserver.pkg.storage.etcd3.endpointsMapMu) registryInv

instance registryFact_persistent : Persistent (registryFact (GF := GF)) := by
  unfold registryFact; infer_instance

end defs

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [reg : CompactorRegistry]

/-- **Claim an endpoint not yet claimed**, for the compactors satisfying `Ψ`. -/
theorem epClaim_alloc (M : GMap GoString GName) (ep : GoString) (Ψ : CompactorId → IProp GF)
    (h : M.lookup ep = none) :
    regAuth M ⊢ |==> ∃ γa, regAuth (M.insert ep γa) ∗ epClaim ep Ψ := by
  iintro HA
  imod saved_pred_alloc Ψ DFrac.discard DFrac.valid_discard with ⟨%γa, #HΨ⟩
  iunfold regAuth at HA
  imod ghost_map_insert_persist ep γa h $$ HA with ⟨HA, #He⟩
  imodintro
  iexists γa
  iunfold regAuth
  iframe HA
  iunfold epClaim
  iexists γa
  isplit
  · iexact He
  · iexact HΨ

/-- **Two claims of one endpoint agree** (a later on): what one's predicate says of a compactor,
the other's says. -/
theorem epClaim_agree (ep : GoString) (Ψ1 Ψ2 : CompactorId → IProp GF) (x : CompactorId) :
    epClaim ep Ψ1 ⊢ epClaim ep Ψ2 -∗ ▷ Ψ1 x -∗ ▷ Ψ2 x := by
  iintro #H1 #H2 HP
  iunfold epClaim at H1 H2
  icases H1 with ⟨%γ1, #He1, #HΨ1⟩
  icases H2 with ⟨%γ2, #He2, #HΨ2⟩
  ihave %Hγ := ghostMapElem_agree ep reg.γreg DFrac.discard DFrac.discard γ1 γ2 $$ He1 He2
  subst Hγ
  ihave #Heq := saved_pred_agree γ1 DFrac.discard DFrac.discard Ψ1 Ψ2 x $$ HΨ1 HΨ2
  inext
  ihave Hiff := internalEq_iff _ _ $$ Heq
  icases Hiff with ⟨Hiff, -⟩
  iapply Hiff $$ HP

end laws

end k8s
end EtcdGrove
end Perennial
