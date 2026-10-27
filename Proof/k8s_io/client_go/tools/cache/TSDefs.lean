/-
The thread-safe store (`threadSafeMap`, `tools/cache/thread_safe_store.go`): its lock predicate, its
abstract state and the predicates its specs are stated with. Lean-first.

* `storeSt γ σ`: half of the abstract state `σ` (`St`: items, resource version, indexers), the
  client's; the other half is spread over the store's `RWMutex` (`tsP`, at `q.half` for fraction
  `q`), so a writer (`P 1`) and the client's half update it together, and a reader's share
  (`P rfrac`) agrees with it.
* `tsP q`: the lock's resource: the fields `items`, `rv`, the indices, the indexers' map, at `q`,
  with a ghost mirror of their physical layout (`Ph`) so that shares agree; for good, the
  indexers' contracts (`fnsOk`), each item `nil` or meeting `OK`, and the indices exact for the
  items (`ixOk`).
* `isTS c γ OK Fam`: the store `c` (persistent): its static fields (the `storeIndex` and its
  `indexers` field, the metrics' gauge, which meets `gaugeOk`) and the lock's guard.
* `tsReader c γ OK Fam`: one of the lock's reader slots (`RLock` needs one).

`OK` is the client's contract on objects (persistent), `Fam` its family of index functions'
contracts (`St.fns`; `StoreDefs.lean`'s `Fn`).
-/
module

public import Proof.k8s_io.client_go.tools.cache.StoreDefs
public import Perennial.Proof.sync.Link
public import Perennial.ProgramLogic.AtomicFupd

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

/-- The store's ghost names and static locations: the abstract state's and the physical
layout's ghost variables, its `storeIndex` and the `indexers` map. -/
structure TsNames where
  st : GName
  ph : GName
  idx : Loc
  im : Loc

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- The store's physical layout: the items' map, the indices' map, the indices, the indexers. -/
structure Ph where
  il : Loc
  ip : Loc
  ix : Ix
  fv : GMap GoString GoFunc

instance Ph.countable : Pos.Countable Ph :=
  .ofInjective (fun p => Pos.Countable.encode (p.il, p.ip, p.ix, p.fv)) (by
    rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h
    simp only [Pos.encode_eq_iff, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    rfl)

/-- The client's half of the abstract state. -/
def storeSt (γ : TsNames) (σ : St) : IProp GF := ghostVar γ.st (1 : Qp).half σ

/-- The physical state at fraction `q`. -/
def tsPhys (c : Loc) (γ : TsNames) (σ : St) (ph : Ph) (q : Qp) : IProp GF :=
  iprop(structFieldRef threadSafeMap go!"items" c ↦{DFrac.own q} ph.il ∗
    ph.il ↦${DFrac.own q} σ.items ∗
    structFieldRef threadSafeMap go!"rv" c ↦{DFrac.own q} σ.rv ∗
    structFieldRef storeIndex go!"indices" γ.idx ↦{DFrac.own q} ph.ip ∗
    ownIx ph.ip (DFrac.own q) ph.ix ∗
    γ.im ↦${DFrac.own q} ph.fv)

/-- What holds for good of the state: the indexers' contracts, the items' (`nil` or `OK`), and
the items' recorded index values `iv` (`itemsIv`). -/
def tsPers (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF) (σ : St) (ph : Ph) (iv : IV) :
    IProp GF :=
  iprop(fnsOk OK ph.fv (σ.fns Fam) ∗ ([∗map] _k ↦ o ∈ σ.items, okNil OK o) ∗
    itemsIv (σ.fns Fam) σ.items iv)

instance tsPers_persistent (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF) (σ : St) (ph : Ph)
    (iv : IV) : Persistent (tsPers OK Fam σ ph iv) := by
  unfold tsPers; infer_instance

/-- **The store's lock predicate** at fraction `q`: the items' index values `iv` are recorded here
(each share has its own record; all are exact for the same indices, so they agree where it
matters), the indices exact for them (`ixOk`), none for absent or `nil` items (`ivWf`). -/
def tsP (c : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF) (q : Qp) :
    IProp GF :=
  iprop(∃ (σ : St) (ph : Ph) (iv : IV), ghostVar γ.st q.half σ ∗ ghostVar γ.ph q ph ∗
    tsPhys c γ σ ph q ∗ tsPers OK Fam σ ph iv ∗
    ⌜ixOk (σ.fns Fam) iv ph.ix ∧ ivWf (σ.fns Fam) σ.items iv⌝)

attribute [local instance] ownMap_fractional

instance ownIxN_fractional (l : Loc) (X : IxN) :
    Fractional (fun q => ownIxN (GF := GF) l (DFrac.own q) X) := by
  unfold ownIxN; infer_instance

instance ownIx_fractional (l : Loc) (ix : Ix) :
    Fractional (fun q => ownIx (GF := GF) l (DFrac.own q) ix) := by
  unfold ownIx; infer_instance

instance tsPhys_fractional (c : Loc) (γ : TsNames) (σ : St) (ph : Ph) :
    Fractional (fun q => tsPhys (GF := GF) c γ σ ph q) := by
  have h1 := fun (l : Loc) (v : Loc) =>
    fractional_of_dfractional (fun dq => typedPointsto (GF := GF) l v dq)
  have h2 := fun (l : Loc) (v : GoString) =>
    fractional_of_dfractional (fun dq => typedPointsto (GF := GF) l v dq)
  unfold tsPhys; infer_instance

instance tsP_fractional (c : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF) :
    Fractional (tsP (GF := GF) c γ OK Fam) where
  fractional q1 q2 := by
    have hph := fun (σ : St) (ph : Ph) => (tsPhys_fractional (GF := GF) c γ σ ph).fractional q1 q2
    have hst := fun (σ : St) => (ghostVar_half_fractional (GF := GF) γ.st σ).fractional q1 q2
    have hgp := fun (ph : Ph) => (ghostVar_fractional (GF := GF) γ.ph ph).fractional q1 q2
    unfold tsP
    refine ⟨?_, ?_⟩
    · iintro ⟨%σ, %ph, %iv, Hst, Hgp, Hph, #Hpers, %Hok⟩
      icases (hst σ).1 $$ Hst with ⟨Hst1, Hst2⟩
      icases (hgp ph).1 $$ Hgp with ⟨Hgp1, Hgp2⟩
      icases (hph σ ph).1 $$ Hph with ⟨Hph1, Hph2⟩
      isplitl [Hst1 Hgp1 Hph1]
      · iexists σ, ph, iv; iframe; iframe #; ipureintro; exact Hok
      · iexists σ, ph, iv; iframe; iframe #; ipureintro; exact Hok
    · iintro ⟨⟨%σ, %ph, %iv, Hst1, Hgp1, Hph1, #Hpers, %Hok⟩,
        ⟨%σ', %ph', %iv', Hst2, Hgp2, Hph2, -, -⟩⟩
      icombine Hst1 Hst2 gives % ⟨_, hσ⟩
      icombine Hgp1 Hgp2 gives % ⟨_, hp⟩
      subst hσ hp
      iexists σ, ph, iv
      isplitl [Hst1 Hst2]
      · iapply (hst σ).2; iframe
      isplitl [Hgp1 Hgp2]
      · iapply (hgp ph).2; iframe
      isplitl [Hph1 Hph2]
      · iapply (hph σ ph).2; iframe
      iframe #
      ipureintro; exact Hok

/-- A gauge's contract: `Set` returns. -/
def gaugeOk (g : GaugeMetric) : IProp GF :=
  match g with
  | .nil => iprop(False)
  | .ok i => iprop(∀ x : w64, {{ True }} (App (Val #(methods i.ty go!"Set" i.v)) (Val #x))
      {{ RET #(); True }})

instance gaugeOk_persistent (g : GaugeMetric) : Persistent (gaugeOk (GF := GF) g) := by
  cases g <;> unfold gaugeOk <;> infer_instance

/-- **The store** (persistent). -/
def isTS (c : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF) : IProp GF :=
  iprop(∃ (mp : Loc) (g : GaugeMetric),
    structFieldRef threadSafeMap go!"index" c ↦□ γ.idx ∗
    structFieldRef storeIndex go!"indexers" γ.idx ↦□ γ.im ∗
    structFieldRef threadSafeMap go!"metrics" c ↦□ mp ∗
    structFieldRef storeMetrics go!"storeResourceVersion" mp ↦□ g ∗ gaugeOk g ∗
    sync.isRWMutexGuard (structFieldRef threadSafeMap go!"lock" c) (tsP c γ OK Fam))

instance isTS_persistent (c : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF) :
    Persistent (isTS (GF := GF) c γ OK Fam) := by
  unfold isTS; infer_instance

open Iris.ProofMode in
/-- **A reader's linearization point**: the lock's share of the abstract state agrees with the
client's, which the atomic update gets back unchanged. -/
theorem storeSt_peek (γ : TsNames) (q : Qp) (σ : St) (K : St → IProp GF) :
    ghostVar γ.st q σ ∗
      (|={⊤ \ ∅, ∅}=> ∃ σ', storeSt γ σ' ∗ (storeSt γ σ' ={∅, ⊤ \ ∅}=∗ K σ')) ⊢
      |={⊤}=> ghostVar γ.st q σ ∗ K σ := by
  iintro ⟨Hst, HAU⟩
  rw [Iris.Std.LawfulSet.diff_empty]
  imod HAU with ⟨%σ', Hst', Hcl⟩
  iunfold storeSt at Hst'
  icombine Hst Hst' gives % ⟨_, heq⟩
  subst heq
  imod Hcl $$ [Hst'] with HK
  · iunfold storeSt; iexact Hst'
  imodintro
  iframe

open Iris.ProofMode in
/-- **A writer's linearization point**: with the lock's half (`P 1`), the abstract state becomes
`f σ`. -/
theorem storeSt_update (γ : TsNames) (σ : St) (f : St → St) (K : St → IProp GF) :
    ghostVar γ.st (1 : Qp).half σ ∗
      (|={⊤ \ ∅, ∅}=> ∃ σ', storeSt γ σ' ∗ (storeSt γ (f σ') ={∅, ⊤ \ ∅}=∗ K σ')) ⊢
      |={⊤}=> ghostVar γ.st (1 : Qp).half (f σ) ∗ K σ := by
  iintro ⟨Hst, HAU⟩
  rw [Iris.Std.LawfulSet.diff_empty]
  imod HAU with ⟨%σ', Hst', Hcl⟩
  iunfold storeSt at Hst'
  icombine Hst Hst' gives % ⟨_, heq⟩
  subst heq
  imod ghostVar_update_halves (f σ) $$ Hst Hst' with ⟨Hst, Hst'⟩
  imod Hcl $$ [Hst'] with HK
  · iunfold storeSt; iexact Hst'
  imodintro
  iframe

/-- **The object accessor's contract** (a premise of the writers' specs: apimachinery's
`meta.Accessor` and the accessor's `GetResourceVersion`, outside client-go, which the client
discharges for its object types): on an object meeting `OK`, `meta.Accessor` fails exactly when
`rvOf` has no resource version, and otherwise returns an accessor whose `GetResourceVersion()`
returns it. -/
def getRVOk (m : GoInterface) (rv : GoString) : IProp GF :=
  match m with
  | .nil => iprop(False)
  | .ok i => iprop({{ True }} (App (Val #(methods i.ty go!"GetResourceVersion" i.v)) (Val #()))
      {{ RET #rv; True }})

instance getRVOk_persistent (m : GoInterface) (rv : GoString) :
    Persistent (getRVOk (GF := GF) m rv) := by
  cases m <;> unfold getRVOk <;> infer_instance

def rvAcc (OK : GoInterface → IProp GF) (rvOf : GoInterface → Option GoString) : IProp GF :=
  iprop(∀ o : GoInterface, {{ □ OK o }}
    (App (Val (@! _root_.Perennial.k8s_io.apimachinery.pkg.api.«meta».Accessor)) (Val #o))
    {{ (m err : GoInterface), RET (PairV #m #err);
        match rvOf o with
        | some rv => ⌜err = interface.nil⌝ ∗ getRVOk m rv
        | none => ⌜err ≠ interface.nil⌝ }})

instance rvAcc_persistent (OK : GoInterface → IProp GF) (rvOf : GoInterface → Option GoString) :
    Persistent (rvAcc (GF := GF) OK rvOf) := by
  unfold rvAcc; infer_instance

/-- The objects of some of the items' keys meet their contract. -/
theorem okNil_of_keys (OK : GoInterface → IProp GF) (it : Items) (ks : List GoString)
    (h : ∀ k ∈ ks, k ∈ it) :
    □ ([∗map] _k ↦ o ∈ it, okNil OK o) ⊢ [∗list] o ∈ ks.map (objAt it), okNil OK o := by
  rw [BigSepL.bigSepL_map]
  apply BigSepL.bigSepL_intro
  intro i k hk
  have hm := h k (List.mem_of_getElem? hk)
  rw [GMap.mem_iff] at hm
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 hm
  unfold objAt
  rw [ho]
  exact intuitionistically_elim.trans (BigSepM.bigSepM_lookup ho)

/-- One of the store lock's reader slots. -/
def tsReader (c : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF) : IProp GF :=
  sync.ownRWMutex (structFieldRef threadSafeMap go!"lock" c) (tsP c γ OK Fam)

end defs

end cache
end EtcdGrove
end Perennial
