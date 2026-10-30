/-
The consistency store's representation predicates (`k8s.io/client-go/util/consistency`,
`consistency.go`). Lean-first; phase 2 of the DaemonSet plan (`notes/k8s-daemonset-plan.md`).
The abstract state and its operations are in `Model.lean`.

**The specs are logically atomic** over the abstract state `M` (`consState γ M`, half of a ghost
variable whose other half is in the store's invariant): the caller keeps `consState γ M` in an
invariant of its own and each method's linearization point updates it (`wroteAtM`, `clearM`,
`GMap.delete`).

**The documented precondition of `EnsureReady`** ("Must not be called concurrently with WroteAt for
the same owner", `consistency.go:44,150`) is a resource: the store is built for a family of
permissions `T o q` that the caller chooses (`NewConsistencyStore`'s spec; for the DaemonSet
controller, built from the work queue's per-key token), fractional in `q` and such that `T o 1`
excludes any other `T o q` (`tokExcl T`). `WroteAt(o, ...)` needs some `T o q`, `EnsureReady(o)`
needs `T o 1`; `Clear` needs none. Without the precondition the specs would be false: `EnsureReady`
checks the record and then clears it (two critical sections), and a `WroteAt` in between is lost.

**The invariant** `consInv` (namespace `consN`). Physical state: the map `writes` (owner to
`*ownerRecord`), under the `RWMutex` `writesLock`, mirrored by the ghost variable `γ.W` (half in
the lock's predicate `writesP`, half here); each record's `versions` map, under its `Mutex`, mirrored
by a ghost variable per record (`RecS.γv`: half in the record's lock invariant `recLockInv`, half
here, `Vg`). Every record ever created is registered (`γ.recs`, persistent elements: `isRec`).
**Pending writes** (`γ.pend`): `WroteAt` takes effect (its linearization point) when it finds or
installs the owner's record, under the map's lock, and writes the record afterwards, under the
record's lock; in between its write is pending (`pendTok`, its receipt), and the permission
`T o q` it holds is deposited here. The abstract versions of the owner's current record are the
newest of its physical and its pending versions (`absVsOk`, `absRel`).
**`EnsureReady`'s slot** (`γ.ens`): `EnsureReady(o)` deposits its `T o 1` here while it reads the
record (`EnsSt`), so no write of `o` is pending (`tokExcl`) and the record's versions do not
change; once it finds them ready it marks the slot cleared, which deletes the owner's record
abstractly (its linearization point), and its `Clear` then removes the record physically and
takes the permission back (`ensTok`).

**The stores** `S` (group resource to `LastSyncRVGetter`, read-only once built) and their
contract `G gr rv` (persistent, the caller's): each non-nil getter's
`LastStoreSyncResourceVersion()` returns some `rv` with `□ G gr rv` (`getterOk`). For the
DaemonSet controller, `G` says that the informer's store has seen every change up to `rv`.
-/
module

public import Proof.k8s_io.client_go.util.consistency.Model
public import Proof.k8s_io.client_go.util.consistency.Init
public import Perennial.Proof.sync
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.GhostVar
public import Perennial.ProgramLogic.AtomicFupd

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace consistency

open Iris Iris.BI k8s_io.client_go.util.consistency resourceversion

/-! ## Ghost state and records -/

/-- A record's fixed facts: its owner and UID, the `versions` map's location, the ghost name of
its versions' mirror. -/
structure RecS [GooseExts] where
  owner : Owner
  uid : GoString
  vm : Loc
  γv : GName

/-- A pending write: to record `r`, of `rv` to `gr`, by a holder of `T _ q`. -/
structure Pend [GooseExts] where
  r : Loc
  gr : GR
  rv : GoString
  q : Qp

/-- `EnsureReady`'s slot: the record `r` it reads, its versions `V`, and whether it found them
ready (the owner's record is then deleted, abstractly). -/
structure EnsSt [GooseExts] where
  r : Loc
  V : Vs
  cleared : Bool

section count
variable [GooseExts]

instance recS_countable : Pos.Countable RecS :=
  .ofInjective (fun s => Pos.Countable.encode (s.owner, s.uid, s.vm, s.γv))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h; obtain ⟨h1, h2, h3, h4⟩ := h
      subst h1 h2 h3 h4; rfl)

instance pend_countable : Pos.Countable Pend :=
  .ofInjective (fun p => Pos.Countable.encode (p.r, p.gr, p.rv, p.q))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h; obtain ⟨h1, h2, h3, h4⟩ := h
      subst h1 h2 h3 h4; rfl)

instance ensSt_countable : Pos.Countable EnsSt :=
  .ofInjective (fun e => Pos.Countable.encode (e.r, e.V, e.cleared))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h; obtain ⟨h1, h2, h3⟩ := h
      subst h1 h2 h3; rfl)

instance rec_countable : Pos.Countable Rec :=
  .ofInjective (fun r => Pos.Countable.encode (r.uid, r.vs))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h; obtain ⟨h1, h2⟩ := h
      subst h1 h2; rfl)

end count

/-- The ghost names and fixed locations of a consistency store. -/
structure ConsNames where
  /-- the abstract state (`consState`) -/
  M : GName
  /-- the mirror of the `writes` map -/
  W : GName
  /-- the registered records -/
  recs : GName
  /-- the pending writes -/
  pend : GName
  /-- `EnsureReady`'s slots -/
  ens : GName
  /-- the `writes` map -/
  wm : Loc
  /-- the `stores` map -/
  sm : Loc

/-- The namespace of the store's invariant (and of its specs' masks). -/
def consN : Namespace := nroot.@"consistency"

/-! ## The pure invariant -/

section pure
variable [GooseExts]

/-- The pending writes to `r`: `pin gr y` iff some pending write of `y` to `gr` is to `r`. -/
def pendOf (P : GMap Nat Pend) (r : Loc) (gr : GR) (y : GoString) : Prop :=
  ∃ id p, P !! id = some p ∧ p.r = r ∧ p.gr = gr ∧ p.rv = y

/-- `EnsureReady(o)` found `r`'s versions ready and deleted the owner's record abstractly. -/
def clearedAt (E : GMap Owner EnsSt) (o : Owner) (r : Loc) : Prop :=
  ∃ e, E !! o = some e ∧ e.r = r ∧ e.cleared = true

/-- **The abstraction**: an owner's abstract record is its current record's UID with the newest of
its physical and pending versions, unless `EnsureReady` deleted it. -/
def absRel (M : GMap Owner Rec) (W : GMap Owner Loc) (R : GMap Loc RecS) (Vg : GMap Loc Vs)
    (P : GMap Nat Pend) (E : GMap Owner EnsSt) : Prop :=
  ∀ o, match W !! o with
    | none => M !! o = none
    | some r => (clearedAt E o r → M !! o = none) ∧
        (¬ clearedAt E o r → ∃ s V Va, R !! r = some s ∧ Vg !! r = some V ∧
          M !! o = some ⟨s.uid, Va⟩ ∧ absVsOk V (pendOf P r) Va)

/-- The pure part of the invariant. -/
def consWf (M : GMap Owner Rec) (W : GMap Owner Loc) (R : GMap Loc RecS) (Vg : GMap Loc Vs)
    (P : GMap Nat Pend) (n : Nat) (E : GMap Owner EnsSt) : Prop :=
  absRel M W R Vg P E ∧
  (∀ o r, W !! o = some r → ∃ s, R !! r = some s ∧ s.owner = o) ∧
  (∀ id p, P !! id = some p → (R !! p.r).isSome ∧ id < n) ∧
  (∀ r V, Vg !! r = some V → vsWf V) ∧
  (∀ r, (R !! r).isSome → (Vg !! r).isSome) ∧
  (∀ o e, E !! o = some e →
    (W !! o = some e.r ∨ W !! o = none) ∧ Vg !! e.r = some e.V ∧
    (∃ s, R !! e.r = some s ∧ s.owner = o))

end pure

/-! ## The map keys -/

section inj
variable [GooseExts] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]

/-- Two string fields determine a value (their loads are deterministic). -/
theorem two_fields_inj [go.BasicIntoValInj] {S : Type} (ty : go.GoType) (f1 f2 : GoString)
    (g1 g2 : S → GoString)
    (h1 : ∀ x : S, go.IsGoStepPureDetTagged under (StructFieldGet ty f1) #x (Val #(g1 x)))
    (h2 : ∀ x : S, go.IsGoStepPureDetTagged under (StructFieldGet ty f2) #x (Val #(g2 x)))
    (x y : S) (h : (#x : val) = #y) : g1 x = g1 y ∧ g2 x = g2 y := by
  have k1 := (h1 x).isGoStep_det_internal.isGoStep_pure_det
  have k1' := (h1 y).isGoStep_det_internal.isGoStep_pure_det
  have k2 := (h2 x).isGoStep_det_internal.isGoStep_pure_det
  have k2' := (h2 y).isGoStep_det_internal.isGoStep_pure_det
  rw [h] at k1 k2
  have e1 := congrFun (k1.symm.trans k1') (Val #(g1 x))
  have e2 := congrFun (k2.symm.trans k2') (Val #(g2 x))
  simp only [eq_iff_iff, true_iff] at e1 e2
  have f1' : (#(g1 x) : val) = #(g1 y) := by injection e1.symm
  have f2' : (#(g2 x) : val) = #(g2 y) := by injection e2.symm
  exact ⟨go.intoVal_inj f1', go.intoVal_inj f2'⟩

variable [go.BasicIntoValInj]
variable [k8s_io.apimachinery.pkg.types.NamespacedName.TypeAssumptions]
variable [k8s_io.apimachinery.pkg.runtime.schema.GroupResource.TypeAssumptions]

instance owner_intoValInj : go.IntoValInj Owner where
  intoVal_inj x y h := by
    have ⟨e1, e2⟩ := two_fields_inj _ _ _ _ _
      k8s_io.apimachinery.pkg.types.NamespacedName.TypeAssumptions.get_Namespace
      k8s_io.apimachinery.pkg.types.NamespacedName.TypeAssumptions.get_Name x y h
    cases x; cases y; simp only at e1 e2; rw [e1, e2]

instance gr_intoValInj : go.IntoValInj GR where
  intoVal_inj x y h := by
    have ⟨e1, e2⟩ := two_fields_inj _ _ _ _ _
      k8s_io.apimachinery.pkg.runtime.schema.GroupResource.TypeAssumptions.get_Group
      k8s_io.apimachinery.pkg.runtime.schema.GroupResource.TypeAssumptions.get_Resource x y h
    cases x; cases y; simp only at e1 e2; rw [e1, e2]

end inj

/-! ## The separation-logic predicates -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.consistency.Assumptions]


/-- An owner is a safe map key: comparing it with another (field by field) does not panic and is
equality of values. -/
instance owner_safeMapKey (o : Owner) :
    SafeMapKey (GF := GF) k8s_io.apimachinery.pkg.types.NamespacedName.ty o where
  key_ok := trivial
  wp_go_eq_map_key o' _ s E Φ := by
    iintro HΦ
    wp_pures
    by_cases h1 : o.Namespace' = o'.Namespace'
    · rw [decide_eq_true h1]
      wp_pures
      rw [show decide (o.Name' = o'.Name') = decide (o = o') by cases o; cases o'; simp_all]
      iapply HΦ
    · rw [decide_eq_false h1]
      wp_pures
      rw [show (false : Bool) = decide (o = o') by cases o; cases o'; simp_all]
      iapply HΦ

/-- A group resource is a safe map key. -/
instance gr_safeMapKey (g : GR) :
    SafeMapKey (GF := GF) k8s_io.apimachinery.pkg.runtime.schema.GroupResource.ty g where
  key_ok := trivial
  wp_go_eq_map_key g' _ s E Φ := by
    iintro HΦ
    wp_pures
    by_cases h1 : g.Group' = g'.Group'
    · rw [decide_eq_true h1]
      wp_pures
      rw [show decide (g.Resource' = g'.Resource') = decide (g = g') by cases g; cases g'; simp_all]
      iapply HΦ
    · rw [decide_eq_false h1]
      wp_pures
      rw [show (false : Bool) = decide (g = g') by cases g; cases g'; simp_all]
      iapply HΦ

/-- The caller's permissions: `T o 1` excludes every other `T o q`. -/
def tokExcl (T : Owner → Qp → IProp GF) : IProp GF :=
  iprop(□ ∀ o q, T o 1 -∗ T o q -∗ False)

instance tokExcl_persistent (T : Owner → Qp → IProp GF) : Persistent (tokExcl T) := by
  unfold tokExcl; infer_instance

/-- **The abstract state** (the caller's half). -/
def consState (γ : ConsNames) (M : GMap Owner Rec) : IProp GF := ghostVar γ.M (1 : Qp).half M

/-- A record's lock invariant: its `versions` map and its mirror's half. -/
def recLockInv (s : RecS) : IProp GF :=
  iprop(∃ V : Vs, s.vm ↦$ V ∗ ghostVar s.γv (1 : Qp).half V)

/-- A record's fixed physical facts (persistent): its UID and `versions` fields for good, its
lock. -/
def recPhys (r : Loc) (s : RecS) : IProp GF :=
  iprop(⌜r ≠ null⌝ ∗ structFieldRef ownerRecord go!"ownerUID" r ↦□ s.uid ∗
    structFieldRef ownerRecord go!"versions" r ↦□ s.vm ∗
    sync.isMutex (structFieldRef ownerRecord go!"versionsLock" r) (recLockInv s))

instance recPhys_persistent (r : Loc) (s : RecS) : Persistent (recPhys (GF := GF) r s) := by
  unfold recPhys; infer_instance

/-- **A registered record** (persistent). -/
def isRec (γ : ConsNames) (r : Loc) (s : RecS) : IProp GF :=
  iprop(ghostMapElem γ.recs r DFrac.discard s ∗ recPhys r s)

instance isRec_persistent (γ : ConsNames) (r : Loc) (s : RecS) :
    Persistent (isRec (GF := GF) γ r s) := by
  unfold isRec; infer_instance

/-- **A pending write's receipt**. -/
def pendTok (γ : ConsNames) (id : Nat) (p : Pend) : IProp GF := ghostMapElem γ.pend id (DFrac.own 1) p

/-- **`EnsureReady`'s receipt** for its slot. -/
def ensTok (γ : ConsNames) (o : Owner) (e : EnsSt) : IProp GF := ghostMapElem γ.ens o (DFrac.own 1) e

/-- **The invariant** (see the file header). -/
def consInv (γ : ConsNames) (T : Owner → Qp → IProp GF) : IProp GF :=
  iprop(∃ (M : GMap Owner Rec) (W : GMap Owner Loc) (R : GMap Loc RecS) (Vg : GMap Loc Vs)
      (P : GMap Nat Pend) (n : Nat) (E : GMap Owner EnsSt),
    "HM" ∷ ghostVar γ.M (1 : Qp).half M ∗
    "HW" ∷ ghostVar γ.W (1 : Qp).half W ∗
    "Hrecs" ∷ ghostMapAuth γ.recs 1 R ∗
    "#Hrecs_p" ∷ ([∗map] r ↦ s ∈ R, isRec γ r s) ∗
    "Hvg" ∷ ([∗map] r ↦ V ∈ Vg, ∃ s : RecS, ghostMapElem γ.recs r DFrac.discard s ∗
      ghostVar s.γv (1 : Qp).half V) ∗
    "Hpend" ∷ ghostMapAuth γ.pend 1 P ∗
    "Hptoks" ∷ ([∗map] _id ↦ p ∈ P, ∃ s : RecS, ghostMapElem γ.recs p.r DFrac.discard s ∗
      T s.owner p.q) ∗
    "Hens" ∷ ghostMapAuth γ.ens 1 E ∗
    "Hetoks" ∷ ([∗map] o ↦ _e ∈ E, T o 1) ∗
    "%Hwf" ∷ ⌜consWf M W R Vg P n E⌝)

/-- The `writes` map's lock predicate at fraction `q`: the map and its mirror's share. -/
def writesP (γ : ConsNames) (q : Qp) : IProp GF :=
  iprop(∃ W : GMap Owner Loc, γ.wm ↦${DFrac.own q} W ∗ ghostVar γ.W (q.half) W)

instance writesP_fractional (γ : ConsNames) : Fractional (writesP (GF := GF) γ) where
  fractional q1 q2 := by
    have hm := fun (W : GMap Owner Loc) => (ownMap_fractional (GF := GF) γ.wm W).fractional q1 q2
    have hgv := fun (W : GMap Owner Loc) =>
      (ghostVar_fractional (GF := GF) γ.W W).fractional q1.half q2.half
    unfold writesP
    rw [Qp_half_add]
    refine ⟨?_, ?_⟩
    · iintro ⟨%W, Hm, Hg⟩
      icases (hm W).1 $$ Hm with ⟨Hm1, Hm2⟩
      icases (hgv W).1 $$ Hg with ⟨Hg1, Hg2⟩
      isplitl [Hm1 Hg1]
      · iexists W; iframe
      · iexists W; iframe
    · iintro ⟨⟨%W1, Hm1, Hg1⟩, ⟨%W2, Hm2, Hg2⟩⟩
      icombine Hg1 Hg2 gives % ⟨_, Heq⟩
      subst Heq
      iexists W1
      isplitl [Hm1 Hm2]
      · iapply (hm W1).2; iframe
      · iapply (hgv W1).2; iframe

/-- A getter's contract: a non-nil getter's `LastStoreSyncResourceVersion()` returns some `rv`
with `□ Gr rv`. -/
def getterOk (v : LastSyncRVGetter) (Gr : GoString → IProp GF) : IProp GF :=
  match v with
  | .nil => iprop(True)
  | .ok i => iprop({{ True }}
      (App (Val #(methods i.ty go!"LastStoreSyncResourceVersion" i.v)) (Val #()))
      {{ (rv : GoString), RET #rv; □ Gr rv }})

instance getterOk_persistent (v : LastSyncRVGetter) (Gr : GoString → IProp GF) :
    Persistent (getterOk v Gr) := by
  cases v <;> unfold getterOk <;> infer_instance

/-- **The store** (persistent): `c` is a `*consistencyStore` with the stores `S` (whose getters
meet `G`), the permissions `T`, ghost names `γ`. -/
def isCons (c : Loc) (γ : ConsNames) (T : Owner → Qp → IProp GF)
    (S : GMap GR LastSyncRVGetter) (G : GR → GoString → IProp GF) : IProp GF :=
  iprop(
    "#Hwm" ∷ structFieldRef consistencyStore go!"writes" c ↦□ γ.wm ∗
    "#Hsm" ∷ structFieldRef consistencyStore go!"stores" c ↦□ γ.sm ∗
    "#HS" ∷ γ.sm ↦$□ S ∗
    "#Hget" ∷ ([∗map] gr ↦ v ∈ S, getterOk v (G gr)) ∗
    "#Hguard" ∷ sync.isRWMutexGuard (structFieldRef consistencyStore go!"writesLock" c)
      (writesP γ) ∗
    "#Hinv" ∷ inv consN (consInv γ T) ∗
    "#Hexcl" ∷ tokExcl T)

instance isCons_persistent (c : Loc) (γ : ConsNames) (T : Owner → Qp → IProp GF)
    (S : GMap GR LastSyncRVGetter) (G : GR → GoString → IProp GF) :
    Persistent (isCons c γ T S G) := by
  unfold isCons named; infer_instance

/-- **A reader's slot**: one of the `RWMutex`'s bounded reader slots (`WroteAt` and
`EnsureReady` read the map under its read lock). -/
def consReader (c : Loc) (γ : ConsNames) : IProp GF :=
  sync.ownRWMutex (structFieldRef consistencyStore go!"writesLock" c) (writesP γ)

/-- **What `EnsureReady(o)` checked** when it succeeds, of the owner's record `r` (if any) at its
linearization point: for every recorded `gr ↦ wroteRV`, a store is registered for `gr` and it
returned a non-empty `readRV` (with the caller's `G gr readRV`) such that, **if `readRV` is well
formed**, it is at least `wroteRV`. A `readRV` that is not well formed (`"0"`, say) passes the
check: `CompareResourceVersion` fails and the loop goes on (`consistency.go:211`). -/
def readyRec (S : GMap GR LastSyncRVGetter) (G : GR → GoString → IProp GF) :
    Option Rec → IProp GF
  | none => iprop(True)
  | some r => iprop([∗map] gr ↦ wroteRV ∈ r.vs, ∃ readRV : GoString,
      □ G gr readRV ∗
      ⌜(∃ v, S !! gr = some v ∧ v ≠ interface.nil) ∧ readRV ≠ [] ∧
        (wellFormed readRV = true → decVal wroteRV ≤ decVal readRV)⌝)

end defs

end consistency
end EtcdGrove
end Perennial
