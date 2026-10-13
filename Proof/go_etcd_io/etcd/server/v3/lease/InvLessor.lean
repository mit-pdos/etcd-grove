/-
The lessor's lock and what it holds (`server/lease/lessor.go`, 2026-10-13, unit 8 of the
backend). Lean-first (no Rocq counterpart); see `notes/decisions.md`, "The lessor's KV-facing
methods and the live leases (unit 8)".

**The lock** `le.mu` (an `RWMutex`, `lessorMu lp γl`): the fields `leaseMap` (the granted leases,
id to `*Lease`), `itemMap` (item to lease id) and `rd` (the range deleter), and the lessor's half
of the **live-lease set**: a ghost variable `γl` (the store's `γ.leases`) at `(lp, L)`, `L` the
domain of `leaseMap`. Every `*Lease` of the map is `isLeaseObj`: not nil, its own lock `l.mu`
guarding its `itemSet`.

**The lease owner's half** (`leaseOwn γl L`): the other half of `γl`, held by the apply thread
(the one goroutine that grants and revokes leases: `lessor.Grant`/`Revoke` run only in the
applier). Holding it, `L` is the live set: `Attach(id, …)` of an `id ∈ L` succeeds, `Lookup(id)`
returns non-nil exactly for `id ∈ L`. A lease known live is a pure fact `id ∈ L` relative to the
half the caller holds, not a persistent fact: `Revoke` takes the half and shrinks `L`.

**The readers** (`lessorRd lp γl`): `GetLease` and `Lookup` take `le.mu`'s read lock, which needs a
reader slot (`sync.ownRWMutex`); the writers (`Attach`, `Detach`, `SetRangeDeleter`) only the
guard.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.Base
public import Perennial.Ghost.GhostMap

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

namespace go_etcd_io.etcd.server.v3.lease

deriving instance DecidableEq for LeaseItem

end go_etcd_io.etcd.server.v3.lease

namespace EtcdGrove
namespace lease

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease

section fields
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- `&le.<f>` -/
abbrev lF (f : GoString) (lp : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.lease.lessor f lp

/-- `&l.<f>` (a `*Lease`) -/
abbrev lsF (f : GoString) (l : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.lease.Lease f l

/-- The lessor `lp` as a `Lessor` interface value. -/
abbrev lessorIface (lp : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty) #lp

end fields

section keys
variable [FfiSyntax] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]
variable [LeaseItem.TypeAssumptions]

/-- A `LeaseItem` is its key: its Go value determines it (the field read is deterministic). -/
instance leaseItem_intoValInj [go.BasicIntoValInj] : go.IntoValInj LeaseItem where
  intoVal_inj x y h := by
    have hx := (LeaseItem.TypeAssumptions.get_Key x).isGoStep_det_internal.isGoStep_pure_det
    have hy := (LeaseItem.TypeAssumptions.get_Key y).isGoStep_det_internal.isGoStep_pure_det
    rw [h] at hx
    have h2 := congrFun (hx.symm.trans hy) (Val #(x.Key'))
    simp only [eq_iff_iff, true_iff] at h2
    have h3 : (#(x.Key') : val) = #(y.Key') := by
      have := h2.symm
      injection this
    have h4 : x.Key' = y.Key' := go.intoVal_inj h3
    cases x; cases y
    simp only at h4
    subst h4; rfl

end keys

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- What a lease's lock `l.mu` guards: its item set. -/
def leaseItems (l : Loc) (q : Qp) : IProp GF :=
  iprop(∃ (sm : Loc) (S : GMap LeaseItem Unit), lsF go!"itemSet" l ↦{DFrac.own q} sm ∗
    sm ↦${DFrac.own q} S)

/-- A lease of the map: not nil, its lock guarding its item set (persistent). -/
def isLeaseObj (l : Loc) : IProp GF :=
  iprop(⌜l ≠ null⌝ ∗ sync.isRWMutexGuard (lsF go!"mu" l) (leaseItems l))

instance isLeaseObj_persistent (l : Loc) : Persistent (isLeaseObj (GF := GF) l) := by
  unfold isLeaseObj; infer_instance

/-- The lessor's ghost map `γl`'s contents: its location at `false` (pinned for good), its live
set at `true`. -/
def lessorGhost (lp : Loc) (L : List w64) : GMap Bool (Loc ⊕ List w64) :=
  (((∅ : GMap Bool (Loc ⊕ List w64)).insert false (Sum.inl lp)).insert true (Sum.inr L))

/-- A share `q` of the live set `L` (the ghost map `γl`'s element `true`). -/
def leaseFrag (γl : GName) (q : Qp) (L : List w64) : IProp GF :=
  ghostMapElem γl true (DFrac.own q) (Sum.inr L : Loc ⊕ List w64)

instance leaseFrag_timeless (γl : GName) (q : Qp) (L : List w64) :
    Timeless (leaseFrag (GF := GF) γl q L) := by
  unfold leaseFrag; infer_instance

/-- The lessor of `γl` is at `lp` (persistent: the ghost map's element `false`, discarded). -/
def lessorPin (γl : GName) (lp : Loc) : IProp GF :=
  ghostMapElem γl false DFrac.discard (Sum.inl lp : Loc ⊕ List w64)

instance lessorPin_persistent (γl : GName) (lp : Loc) : Persistent (lessorPin (GF := GF) γl lp) := by
  unfold lessorPin; infer_instance

/-- **What `le.mu` guards** at fraction `q`: the lease map `M` (whose domain is the live set
`L`; the lessor's share of it, `q/2`, and of the ghost map's authority), the item map, the range
deleter; every lease of the map `isLeaseObj`. -/
def lessorMu (lp : Loc) (γl : GName) (q : Qp) : IProp GF :=
  iprop(∃ (lm im : Loc) (M : GMap w64 Loc) (I : GMap LeaseItem w64) (rd : GoFunc)
      (L : List w64),
    lF go!"leaseMap" lp ↦{DFrac.own q} lm ∗ lm ↦${DFrac.own q} M ∗
    lF go!"itemMap" lp ↦{DFrac.own q} im ∗ im ↦${DFrac.own q} I ∗
    lF go!"rd" lp ↦{DFrac.own q} rd ∗
    ghostMapAuth γl q (lessorGhost lp L) ∗ leaseFrag γl q.half L ∗
    ⌜∀ id : w64, id ∈ L ↔ (M.lookup id).isSome⌝ ∗
    [∗map] _id ↦ l ∈ M, isLeaseObj l)

/-- **The lessor** at `lp` with ghost map `γl` (persistent): pinned, its lock's guard. -/
def lessorInv (lp : Loc) (γl : GName) : IProp GF :=
  iprop(⌜lp ≠ null⌝ ∗ lessorPin γl lp ∗ sync.isRWMutexGuard (lF go!"mu" lp) (lessorMu lp γl))

instance lessorInv_persistent (lp : Loc) (γl : GName) :
    Persistent (lessorInv (GF := GF) lp γl) := by
  unfold lessorInv; infer_instance

/-- A reader slot of the lessor's lock (`GetLease`, `Lookup`). -/
def lessorRd (lp : Loc) (γl : GName) : IProp GF :=
  sync.ownRWMutex (lF go!"mu" lp) (lessorMu lp γl)

/-- **The lease owner's half** of the live set: holding it, `L` is the live set (the apply
thread's). -/
def leaseOwn (γl : GName) (L : List w64) : IProp GF := leaseFrag γl (1 : Qp).half L

instance leaseOwn_timeless (γl : GName) (L : List w64) : Timeless (leaseOwn (GF := GF) γl L) := by
  unfold leaseOwn; infer_instance

/-- A reader slot of the lessor of `γl`, wherever it is (`lessorPin`). -/
def lessorRdOf (γl : GName) : IProp GF :=
  iprop(∃ lp : Loc, lessorPin γl lp ∗ lessorRd lp γl)

/-- **The lease owner's resource** at the txn layer: its half of the live set and a reader slot
of the lessor's lock (`Lookup`). -/
def lessorUser (γl : GName) (L : List w64) : IProp GF :=
  iprop(leaseOwn γl L ∗ lessorRdOf γl)

/-- Two pins of one ghost map agree. -/
theorem lessorPin_agree (γl : GName) (lp lp' : Loc) :
    lessorPin (GF := GF) γl lp ∗ lessorPin γl lp' ⊢ ⌜lp = lp'⌝ := by
  unfold lessorPin
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %H
  ipureintro
  have h2 := H.2
  cases h2; rfl

/-- Two shares of the live set agree. -/
theorem leaseFrag_agree (γl : GName) (q1 q2 : Qp) (L1 L2 : List w64) :
    leaseFrag (GF := GF) γl q1 L1 ∗ leaseFrag γl q2 L2 ⊢ ⌜L1 = L2⌝ := by
  unfold leaseFrag
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %H
  ipureintro
  have h2 := H.2
  cases h2; rfl

end defs

end lease
end EtcdGrove
end Perennial
