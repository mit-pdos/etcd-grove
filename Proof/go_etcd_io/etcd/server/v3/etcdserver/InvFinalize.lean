/-
The cluster's bootstrap finalization, `(*bootstrappedCluster).Finalize` (`bootstrap.go`), as
etcd-io/etcd#21867 changes it (pr-verify, 2026-10-17). Lean-first (no Rocq counterpart).

**The membership, abstractly.** `Finalize` runs once, in `bootstrap`, before the server exists:
nothing else touches the cluster then. Its membership is described by a record of ids,
`ClusterSt` (the members and the removed ids), held through a predicate `P : ClusterSt → IProp`
that the spec quantifies over: the cluster's methods are names-only (`SetID`, `SetBackend`,
`Recover`, `RemoveMember`, ... are not translated), so what `Finalize` relies on them for is
stated as **contracts on `P`** (persistent Hoare triples, premises of the spec, as
`InvNodeStart.lean`'s `rnClusterOk`), not as axioms:

* `SetID`, `SetBackend`, `ID` leave the membership as it is;
* `Recover` replaces the in-memory membership by the backend's, `σrec` (`UnsafeLoad` reads the
  members and removed buckets);
* `Members()` returns fresh owned members whose ids are a permutation of the members' (the
  existing `RaftCluster.Members.spec`, over the server's `isRaftCluster`, does not state the ids;
  this contract is its bootstrap-time, exclusive view);
* `RemoveMember(id, true)` (`ApplyBoth`) deletes `id` from the members and adds it to the removed
  ids, in memory and in the backend (`MustDeleteMemberFromBackend` deletes from `members` and puts
  into `members_removed`);
* `databaseFileMissing`, `BackendPath`, `os.RemoveAll`, `schema.NewMembershipBackend` and
  `membership.ValidateMaxLearnerConfig`: some result, the membership unchanged.

The contracts are of runs that return: `Recover`'s `MustDetectDowngrade` and the backend reads
and writes (`MustReadMembersFromBackend`, `RemoveMember`'s bolt writes) can panic or `lg.Fatal`,
which the spec does not cover. `ClusterSt` is one record for the in-memory maps and the backend's
buckets: they agree after `Recover`, and `RemoveMember(id, ApplyBoth)` writes both; that reading of
`P` is the contracts' (nothing here ties `P` to the backend).

**The validation model.** `validateRemove σ id` transcribes the `ConfChangeRemoveNode` case of
`RaftCluster.ValidateConfigurationChange` (`cluster.go`; names-only here): with `ApplyBoth`, an id
in the backend's removed set is `ErrIDRemoved`, one not among its members `ErrIDNotFound`, else
valid. `EtcdServer.applyConfChange` (`server.go`), on a validation error, applies the change to
raft with `NodeId = raft.None` and returns before `RemovePeer`: the transport keeps the peer.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

/-! ### The membership record and what `Finalize` does to it (pure) -/

/-- A cluster's membership: the members' ids and the removed ids. -/
structure ClusterSt where
  members : List w64
  removed : List w64

/-- `RemoveMember(id, ApplyBoth)`: `id` leaves the members and joins the removed ids. -/
def ClusterSt.remove (σ : ClusterSt) (id : w64) : ClusterSt :=
  ⟨σ.members.filter (fun x => decide (x ≠ id)), id :: σ.removed⟩

/-- The PR's loop: `RemoveMember` of every id of `ids` but `self`, in order. -/
def removeOthers (self : w64) : List w64 → ClusterSt → ClusterSt
  | [], σ => σ
  | id :: ids, σ => removeOthers self ids (if id ≠ self then σ.remove id else σ)

theorem removeOthers_append (self : w64) (l1 l2 : List w64) (σ : ClusterSt) :
    removeOthers self (l1 ++ l2) σ = removeOthers self l2 (removeOthers self l1 σ) := by
  induction l1 generalizing σ with
  | nil => rfl
  | cons a l1 ih => simp only [List.cons_append, removeOthers]; exact ih _

theorem removeOthers_mem (self : w64) (ids : List w64) (σ : ClusterSt) (x : w64) :
    (x ∈ (removeOthers self ids σ).members ↔ x ∈ σ.members ∧ (x = self ∨ x ∉ ids)) ∧
    (x ∈ (removeOthers self ids σ).removed ↔ x ∈ σ.removed ∨ (x ∈ ids ∧ x ≠ self)) := by
  induction ids generalizing σ with
  | nil => simp [removeOthers]
  | cons a ids ih =>
    simp only [removeOthers]
    rw [(ih _).1, (ih _).2]
    by_cases ha : a = self
    · subst ha
      simp only [ne_eq, not_true_eq_false, ↓reduceIte, List.mem_cons]
      by_cases h1 : x = a <;> by_cases h2 : x ∈ ids <;> simp [h1, h2]
    · simp only [ne_eq, ha, not_false_eq_true, ↓reduceIte, ClusterSt.remove, List.mem_filter,
        decide_eq_true_eq, List.mem_cons]
      have hna : ¬(x = a ∧ x = self) := fun ⟨p, q⟩ => ha (p ▸ q)
      clear ih
      generalize (x ∈ σ.members) = A at *
      generalize (x ∈ σ.removed) = E at *
      generalize (x ∈ ids) = C at *
      generalize (x = a) = B at *
      generalize (x = self) = D at *
      by_cases A <;> by_cases B <;> by_cases C <;> by_cases D <;> by_cases E <;> simp_all

theorem removeOthers_take_succ (self : w64) (ids : List w64) (σ : ClusterSt) (k : Nat) (x : w64)
    (h : ids[k]? = some x) :
    removeOthers self (ids.take (k + 1)) σ =
      (if x ≠ self then (removeOthers self (ids.take k) σ).remove x
       else removeOthers self (ids.take k) σ) := by
  rw [List.take_add_one, h]
  simp [removeOthers_append, removeOthers]

/-- **What `Finalize` leaves**, from the backend's membership `σrec` (after `Recover`): without
`--force-new-cluster`, `σrec` itself; with it (the PR), only `self` of the members, and every other
member among the removed ids. -/
def FinalizedSt (force : Bool) (self : w64) (σrec σ' : ClusterSt) : Prop :=
  if force then
    (∀ x, x ∈ σ'.members ↔ x ∈ σrec.members ∧ x = self) ∧
    (∀ x, x ∈ σ'.removed ↔ x ∈ σrec.removed ∨ (x ∈ σrec.members ∧ x ≠ self))
  else σ' = σrec

theorem removeOthers_finalized (self : w64) (ids : List w64) (σrec : ClusterSt)
    (hp : ids.Perm σrec.members) :
    FinalizedSt true self σrec (removeOthers self ids σrec) := by
  simp only [FinalizedSt, ↓reduceIte]
  constructor
  · intro x
    rw [(removeOthers_mem self ids σrec x).1, hp.mem_iff]
    constructor
    · rintro ⟨hm, hx | hx⟩
      · exact ⟨hm, hx⟩
      · exact absurd hm hx
    · rintro ⟨hm, hx⟩; exact ⟨hm, Or.inl hx⟩
  · intro x
    rw [(removeOthers_mem self ids σrec x).2, hp.mem_iff]

/-- The outcome of `ValidateConfigurationChange` on a `ConfChangeRemoveNode` (`ApplyBoth`). -/
inductive RemoveCheck where
  | ok
  | idRemoved
  | idNotFound
  deriving DecidableEq

/-- `ValidateConfigurationChange`'s `ConfChangeRemoveNode` case, on the backend's membership. -/
def validateRemove (σ : ClusterSt) (id : w64) : RemoveCheck :=
  if id ∈ σ.removed then .idRemoved else if id ∈ σ.members then .ok else .idNotFound

/-- **The PR's finding, on the model.** After `Finalize` with `--force-new-cluster`, the
`ConfChangeRemoveNode` entry `--force-new-cluster` appended for a member other than `self`
(`CreateConfigChangeEnts`, for every id of the WAL's snapshot and entries) fails validation with
`ErrIDRemoved`: `applyConfChange` then never calls `RemovePeer` for it. -/
theorem finalize_force_rejects_removal (self : w64) (σrec σ' : ClusterSt)
    (h : FinalizedSt true self σrec σ') (x : w64) (hx : x ∈ σrec.members) (hne : x ≠ self) :
    validateRemove σ' x = .idRemoved := by
  simp only [FinalizedSt, ↓reduceIte] at h
  have : x ∈ σ'.removed := (h.2 x).2 (Or.inr ⟨hx, hne⟩)
  simp [validateRemove, this]

/-- The same at any later membership whose removed ids include those `Finalize` left (the
validation runs after the WAL's replay, whose `RemoveMember`s only add removed ids). -/
theorem finalize_force_rejects_removal_later (self : w64) (σrec σ' τ : ClusterSt)
    (h : FinalizedSt true self σrec σ') (hτ : ∀ y, y ∈ σ'.removed → y ∈ τ.removed)
    (x : w64) (hx : x ∈ σrec.members) (hne : x ≠ self) :
    validateRemove τ x = .idRemoved := by
  simp only [FinalizedSt, ↓reduceIte] at h
  have : x ∈ τ.removed := hτ x ((h.2 x).2 (Or.inr ⟨hx, hne⟩))
  simp [validateRemove, this]

/-- Without the PR (the backend's membership as `Recover` loaded it), the same entry is valid for
a member not already removed. -/
theorem base_accepts_removal (σrec : ClusterSt) (x : w64) (hx : x ∈ σrec.members)
    (hnr : x ∉ σrec.removed) : validateRemove σrec x = .ok := by
  simp [validateRemove, hx, hnr]

/-- And with the PR, a member of the backend in neither the WAL's snapshot nor its entries (no
removal entry is appended for it, etcd-io/etcd#20967's inconsistency) is gone from the members
all the same: `buildConfStateFromV3store` builds raft's voters from the backend's members, here
`self` only. -/
theorem finalize_force_only_self (self : w64) (σrec σ' : ClusterSt)
    (h : FinalizedSt true self σrec σ') (x : w64) : x ∈ σ'.members → x = self := by
  simp only [FinalizedSt, ↓reduceIte] at h
  intro hx; exact ((h.1 x).1 hx).2

/-! ### The contracts -/

section typeRepr
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `TypeRepr` of the bootstrap structs `Finalize` reads, straight from their `TypeAssumptions`
(as `InvServer.lean` does): their fields of axiomatized types have `sorry` instances. -/
instance (priority := high) bootstrappedCluster_typeRepr :
    TypeRepr bootstrappedCluster.ty bootstrappedCluster :=
  go.type_repr_underlying (u := bootstrappedCluster.underlying)
instance (priority := high) bootstrappedCluster_typeRepr_u :
    TypeRepr bootstrappedCluster.underlying bootstrappedCluster :=
  go.type_repr_underlying (u := bootstrappedCluster.underlying)
instance (priority := high) bootstrappedStorage_typeRepr :
    TypeRepr bootstrappedStorage.ty bootstrappedStorage :=
  go.type_repr_underlying (u := bootstrappedStorage.underlying)
instance (priority := high) bootstrappedStorage_typeRepr_u :
    TypeRepr bootstrappedStorage.underlying bootstrappedStorage :=
  go.type_repr_underlying (u := bootstrappedStorage.underlying)
instance (priority := high) bootstrappedBackend_typeRepr :
    TypeRepr bootstrappedBackend.ty bootstrappedBackend :=
  go.type_repr_underlying (u := bootstrappedBackend.underlying)
instance (priority := high) bootstrappedBackend_typeRepr_u :
    TypeRepr bootstrappedBackend.underlying bootstrappedBackend :=
  go.type_repr_underlying (u := bootstrappedBackend.underlying)
instance (priority := high) bootstrappedWAL_typeRepr : TypeRepr bootstrappedWAL.ty bootstrappedWAL :=
  go.type_repr_underlying (u := bootstrappedWAL.underlying)
instance (priority := high) bootstrappedWAL_typeRepr_u :
    TypeRepr bootstrappedWAL.underlying bootstrappedWAL :=
  go.type_repr_underlying (u := bootstrappedWAL.underlying)
instance (priority := high) fzServerConfig_typeRepr :
    TypeRepr go_etcd_io.etcd.server.v3.config.ServerConfig.ty
      go_etcd_io.etcd.server.v3.config.ServerConfig :=
  go.type_repr_underlying (u := go_etcd_io.etcd.server.v3.config.ServerConfig.underlying)
instance (priority := high) fzServerConfig_typeRepr_u :
    TypeRepr go_etcd_io.etcd.server.v3.config.ServerConfig.underlying
      go_etcd_io.etcd.server.v3.config.ServerConfig :=
  go.type_repr_underlying (u := go_etcd_io.etcd.server.v3.config.ServerConfig.underlying)

end typeRepr

section contracts
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

local notation "RC" => go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty

/-- **The cluster `cl`'s methods at bootstrap, over the membership predicate `P`**, and `Recover`
loading the backend's membership `σrec` (see the file header). Hoare triples, as a callee's spec
is: a premise of `Finalize`'s spec. -/
structure fzClusterOk (cl : Loc) (P : ClusterSt → IProp GF) (σrec : ClusterSt) : Prop where
  /-- `SetID(localID, cid)` -/
  setID : ∀ (σ : ClusterSt) (lid cid : w64), {{ P σ }}
      (App (App (Val (cl @!! RC @!! go!"SetID")) (Val #lid)) (Val #cid))
      {{ RET #(); P σ }}
  /-- `ID()` -/
  id : ∀ σ : ClusterSt, {{ P σ }}
      (App (Val (cl @!! RC @!! go!"ID")) (Val #()))
      {{ (cid : w64), RET #cid; P σ }}
  /-- `SetBackend(be)` -/
  setBackend : ∀ (σ : ClusterSt) (be : GoInterface), {{ P σ }}
      (App (Val (cl @!! RC @!! go!"SetBackend")) (Val #be))
      {{ RET #(); P σ }}
  /-- `Recover(onSet)`: the backend's membership -/
  recover : ∀ (σ : ClusterSt) (f : GoFunc), {{ P σ }}
      (App (Val (cl @!! RC @!! go!"Recover")) (Val #f))
      {{ RET #(); P σrec }}
  /-- `Members()`: fresh owned members, their ids a permutation of the members' -/
  members : ∀ σ : ClusterSt, {{ P σ }}
      (App (Val (cl @!! RC @!! go!"Members")) (Val #()))
      {{ (sl : GoSlice), RET #sl; ∃ l : List (Loc × w64),
          sl ↦* l.map Prod.fst ∗ ([∗list] p ∈ l, membership.memberIs p.1 p.2) ∗
          ⌜(l.map Prod.snd).Perm σ.members⌝ ∗ P σ }}
  /-- `RemoveMember(id, ApplyBoth)` -/
  removeMember : ∀ (σ : ClusterSt) (id : w64), {{ P σ }}
      (App (App (Val (cl @!! RC @!! go!"RemoveMember")) (Val #id)) (Val #true))
      {{ RET #(); P (σ.remove id) }}

/-- **The other callees, names-only** (see the file header): `c.databaseFileMissing(s)`,
`cfg.BackendPath()`, `os.RemoveAll`, `schema.NewMembershipBackend`,
`membership.ValidateMaxLearnerConfig`: some result, the membership (`P σ`) untouched. -/
structure fzCalleesOk (c : Loc) (P : ClusterSt → IProp GF) : Prop where
  dbMissing : ∀ (σ : ClusterSt) (s : Loc), {{ P σ }}
      (App (Val (c @!! go.GoType.PointerType bootstrappedCluster.ty @!! go!"databaseFileMissing"))
        (Val #s))
      {{ (b : Bool), RET #b; P σ }}
  backendPath : ∀ p : Loc, {{ (True : IProp GF) }}
      (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.config.ServerConfig.ty
        @!! go!"BackendPath")) (Val #()))
      {{ (path : GoString), RET #path; True }}
  removeAll : ∀ path : GoString, {{ (True : IProp GF) }}
      (App (Val (@! _root_.Perennial.os.RemoveAll)) (Val #path))
      {{ (err : GoInterface), RET #err; True }}
  newMembershipBackend : ∀ (lg : Loc) (be : go_etcd_io.etcd.server.v3.storage.backend.Backend),
      {{ (True : IProp GF) }}
      (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.NewMembershipBackend))
        (Val #lg)) (Val #be))
      {{ (mb : Loc), RET #mb; True }}
  validateMaxLearner : ∀ (n : w64) (sl : GoSlice) (ms : List Loc), {{ membership.membersAt (GF := GF) sl ms }}
      (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.membership.ValidateMaxLearnerConfig))
        (Val #n)) (Val #sl)) (Val #false))
      {{ (err : GoInterface), RET #err; True }}

end contracts

end EtcdGrove
end Perennial
