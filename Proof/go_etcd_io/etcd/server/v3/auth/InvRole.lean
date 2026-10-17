/-
The auth store's write side for roles (PR etcd#21845, `pr-verify/etcd-21845`): what
`RoleGrantPermission` owns and the contract of the backend's batch transaction it writes the
role through. Lean-first (no Rocq counterpart).

**A role** at `rp` (`ownRole rp name ps`, a `*authpb.Role` as `UnsafeGetRole` unmarshals it): its
struct, its `Name` (read-only bytes, the role's name), its `KeyPermission` slice with its capacity,
and each permission's struct (`ownPerm`, its `Key` and `RangeEnd` read-only bytes), modelled as
the list `ps` of `PermM`s (`RolePerms.lean`).

**The request** (`grantReqOk r name pp`): `r` (a `*AuthRoleGrantPermissionRequest`) and its
permission `pp`, if not nil, read-only (`permRO`): the store only reads them; the permission it
appends shares the request's `Key` and `RangeEnd` slices.

**The roles in the backend** (`Roles m`, abstract): the caller's resource, the role names mapped to
their permissions (`m`). The store writes the roles only from the apply loop, one request at a
time, so the caller owns `Roles` across the request (a premise of the spec, as `W`).

**Contracts** (the store calls them through interfaces; not proved of the real objects, as
`InvAuth.lean`'s read side):
- the backend `be` (`authWriteBackendOk be W H Roles`): `BatchTx()` returns a transaction
  `authBatchTxOk tx W H Roles`;
- the transaction: `Lock()` turns the caller's write resource `W` into the held token `H`,
  `Unlock()` back; with `H`, `UnsafeGetRole(name)` returns nil if `m` has no role `name`, else
  the role `m name` (`ownRole`), and `UnsafePutRole(rp)` stores the role at `rp` under its name.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth
public import Proof.go_etcd_io.etcd.server.v3.auth.RolePerms
public import Perennial.Proof.bytes.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace auth

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth go_etcd_io.etcd.api.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The roles: name to permissions. -/
abbrev RolesM := GoString → Option (List PermM)

/-- `m` with the role `name` holding `ps`. -/
def rolesSet (m : RolesM) (name : GoString) (ps : List PermM) : RolesM :=
  fun n => if n = name then some ps else m n

/-- Every role's permissions are sorted by key. -/
def rolesSorted (m : RolesM) : Prop := ∀ n ps, m n = some ps → SortedByKey ps

/-- **A permission of a role** at `p`: its struct, `PermType` as in `pm`, `Key` and `RangeEnd`
read-only bytes. -/
def ownPerm (p : Loc) (pm : PermM) : IProp GF :=
  iprop(∃ v : authpb.Permission, p ↦ v ∗ ⌜v.PermType' = pm.permType⌝ ∗
    v.Key' ↦*□ pm.key ∗ v.RangeEnd' ↦*□ pm.rangeEnd)

/-- A read-only permission (the request's). -/
def permRO (p : Loc) (pm : PermM) : IProp GF :=
  iprop(∃ v : authpb.Permission, p ↦□ v ∗ ⌜v.PermType' = pm.permType⌝ ∗
    v.Key' ↦*□ pm.key ∗ v.RangeEnd' ↦*□ pm.rangeEnd)

instance permRO_persistent (p : Loc) (pm : PermM) : Persistent (permRO (GF := GF) p pm) := by
  unfold permRO; infer_instance

/-- **The permissions of a role**, the slice `sl` holding the pointers of `l`, each owned. -/
def ownPerms (sl : GoSlice) (l : List (Loc × PermM)) : IProp GF :=
  iprop(sl ↦* l.map Prod.fst ∗ [∗list] x ∈ l, ownPerm x.1 x.2)

/-- **A role** at `rp` named `name` with permissions `ps`. -/
def ownRole (rp : Loc) (name : GoString) (ps : List PermM) : IProp GF :=
  iprop(∃ (v : authpb.Role) (l : List (Loc × PermM)), rp ↦ v ∗ v.Name' ↦*□ name ∗
    ownPerms v.KeyPermission' l ∗ ownSliceCap Loc v.KeyPermission' (DFrac.own 1) ∗
    ⌜l.map Prod.snd = ps⌝)

/-- What `UnsafeGetRole(name)` returns for the role `o` of the backend: nil if there is none,
else the role. -/
def roleIs (rp : Loc) (name : GoString) (o : Option (List PermM)) : IProp GF :=
  iprop(⌜rp = null ∧ o = none⌝ ∨ ∃ ps, ⌜rp ≠ null ∧ o = some ps⌝ ∗ ownRole rp name ps)

/-- **The backend's batch transaction** `tx` (an `AuthBatchTx`; a contract) for the caller's
write resource `W`, held token `H` and roles `Roles`. -/
def authBatchTxOk (tx : GoInterface) (W H : IProp GF) (Roles : RolesM → IProp GF) : IProp GF :=
  iprop(∃ ti : GoInterfaceOk, ⌜tx = GoInterface.ok ti⌝ ∗
    □ ({{ W }} (App (Val #(methods ti.ty go!"Lock" ti.v)) (Val #())) {{ RET #(); H }}) ∗
    □ ({{ H }} (App (Val #(methods ti.ty go!"Unlock" ti.v)) (Val #())) {{ RET #(); W }}) ∗
    □ (∀ (name : GoString) (m : RolesM),
      {{ H ∗ Roles m }} (App (Val #(methods ti.ty go!"UnsafeGetRole" ti.v)) (Val #name))
      {{ (rp : Loc), RET #rp; H ∗ Roles m ∗ roleIs rp name (m name) }}) ∗
    □ (∀ (rp : Loc) (name : GoString) (ps : List PermM) (m : RolesM),
      {{ H ∗ Roles m ∗ ownRole rp name ps }}
        (App (Val #(methods ti.ty go!"UnsafePutRole" ti.v)) (Val #rp))
      {{ RET #(); H ∗ Roles (rolesSet m name ps) ∗ ownRole rp name ps }}))

instance authBatchTxOk_persistent (tx : GoInterface) (W H : IProp GF)
    (Roles : RolesM → IProp GF) : Persistent (authBatchTxOk (GF := GF) tx W H Roles) := by
  unfold authBatchTxOk; infer_instance

/-- **The auth backend's write side** `be` (a contract): `BatchTx()` returns a batch
transaction. -/
def authWriteBackendOk (be : GoInterface) (W H : IProp GF) (Roles : RolesM → IProp GF) :
    IProp GF :=
  iprop(∃ bi : GoInterfaceOk, ⌜be = GoInterface.ok bi⌝ ∗
    □ ({{ True }} (App (Val #(methods bi.ty go!"BatchTx" bi.v)) (Val #()))
      {{ (tx : GoInterface), RET #tx; authBatchTxOk tx W H Roles }}))

instance authWriteBackendOk_persistent (be : GoInterface) (W H : IProp GF)
    (Roles : RolesM → IProp GF) : Persistent (authWriteBackendOk (GF := GF) be W H Roles) := by
  unfold authWriteBackendOk; infer_instance

/-- **The store's backend, for writes**: the store's `be` (read-only, `authInv`) meets the write
contract. -/
def authWriteInv (st : Loc) (W H : IProp GF) (Roles : RolesM → IProp GF) : IProp GF :=
  iprop(∃ be : AuthBackend, aF go!"be" st ↦□ be ∗ authWriteBackendOk be W H Roles)

instance authWriteInv_persistent (st : Loc) (W H : IProp GF) (Roles : RolesM → IProp GF) :
    Persistent (authWriteInv (GF := GF) st W H Roles) := by
  unfold authWriteInv; infer_instance

/-- **The request** `r` of `RoleGrantPermission`, read-only: role name `name`, permission `pp`
(nil, or read-only with model `pm`). -/
def grantReqOk (r : Loc) (name : GoString) (pp : Loc) (pm : PermM) : IProp GF :=
  iprop(∃ v : etcdserverpb.AuthRoleGrantPermissionRequest, r ↦□ v ∗
    ⌜v.Name' = name ∧ v.Perm' = pp⌝ ∗ (⌜pp = null⌝ ∨ ⌜pp ≠ null⌝ ∗ permRO pp pm))

instance grantReqOk_persistent (r : Loc) (name : GoString) (pp : Loc) (pm : PermM) :
    Persistent (grantReqOk (GF := GF) r name pp pm) := by
  unfold grantReqOk; infer_instance

/-- The error variables `RoleGrantPermission` returns, and `authpb.Permission_Type_name` (the
log line's map), initialized: read-only globals (as `authInit`'s, but not in the package's
`isPkgInit`, which the other proofs share). -/
def grantGlobals : IProp GF :=
  iprop((∃ e : GoInterface, globalAddr ErrPermissionNotGiven ↦□ e ∗ ⌜e ≠ GoInterface.nil⌝) ∗
    (∃ e : GoInterface, globalAddr ErrInvalidAuthMgmt ↦□ e ∗ ⌜e ≠ GoInterface.nil⌝) ∗
    (∃ e : GoInterface, globalAddr ErrRoleNotFound ↦□ e ∗ ⌜e ≠ GoInterface.nil⌝) ∗
    (∃ (mp : GoMap) (M : GMap w32 GoString),
      globalAddr authpb.Permission_Type_name ↦□ mp ∗ mp ↦$□ M))

instance grantGlobals_persistent : Persistent (grantGlobals (GF := GF)) := by
  unfold grantGlobals; infer_instance

/-- `bytes.Compare(a, b) < 0` is `a < b`. -/
theorem compareResult_neg (a b : GoString) :
    decide (sint.Z (bytes.compareResult a b) < sint.Z (W64 0)) = decide (go.GoStringLt a b) := by
  unfold bytes.compareResult
  by_cases h : go.GoStringLt a b
  · simp only [h, ↓reduceIte, decide_true]; decide
  · simp only [h, ↓reduceIte, decide_false]
    split <;> decide

/-- The permission `x` of a role's list, out of the list's ownership, and back. -/
theorem ownPerms_acc (l : List (Loc × PermM)) (n : Nat) (x : Loc × PermM)
    (h : l[n]? = some x) :
    ([∗list] y ∈ l, ownPerm (GF := GF) y.1 y.2) ⊢
      ownPerm x.1 x.2 ∗ (ownPerm x.1 x.2 -∗ [∗list] y ∈ l, ownPerm (GF := GF) y.1 y.2) := by
  refine (BigSepL.bigSepL_lookup_acc (PROP := IProp GF)
    (Φ := fun (_ : Nat) (y : Loc × PermM) => ownPerm (GF := GF) y.1 y.2) h).1.trans ?_
  iintro ⟨H, Hw⟩
  iframe H
  iintro H
  ihave Hr := Hw $$ %x H
  rw [list_set_lookup_self _ _ _ h]
  iexact Hr

/-- `bytes.Compare(a, b) >= 0` is `!(a < b)`. -/
theorem compareResult_ge (a b : GoString) :
    decide (sint.Z (bytes.compareResult a b) ≥ sint.Z (W64 0)) = !decide (go.GoStringLt a b) := by
  rw [← compareResult_neg]
  by_cases h : sint.Z (bytes.compareResult a b) < sint.Z (W64 0)
  · rw [_root_.decide_eq_true h, _root_.decide_eq_false (by omega)]; rfl
  · rw [_root_.decide_eq_false h, _root_.decide_eq_true (by omega)]; rfl

end defs

end auth
end EtcdGrove
end Perennial
