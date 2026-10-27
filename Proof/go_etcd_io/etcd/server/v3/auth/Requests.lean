/-
**The admin requests' contents** (the auth plan's S4, 2026-10-24): what the auth store's admin
methods read of their request messages (`etcdserverpb.Auth*Request`), as persistent read-only
fields, the shape of the apply package's request predicates (`apply/InvRequest.lean`,
`authUserAddIs`, which now are these). A request's `[]byte` fields (`RoleRevokePermission`'s
`Key`/`RangeEnd`, `RoleGrantPermission`'s `Perm`) are read-only slices, as `proto.Unmarshal`
leaves them; the permission of a `RoleGrantPermission` is a read-only message (`ownPermW`,
`Buckets.lean`), which the store puts into the role's record as it is.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Buckets
public import Proof.encoding.base64.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace auth

open Iris Iris.BI go_etcd_io.etcd.api.v3

/-- **base64's standard encoding** (`encoding/base64`'s `StdEncoding.EncodeToString`), of a byte
string. Opaque: what the proofs need is only that what it encodes decodes without an error
(`selectPassword`'s trust boundary, the auth plan's E2u), not the encoding itself. (It moved here
from the apply package's request model, E2t, so that the auth store's boundary can name it.) Since
E2x (2026-10-26) it is `encoding/base64`'s own `stdEnc`, which its package fact gives
`StdEncoding.EncodeToString` (`Proof/encoding/base64/Base.lean`), so that `EtcdServer.UserAdd`'s
request is shown of this form. -/
abbrev stdB64Enc : List w8 → GoString := _root_.Perennial.encoding.base64.stdEnc

/-- **A password choice that cannot fail**: no password asked for, or an empty `Password` with a
`HashedPassword` that is the standard base64 encoding of some bytes (the server's own form since
3.5, `EtcdServer.UserAdd`), which `selectPassword` decodes without an error. -/
def pwSureP (pw hpw : GoString) (nob : Bool) : Prop :=
  nob = true ∨ (pw = [] ∧ ∃ bs : List w8, hpw = stdB64Enc bs)

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The `*pb.AuthUserAddRequest` `r` (not nil): its `Name`, its passwords (`Password`,
`HashedPassword`: read-only, any strings; the model keeps no passwords, `selectPassword` is the
trust boundary), and its `Options` (nil, or a read-only `UserAddOptions`, `userOptsAt`). -/
def userAddReqIs (r : Loc) (name : GoString) : IProp GF :=
  iprop(⌜r ≠ null⌝ ∗ structFieldRef etcdserverpb.AuthUserAddRequest go!"Name" r ↦□ name ∗
    (∃ pw hpw : GoString, structFieldRef etcdserverpb.AuthUserAddRequest go!"Password" r ↦□ pw ∗
      structFieldRef etcdserverpb.AuthUserAddRequest go!"HashedPassword" r ↦□ hpw) ∗
    ∃ (o : Loc) (b : Bool), structFieldRef etcdserverpb.AuthUserAddRequest go!"Options" r ↦□ o ∗ userOptsAt o b)

/-- **The `*pb.AuthUserAddRequest` `r`'s password choice cannot fail** (`pwSureP` of its
`Password`, `HashedPassword` and its options' `NoPassword`): with it, `UserAdd` does not return
`ErrNoPasswordUser` (`UserAdd.specSure`, the auth plan's E2u). -/
def userAddSure (r : Loc) : IProp GF :=
  iprop(∃ (pw hpw : GoString) (o : Loc) (b : Bool),
    structFieldRef etcdserverpb.AuthUserAddRequest go!"Password" r ↦□ pw ∗
    structFieldRef etcdserverpb.AuthUserAddRequest go!"HashedPassword" r ↦□ hpw ∗
    structFieldRef etcdserverpb.AuthUserAddRequest go!"Options" r ↦□ o ∗ userOptsAt o b ∗
    ⌜pwSureP pw hpw b⌝)

instance userAddSure_persistent (r : Loc) : Persistent (userAddSure (GF := GF) r) := by
  unfold userAddSure; infer_instance

/-- The `*pb.AuthUserDeleteRequest` `r` (not nil): its `Name`. -/
def userDeleteReqIs (r : Loc) (name : GoString) : IProp GF :=
  iprop(⌜r ≠ null⌝ ∗ structFieldRef etcdserverpb.AuthUserDeleteRequest go!"Name" r ↦□ name)

/-- The `*pb.AuthUserChangePasswordRequest` `r` (not nil): its `Name` and its passwords. -/
def userChangePasswordReqIs (r : Loc) (name : GoString) : IProp GF :=
  iprop(⌜r ≠ null⌝ ∗ structFieldRef etcdserverpb.AuthUserChangePasswordRequest go!"Name" r ↦□ name ∗
    ∃ pw hpw : GoString,
      structFieldRef etcdserverpb.AuthUserChangePasswordRequest go!"Password" r ↦□ pw ∗
      structFieldRef etcdserverpb.AuthUserChangePasswordRequest go!"HashedPassword" r ↦□ hpw)

/-- The `*pb.AuthUserGrantRoleRequest` `r` (not nil): its `User` and `Role`. -/
def userGrantRoleReqIs (r : Loc) (user role : GoString) : IProp GF :=
  iprop(⌜r ≠ null⌝ ∗ structFieldRef etcdserverpb.AuthUserGrantRoleRequest go!"User" r ↦□ user ∗
    structFieldRef etcdserverpb.AuthUserGrantRoleRequest go!"Role" r ↦□ role)

/-- The `*pb.AuthUserGetRequest` `r` (not nil): its `Name`. -/
def userGetReqIs (r : Loc) (name : GoString) : IProp GF :=
  iprop(⌜r ≠ null⌝ ∗ structFieldRef etcdserverpb.AuthUserGetRequest go!"Name" r ↦□ name)

/-- The `*pb.AuthUserRevokeRoleRequest` `r` (not nil): its `Name` and `Role`. -/
def userRevokeRoleReqIs (r : Loc) (name role : GoString) : IProp GF :=
  iprop(⌜r ≠ null⌝ ∗ structFieldRef etcdserverpb.AuthUserRevokeRoleRequest go!"Name" r ↦□ name ∗
    structFieldRef etcdserverpb.AuthUserRevokeRoleRequest go!"Role" r ↦□ role)

/-- The `*pb.AuthRoleAddRequest` `r` (not nil): its `Name`. -/
def roleAddReqIs (r : Loc) (name : GoString) : IProp GF :=
  iprop(⌜r ≠ null⌝ ∗ structFieldRef etcdserverpb.AuthRoleAddRequest go!"Name" r ↦□ name)

/-- The `*pb.AuthRoleGetRequest` `r` (not nil): its `Role`. -/
def roleGetReqIs (r : Loc) (role : GoString) : IProp GF :=
  iprop(⌜r ≠ null⌝ ∗ structFieldRef etcdserverpb.AuthRoleGetRequest go!"Role" r ↦□ role)

/-- The `*pb.AuthRoleDeleteRequest` `r` (not nil): its `Role`. -/
def roleDeleteReqIs (r : Loc) (role : GoString) : IProp GF :=
  iprop(⌜r ≠ null⌝ ∗ structFieldRef etcdserverpb.AuthRoleDeleteRequest go!"Role" r ↦□ role)

/-- The `*pb.AuthRoleRevokePermissionRequest` `r` (not nil): its `Role`, and its `Key` and
`RangeEnd`, read-only slices holding `key` and `rangeEnd`. -/
def roleRevokePermissionReqIs (r : Loc) (role key rangeEnd : GoString) : IProp GF :=
  iprop(⌜r ≠ null⌝ ∗ structFieldRef etcdserverpb.AuthRoleRevokePermissionRequest go!"Role" r ↦□ role ∗
    (∃ ks : GoSlice, structFieldRef etcdserverpb.AuthRoleRevokePermissionRequest go!"Key" r ↦□ ks ∗ ks ↦*□ key) ∗
    (∃ res : GoSlice, structFieldRef etcdserverpb.AuthRoleRevokePermissionRequest go!"RangeEnd" r ↦□ res ∗
      res ↦*□ rangeEnd))

/-- The `*pb.AuthRoleGrantPermissionRequest` `r` (not nil): its `Name`, and its `Perm`: nil
(`w = none`), or a read-only permission message holding the wire permission `w` (`ownPermW`). -/
def roleGrantPermissionReqIs (r : Loc) (name : GoString) (w : Option PermW) : IProp GF :=
  iprop(⌜r ≠ null⌝ ∗ structFieldRef etcdserverpb.AuthRoleGrantPermissionRequest go!"Name" r ↦□ name ∗
    ∃ p : Loc, structFieldRef etcdserverpb.AuthRoleGrantPermissionRequest go!"Perm" r ↦□ p ∗
      match w with
      | none => iprop(⌜p = null⌝)
      | some w => ownPermW p w)

instance userAddReqIs_persistent (r : Loc) (name : GoString) :
    Persistent (userAddReqIs (GF := GF) r name) := by
  unfold userAddReqIs; infer_instance
instance userDeleteReqIs_persistent (r : Loc) (name : GoString) :
    Persistent (userDeleteReqIs (GF := GF) r name) := by
  unfold userDeleteReqIs; infer_instance
instance userChangePasswordReqIs_persistent (r : Loc) (name : GoString) :
    Persistent (userChangePasswordReqIs (GF := GF) r name) := by
  unfold userChangePasswordReqIs; infer_instance
instance userGrantRoleReqIs_persistent (r : Loc) (user role : GoString) :
    Persistent (userGrantRoleReqIs (GF := GF) r user role) := by
  unfold userGrantRoleReqIs; infer_instance
instance userGetReqIs_persistent (r : Loc) (name : GoString) :
    Persistent (userGetReqIs (GF := GF) r name) := by
  unfold userGetReqIs; infer_instance
instance userRevokeRoleReqIs_persistent (r : Loc) (name role : GoString) :
    Persistent (userRevokeRoleReqIs (GF := GF) r name role) := by
  unfold userRevokeRoleReqIs; infer_instance
instance roleAddReqIs_persistent (r : Loc) (name : GoString) :
    Persistent (roleAddReqIs (GF := GF) r name) := by
  unfold roleAddReqIs; infer_instance
instance roleGetReqIs_persistent (r : Loc) (role : GoString) :
    Persistent (roleGetReqIs (GF := GF) r role) := by
  unfold roleGetReqIs; infer_instance
instance roleDeleteReqIs_persistent (r : Loc) (role : GoString) :
    Persistent (roleDeleteReqIs (GF := GF) r role) := by
  unfold roleDeleteReqIs; infer_instance
instance roleRevokePermissionReqIs_persistent (r : Loc) (role key rangeEnd : GoString) :
    Persistent (roleRevokePermissionReqIs (GF := GF) r role key rangeEnd) := by
  unfold roleRevokePermissionReqIs; infer_instance
instance roleGrantPermissionReqIs_persistent (r : Loc) (name : GoString) (w : Option PermW) :
    Persistent (roleGrantPermissionReqIs (GF := GF) r name w) := by
  unfold roleGrantPermissionReqIs; cases w <;> infer_instance

/-- A response of type `T` returned by an admin method: `nil` if it refused, else a fresh one
whose `Header` the applier sets (the apply package's `respHdrOk`, whose shape this is). -/
def respOk (T : Type) (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop(⌜err ≠ GoInterface.nil → resp = null⌝ ∗
    (⌜resp = null⌝ ∨ ∃ h : Loc, structFieldRef T go!"Header" resp ↦ h))

end defs

end auth
end EtcdGrove
end Perennial
