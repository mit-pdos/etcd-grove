/-
**The lease API's key checks: their vocabulary** (the lease-keys plan, Part B, 2026-10-31;
`notes/lease-keys-plan.md`). Lean-first (no Rocq counterpart).

`checkLeaseRenew`, `checkLeaseTimeToLive` and `checkLeaseLeases` (`v3_server.go`) run on a gRPC
goroutine: they read the auth store as a reader with a lower bound `n` of its published index
(`auth.authPubLbM`, as the read path's checks, `apply/AuthCheckTxnLb.lean`) and the lessor as a
reader with a lower bound `m` of its history (`lease.lessorLb`, `lease/Reader.lean`). A passed check
says, of the principal the request carries (`infoBoundM`): auth disabled at a state no older than
`n`, or the principal an admin at one, or the permission (`IsPutPermitted` for a renewal,
`IsRangePermitted` for the others) of every key of the lease at an index no older than `m`, each at a
state no older than `n`.

- `adminVerdictFrom M n info err`: `IsAdminPermitted`'s verdict no older than `n` (its `nil`).
- `isAuthStoreLeaseLb st RD M n` (persistent): the auth store's methods the checks call, each at
  states no older than `n`: `IsAuthEnabled`, `Revision`, `IsAdminPermitted`, `IsPutPermitted`,
  `IsRangePermitted`. The real store's: `IsAuthEnabled.wp_lb`, `Revision.wp_lb`,
  `IsPutPermitted.wp_lb`, `IsRangePermitted.wp_lb` (`auth/Fresh*.lean`); `IsAdminPermitted` at a
  lower bound has no proof yet (Part B leaves the server-level resources to the entry points).
- `srvAuthLeaseLb s E`, `srvLessorRd s γl`: the server's auth store and lessor fields with them.
- `leaseKeysFrom`'s verdicts: `leaseKeysVerdictFrom M n info γl m id op`; the checks' class:
  `leaseCheckFrom`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReadOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthCheckTxnLb
public import Proof.go_etcd_io.etcd.server.v3.lease.Reader

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`IsAdminPermitted`'s verdict no older than the index `n`** in the mode `M` (persistent): in
`on γa`, a passed check's principal an admin at a state recorded at an index at least `n`; with auth
off, a pass. -/
def adminVerdictFrom (M : auth.AuthMode) (n : Nat) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (err : GoInterface) : IProp GF :=
  match M with
  | .off => iprop(⌜err = GoInterface.nil⌝)
  | .any => iprop(True)
  | .on γa => iprop(∃ (i : Nat) (st : auth.AuthState), auth.authStateAt γa i st ∗
      ⌜n ≤ i ∧ (err = GoInterface.nil → auth.adminOk st (some (auth.authInfoM info)))⌝)

instance adminVerdictFrom_persistent (M : auth.AuthMode) (n : Nat)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (err : GoInterface) :
    Persistent (adminVerdictFrom (GF := GF) M n info err) := by
  unfold adminVerdictFrom; cases M <;> infer_instance

/-- **`permCheck2` no older than a lower bound**: `IsPutPermitted(authInfo, key)`'s verdict at states
no older than `n`, for a caller with the reader resource `RD`. -/
def permCheck2Lb (ai : GoInterfaceOk) (m : GoString) (RD : IProp GF) (M : auth.AuthMode) (n : Nat)
    (op : auth.PermType) : IProp GF :=
  iprop(□ (∀ (a : Loc) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac) (key : GoSlice) (k : List w8)
      (dk : DFrac),
    {{ a ↦{dq} info ∗ key ↦*{dk} k ∗ RD ∗ ⌜sint.Z key.len < 2 ^ 63 - 1⌝ }}
      (App (App (Val #(methods ai.ty m ai.v)) (Val #a)) (Val #key))
    {{ (err : GoInterface), RET #err; a ↦{dq} info ∗ key ↦*{dk} k ∗ RD ∗ authApplyErrIs err ∗
        auth.permVerdictFrom M n info k [] op err }}))

/-- **The auth store's methods the lease checks call, no older than a reader's lower bound `n`**
(persistent): `IsAuthEnabled`, `Revision` and `IsAdminPermitted` with their verdicts at states no
older than `n`, and the permission checks `IsPutPermitted` and `IsRangePermitted` at such states. -/
def isAuthStoreLeaseLb (st : GoInterface) (RD : IProp GF) (M : auth.AuthMode) (n : Nat) :
    IProp GF :=
  iprop(∃ ai : GoInterfaceOk, ⌜st = GoInterface.ok ai⌝ ∗
    □ ({{ RD }} (App (Val #(methods ai.ty go!"IsAuthEnabled" ai.v)) (Val #()))
        {{ (b : Bool), RET #b; RD ∗ auth.enabledVerdictFrom M n b }}) ∗
    □ ({{ True }} (App (Val #(methods ai.ty go!"Revision" ai.v)) (Val #()))
        {{ (x : w64), RET #x; auth.revisionVerdictFrom M n x }}) ∗
    □ (∀ (a : Loc) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac),
      {{ a ↦{dq} info ∗ RD }} (App (Val #(methods ai.ty go!"IsAdminPermitted" ai.v)) (Val #a))
      {{ (err : GoInterface), RET #err; a ↦{dq} info ∗ RD ∗ authApplyErrIs err ∗
          adminVerdictFrom M n info err }}) ∗
    permCheck2Lb ai go!"IsPutPermitted" RD M n .write ∗
    apply.permCheck3Lb ai go!"IsRangePermitted" RD M n .read)

instance isAuthStoreLeaseLb_persistent (st : GoInterface) (RD : IProp GF) (M : auth.AuthMode)
    (n : Nat) : Persistent (isAuthStoreLeaseLb st RD M n) := by
  unfold isAuthStoreLeaseLb permCheck2Lb apply.permCheck3Lb; infer_instance

/-- **The server `s`'s auth store with the lease checks' methods at every lower bound**
(persistent): its `authStore` field, and `isAuthStoreLeaseLb` of it at any lower bound of the
published index the caller holds. -/
def srvAuthLeaseLb (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(∃ au : GoInterface, srvAuthStoreAddr s ↦□ au ∗
    □ ∀ n : Nat, auth.authPubLbM E.authMode n -∗ isAuthStoreLeaseLb au E.RD E.authMode n)

instance srvAuthLeaseLb_persistent (s : Loc) (E : apply.AEnv GF) :
    Persistent (srvAuthLeaseLb (GF := GF) s E) := by
  unfold srvAuthLeaseLb; infer_instance

/-- **The server `s`'s lessor is the lessor of `γl`** (persistent): its `lessor` field the real
lessor at some `lp`, `lessorInv` of it. -/
def srvLessorRd (s : Loc) (γl : GName) : IProp GF :=
  iprop(∃ lp : Loc, srvLessorAddr s ↦□ lease.lessorIface lp ∗ lease.lessorInv lp γl)

instance srvLessorRd_persistent (s : Loc) (γl : GName) : Persistent (srvLessorRd (GF := GF) s γl) := by
  unfold srvLessorRd; infer_instance

/-- **The keys of the lease `id` at an index no older than `m`, each permitted** (persistent): no
lease of `id` there, or the keys `ks` of its lease `l` there (`leaseKeysFrom`), the operation `op`
on each permitted to `info` at a state no older than `n` (`IsPutPermitted(k)`/`IsRangePermitted(k,
[])`'s verdict passed). -/
def leaseKeysVerdictFrom (M : auth.AuthMode) (n : Nat) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (γl : GName) (m : Nat) (id : w64) (op : auth.PermType) : IProp GF :=
  iprop(lease.leaseAbsentFrom γl m id ∨
    ∃ (l : Loc) (ks : List GoString), lease.leaseKeysFrom γl m id l ks ∗
      [∗list] k ∈ ks, auth.permVerdictFrom M n info k [] op GoInterface.nil)

instance leaseKeysVerdictFrom_persistent (M : auth.AuthMode) (n : Nat)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (γl : GName) (m : Nat) (id : w64)
    (op : auth.PermType) : Persistent (leaseKeysVerdictFrom (GF := GF) M n info γl m id op) := by
  unfold leaseKeysVerdictFrom; infer_instance

/-- **What a passed lease check establishes** of the request at `ctx` on the server `s`, for the
keys `K` (persistent): auth disabled at a state no older than `n`; or the request's principal
(`infoBoundM`: with auth on, the empty user or one bound to the context's token) an admin at such a
state, or `K info` (the keys' verdicts). -/
def leaseCheckFrom (s : Loc) (E : apply.AEnv GF) (ctx : GoInterface) (n : Nat)
    (K : go_etcd_io.etcd.server.v3.auth.AuthInfo → IProp GF) : IProp GF :=
  iprop(auth.enabledVerdictFrom E.authMode n false ∨
    ∃ info : go_etcd_io.etcd.server.v3.auth.AuthInfo, infoBoundM E.authOn s E ctx info ∗
      (adminVerdictFrom E.authMode n info GoInterface.nil ∨ K info))

instance leaseCheckFrom_persistent (s : Loc) (E : apply.AEnv GF) (ctx : GoInterface) (n : Nat)
    (K : go_etcd_io.etcd.server.v3.auth.AuthInfo → IProp GF) [hK : ∀ info, Persistent (K info)] :
    Persistent (leaseCheckFrom (GF := GF) s E ctx n K) := by
  unfold leaseCheckFrom; infer_instance

end defs

end EtcdGrove
end Perennial
