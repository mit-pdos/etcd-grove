/-
**The lease API's key checks: their vocabulary** (the lease-keys plan, Part B, 2026-10-31;
`notes/lease-keys-plan.md`). Lean-first (no Rocq counterpart).

`checkLeaseRenew`, `checkLeaseTimeToLive` and `checkLeaseLeases` (`v3_server.go`) run on a gRPC
goroutine: they read the auth store as a reader with a lower bound `n` of its published index
(`auth.authPubLbM`, as the read path's checks, `apply/AuthCheckTxnLb.lean`) and the lessor as a
reader with a lower bound `m` of its history (`lease.lessorLb`, `lease/InvLessor.lean`). A passed check
says, of the principal the request carries (with auth on, bound to the context: `principalBound`):
auth disabled at a state no older than
`n`, or the principal an admin at one, or the permission (`IsPutPermitted` for a renewal,
`IsRangePermitted` for the others) of every key of the lease at an index no older than `m`, each at a
state no older than `n`.

- `adminVerdictFrom M n info err`: `IsAdminPermitted`'s verdict no older than `n` (its `nil`).
- `isAuthStoreLeaseLb st RD M n` (persistent): the auth store's methods the checks call, each at
  states no older than `n`: `IsAuthEnabled`, `Revision`, `IsAdminPermitted`, `IsPutPermitted`,
  `IsRangePermitted`. The real store's: `IsAuthEnabled.wp_lb`, `Revision.wp_lb`,
  `IsPutPermitted.wp_lb`, `IsRangePermitted.wp_lb`, `IsAdminPermitted.wp_lb` (`auth/Fresh*.lean`).
  Both are in `AuthLeaseLb.lean` since the lease-src plan (2026-11-02), for the auth store's
  construction (`authStoreLbM`) to state the latter.
- `srvAuthLeaseLb s E`, `srvLessorRd s γl`: the server's auth store and lessor fields with them.
- `leaseKeysFrom`'s verdicts: `leaseOfKeysVerdictFrom` (of a lease), `leaseKeysVerdictFrom` (of an id); the checks' class:
  `leaseCheckFrom`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReadOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthWhy
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthLeaseLb
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthCheckTxnLb
public import Spec.go_etcd_io.etcd.server.v3.lease.Lease__Keys
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Lookup

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

end defs

section defsHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **The keys of the lease `l` of `id` at an index no older than `m`, each permitted** (persistent):
its keys `ks` there (`leaseKeysFrom`), the operation `op` on each permitted to `info` at a state no
older than `n`. -/
def leaseOfKeysVerdictFrom (M : auth.AuthMode) (n : Nat)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (γl : GName) (m : Nat) (id : w64) (l : Loc)
    (op : auth.PermType) : IProp GF :=
  iprop(∃ ks : List GoString, lease.leaseKeysFrom γl m id l ks ∗
    [∗list] k ∈ ks, auth.permVerdictFrom M n info k [] op GoInterface.nil)

instance leaseOfKeysVerdictFrom_persistent (M : auth.AuthMode) (n : Nat)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (γl : GName) (m : Nat) (id : w64) (l : Loc)
    (op : auth.PermType) : Persistent (leaseOfKeysVerdictFrom (GF := GF) M n info γl m id l op) := by
  unfold leaseOfKeysVerdictFrom; infer_instance

/-- **The keys of the lease `id` at an index no older than `m`, each permitted** (persistent): no
lease of `id` there, or the keys `ks` of its lease `l` there (`leaseKeysFrom`), the operation `op`
on each permitted to `info` at a state no older than `n` (`IsPutPermitted(k)`/`IsRangePermitted(k,
[])`'s verdict passed). -/
def leaseKeysVerdictFrom (M : auth.AuthMode) (n : Nat) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (γl : GName) (m : Nat) (id : w64) (op : auth.PermType) : IProp GF :=
  iprop(lease.leaseAbsentFrom γl m id ∨ ∃ l : Loc, leaseOfKeysVerdictFrom M n info γl m id l op)

instance leaseKeysVerdictFrom_persistent (M : auth.AuthMode) (n : Nat)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (γl : GName) (m : Nat) (id : w64)
    (op : auth.PermType) : Persistent (leaseKeysVerdictFrom (GF := GF) M n info γl m id op) := by
  unfold leaseKeysVerdictFrom; infer_instance

end defsHF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]


end defs

section defsHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **What a passed lease check establishes** of a request carrying the token `tok` on the server
`s`, for the keys `K` (persistent): auth disabled at a state no older than `n`; or the request's
principal, with auth on bound to the token (`principalBound`: the user its token was issued to, or the server's TLS
fallback, whose certificate's common name may be empty), an admin at such a state, or `K info` (the
keys' verdicts). (auth-lease S1, 2026-11-14: until then `infoBoundM`, which with auth on also admitted
the empty user unbound; every lease check refuses a context without a user, `ErrUserEmpty`.) By the
token (perheap C1a, 2026-11-18; until then by the context through the pure `auth.ctxTokenOf`, with
v3rpc's `leaseCheckT` its form over the token, merged into it). -/
def leaseCheckFrom (T : IProp GF) (E : apply.AEnv GF) (tok : Option GoString) (n : Nat)
    (K : go_etcd_io.etcd.server.v3.auth.AuthInfo → IProp GF) : IProp GF :=
  iprop(auth.enabledVerdictFrom E.authMode n false ∨
    ∃ info : go_etcd_io.etcd.server.v3.auth.AuthInfo,
      □ (⌜E.authOn = true⌝ → principalBound T E.authMode tok (some info)) ∗
      (adminVerdictFrom E.authMode n info GoInterface.nil ∨ K info))

instance leaseCheckFrom_persistent (T : IProp GF) [Persistent T] (E : apply.AEnv GF) (tok : Option GoString) (n : Nat)
    (K : go_etcd_io.etcd.server.v3.auth.AuthInfo → IProp GF) [hK : ∀ info, Persistent (K info)] :
    Persistent (leaseCheckFrom (GF := GF) T E tok n K) := by
  unfold leaseCheckFrom; infer_instance

end defsHF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]


end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

open Iris.ProofMode

/-- **The checked principal, bound to the token with auth on** (`principalBound`; auth-lease S1,
the lease checks' `leaseCheckFrom`): `infoBoundM_of_ctxBound` without the empty user. -/
theorem principalBoundOn_of_ctxBound (on : Bool) (s : Loc) (E : apply.AEnv GF) (tok : Option GoString)
    (a : Loc) (user : GoString) (rev : w64) :
    (⌜on = true⌝ → ctxBoundOrTLS s E.authMode tok a) ∗ authInfoIs a user rev ⊢
      □ (⌜on = true⌝ → principalBound (GF := GF) (srvTLSId s) E.authMode tok (some ⟨user, rev⟩)) := by
  iintro ⟨Hb, #Hai⟩
  cases on
  · iintro !> %h; cases h
  · ihave #Hb' := Hb $$ %rfl
    iintro !> %-
    iapply principalBound_of_ctxBoundOrTLS s E.authMode tok a user rev $$ [$Hb' $Hai]

/-- **The bridge to the lease checks** (auth-lease S4, Freeze §4.4, R3-6): `authedFrom` is
`leaseCheckFrom … (fun _ => True)`'s content. -/
theorem leaseCheckFrom_of_authedFrom (s : Loc) (E : apply.AEnv GF) (tok : Option GoString) (n : Nat) :
    authedFrom s E.authMode n tok ⊢ leaseCheckFrom (srvTLSId s) E tok n (fun _ => iprop(True)) := by
  unfold authedFrom leaseCheckFrom
  iintro (#H | ⟨%info, #Hb⟩)
  · ileft; iexact H
  · iright
    iexists info
    isplitr
    · iintro !> %h
      iapply Hb
      ipureintro; exact h
    · iright; itrivial

section monoT
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

open Iris.ProofMode in
/-- `leaseCheckFrom` is monotone in the TLS fact (O2, 2026-11-23). -/
theorem leaseCheckFrom_monoT (T1 T2 : IProp GF) (E : apply.AEnv GF) (tok : Option GoString) (n : Nat)
    (K : go_etcd_io.etcd.server.v3.auth.AuthInfo → IProp GF) :
    iprop(□ (T1 -∗ T2)) ∗ leaseCheckFrom T1 E tok n K ⊢ leaseCheckFrom T2 E tok n K := by
  unfold leaseCheckFrom
  iintro ⟨#HT, H⟩
  icases H with (H | ⟨%info, #Hb, H⟩)
  · ileft; iexact H
  · iright
    iexists info
    iframe H
    imodintro
    iintro %h
    iapply principalBound_mono T1 T2
    iframe HT
    iapply Hb $$ %h

end monoT

end lemmas

end EtcdGrove
end Perennial
