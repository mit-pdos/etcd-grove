/-
**The auth store's snapshot clause** (the auth-on snapshot plan's decision 8 and N4): what the auth
store needs of a backend the snapshot install swaps in (`authSchemaSnap`), its vocabulary (the
realization's open share `authOpenQ`, the schema auth backend `ablOn`, the write contract at a
frozen hook `authWAtHook`, the store's share of a backend's reader slots `authRdSlots` and its
supply `authRdSupply`), and the clause in the store's mode (`authSnapKitM`), which the snapshot
path's bundle carries (`srvSnapRO`). Moved out of `AuthSrv.lean`, which `SnapRO.lean` cannot import.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ImageOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthBkHook
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRest
public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.RdPool

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

-- (P6.2) `authOpenQ`, `authBkts`, `ablOn`, `authWAtHook` are `AuthBkHook.lean`'s.

/-- **The auth store's reader slots of the backend `d`** (N4): its auth share (`backend.rdAuth`,
`backend.authRdN` slots, a part of the constructor's partition, P1) and (A6.2 of `auth-schema-srv`, §R.1,
2026-11-17) the auth buckets' claim tokens (`backend.rbClaimToks`: the realization claims the auth buckets
without the batch lock, `backend.rbOwnIn_claim`, once per backend), which
the boot premise and the snapshot clause hand the realization for good (review R4's F1: a permission
check's read transaction may outlive `beMu`, `store.go:941-947`, so the release cannot give them
back; `backend.Close` takes only the open token, which the slots carry no share of). A ticket `R` is
redeemed against a slot of the backend current at `lockedReadTx` (with a share of its currency
`Cu`, which the release takes whole), so the same `R` works on every backend. -/
def authRdSlots (d : mvcc.KBReal) : IProp GF :=
  iprop(backend.rdAuth d.γB d.P d.be ∗ backend.rbClaimToks d.γB d.P authBkts)

/-- **The auth store's reader supply** (N4; review R4's F2 and N2): what `authStoreKit`'s post gives
the server in place of today's `actualMaxReaders` copies of `RD`, in every mode: `authRdN - 1` plain
copies of the ticket, which the readers keep as long as they like (a gRPC slot, the apply thread's
`kvOwn`, the compactor), as today; the `authRdN`-th is the auth applier's, in `authApplyResPre`
(`Recover` reads with it). `NewServer` takes 66 of them. -/
def authRdSupply (RD : IProp GF) : IProp GF :=
  iprop([∗list] _x ∈ List.replicate (backend.authRdN - 1) (), RD)

/-- **The snapshot clause** (trusted; persistent, at the store's `R`): a backend `d` the apply
thread opened, its hook frozen, its tracked auth buckets `r` holding `st` (`authBucketsAt`), the
lock's share of the history at `st` (deposited, as at boot: `st` is the history's last, so
recorded and at an index no smaller than the published one), its open share `authOpenQ`, the
succession right (the previous backend retired), the client's idle half of the auth buckets
(`rbOwnIn … authBkts`: `r` is what its readers see), the auth buckets in its table and the store's
share of its reader slots (`authRdSlots`): schema's
auth backend `abl` over it meets, for fresh names `γc`, the guarded read contract at `R`, the write
contract at its hook and at every schema auth backend on it (`authWAtHook`), with the write token,
the whole currency and the lifecycle (`authBkLife`, its realization keeping the open share until
the release, and the slots for good). The readers' copies of `R` (tickets, the boot premise's) work on it
unchanged. The client keeps the other tracked buckets. **The state's permission keys valid**
(`auth.permKeysOk st`; auth-schema-srv A6's P2, approved by etcd-grove-03, 2026-11-18): the read contract's views
are recorded states (`authStateAt`, which carries it), and nothing else the clause takes gives it (the role
encoding is opaque); every state of the history has it (`SnapAuthRecover.histWf`). -/
def authSchemaSnap (γa : auth.AuthNames) (R : IProp GF) : IProp GF :=
  iprop(□ ∀ (lg abl : Loc) (d : mvcc.KBReal) (W Pk : IProp GF) (f : GoFunc)
      (r : GMap GoString backend.BktData) (st : auth.AuthState),
    ⌜lg ≠ null⌝ -∗ ⌜authBucketsAt st r⌝ -∗ ⌜auth.permKeysOk st⌝ -∗ ablOn abl d.be lg -∗
    -- (review R1's F5) the auth buckets in the backend's table, as `NewAuthStore.spec` takes them
    ⌜d.P.has mvcc.authBI ∧ d.P.has mvcc.authUsersBI ∧ d.P.has mvcc.authRolesBI⌝ -∗
    backend.isBackend d.γB d.P W Pk d.be -∗ backend.plHookRO d.γB f -∗ ⌜f ≠ func.nil⌝ -∗
    backend.rbOwnIn d.γB authBkts r -∗ authRdSlots d -∗
    backend.bOpen d.γB authOpenQ -∗
    auth.authLockI (.on γa) st -∗ auth.authSucc γa -∗
    |={⊤}=> ∃ γc : auth.AuthBkNames,
      auth.authBackendOk (authBkIface abl) R (.on γa) γc ∗ auth.authCur γc 1 ∗
      auth.authWBackendOkR (authBkIface abl) (.on γa) Pk f (auth.authWTok γc) (backend.wbTok d.γB) ∗
      authWAtHook γa d γc ∗ authBkLend γa γc d ∗ auth.authWTok γc ∗
      auth.authBkLife γa γc (backend.bOpen d.γB authOpenQ))

instance authSchemaSnap_persistent (γa : auth.AuthNames) (R : IProp GF) :
    Persistent (authSchemaSnap (GF := GF) γa R) := by
  unfold authSchemaSnap; infer_instance

/-- **The auth store's snapshot clause in the mode `M`** (the auth-on snapshot plan's decision 8,
the Freeze's item 3; persistent): in `on γa`, the store `stl`'s invariant at its backend's read
resource `R`, the snapshot clause at `R` (`authSchemaSnap`: every later backend meets the store's
contracts), and the checks' reader resource `RD` the store's `authRd` over `R`; nothing in the other
modes. What the install's `Recover` takes with auth on (`srvSnapRO` carries it at the server's
`E.RD`). -/
def authSnapKitM (M : auth.AuthMode) (stl : Loc) (RD : IProp GF) : IProp GF :=
  match M with
  | .on γa => iprop(∃ R : IProp GF, auth.authInv stl R (.on γa) ∗ authSchemaSnap γa R ∗
      ⌜RD = auth.authRd stl R (.on γa)⌝)
  | _ => iprop(True)

instance authSnapKitM_persistent (M : auth.AuthMode) (stl : Loc) (RD : IProp GF) :
    Persistent (authSnapKitM (GF := GF) M stl RD) := by
  cases M <;> unfold authSnapKitM <;> infer_instance

/-- **`authSchemaSrv`, restated** (the premise of `NewServer.specM true`; one trusted premise for
boot and every snapshot): for any auth names, given what `NewAuthStore`'s axiom takes of the
server's backend, its open share `authOpenQ`, the batch lock's share of the history at the boot
state and **half the published index's authority** (decision 2), schema's auth backend `abl` over
`d` meets, for fresh names `γc`: the guarded read contract at a reader resource `R`, with the whole
currency; the write contract at every schema auth backend on `d` at its frozen hook, at the write
token `authWTok γc`; the boot write contract (with the hook `P f`) and `CreateAuthBuckets` at the boot
write token `T_b := authWTok γc ∗ plHook d.γB func.nil`, which it gives back; the publication quarter
and the lifecycle (its realization keeping the open share and a quarter of the published index's
authority); `authRdN - 1` copies of `R` (tickets, backed by the store's share of the backend's reader
slots, `authRdSlots`, taken; N4; A6.1b's option (b), decided by etcd-grove-03 2026-11-17: one slot fewer
than the share, which the realization keeps for the write token's reads, `authBackendReads`, which take
no ticket); the constructor's critical section, whose `Post`
gives back the open share; and the snapshot clause at `R`. It takes the client's idle
half of the (empty) auth buckets (decision 1: their write authority stays with the realization; the
client keeps the others') and the succession right (one live backend).

**Write-back** (auth-schema-fix F1, decided by etcd-grove-81, 2026-11-12): the realization owns no
backend write-back tokens and makes none; each write spends the server's (`Wb := backend.wbTok d.γB`,
paid from the apply loop's receipts and, at boot, `NewServer`'s): a batch `Unlock` two (schema's
`authBatchTx.Unlock` is the backend batch's `Unlock` then `Commit`), `ForceCommit` one,
`CreateAuthBuckets` one, `GetAllRoles` two (a batch). Until F1 the premise handed it a bag of two
tokens (`ownToks d.γB.wb 2`) for every batch it would ever commit.
**The boot write token carries the unset hook** (auth-schema-srv A6's fix (A), decided by etcd-grove-03,
2026-11-18): until then the boot write contract was at `authWTok γc` and `Post` gave back the hook
(`plHook d.γB func.nil`), after which the caller may set the hook; the contract, persistent, then
promised a `Lock` (schema's `LockInsideApply`, which runs the hook) at `f` with no share of the hook
left: false for `f = nil` (a client sets the hook to a panicking function and calls the boot `Lock`
with a trivial contract; `notes/auth-schema-srv-refuted.md`, the third refutation). Now the boot
contract serves only the holder of the unset hook, which nobody can set meanwhile.
**The lend** (`authBkLend`, F2): a read-only observation of the auth buckets (an abstract `RL` with a
law against the batch lock's `rbOwn`), with no write authority; until F2 it lent the buckets'
`rbPart`, through which a client could write them.
**The write contract's text** (`auth.authBatchTxLkR`): `GetAllRoles` lists only `auth.roleListed`
names (F3: Go's range `[0x00, 0xff)`), and all of them only when fewer than `2 ^ 63 - 1` are listed (A6 (R-c),
2026-11-19: the range's implicit limit); `UnsafePutUser` takes valid UTF-8 roles (F4: a proto3
`string`); both puts take a non-empty name of a message without unknown fields (the axiom
re-review's m1 and M1, 2026-11-13).

Refutations fixed against earlier texts: S0's four (`notes/auth-schema-srv-refuted.md`, F1-F4, the
four above); before them, five: (1) the latest clause took `T`; (2) the published index's authority
was shared with the realization, publication needed `T`; (3) no `rbOwn` of the auth buckets came
back; (4) `Cu`/`T` stood for an open share the realization keeps until both are surrendered; (5) `T`
and `Cu` were functions of `γc`, which `beP` and the apply thread share. Review rounds A1/A2: the
auth buckets taken idle (no pending write: the readers see `r`); the succession right taken (one
live backend). -/
def authSchemaSrv : IProp GF :=
  iprop(□ ∀ (γa : auth.AuthNames) (lg abl : Loc) (d : mvcc.KBReal) (W Pk : IProp GF) (qo : Qp)
      (r : GMap GoString backend.BktData),
    ⌜lg ≠ null⌝ -∗
    ⌜(r.lookup go!"auth").getD ∅ = ∅ ∧ (r.lookup go!"authUsers").getD ∅ = ∅ ∧
      (r.lookup go!"authRoles").getD ∅ = ∅⌝ -∗
    ablOn abl d.be lg -∗
    ⌜d.P.has mvcc.authBI ∧ d.P.has mvcc.authUsersBI ∧ d.P.has mvcc.authRolesBI⌝ -∗
    backend.isBackend d.γB d.P W Pk d.be -∗ backend.bOpen d.γB qo -∗
    backend.bOpen d.γB authOpenQ -∗ authRdSlots d -∗
    backend.plHook d.γB func.nil -∗ backend.rbOwnIn d.γB authBkts r -∗
    auth.authSucc γa -∗
    auth.authLockI (.on γa) auth.bootState -∗ auth.authPubQ γa (1 : Qp).half 0 -∗
    |={⊤}=> ∃ (R P : IProp GF) (f : GoFunc) (Pre Q Post : IProp GF) (γc : auth.AuthBkNames),
      auth.authBackendOk (authBkIface abl) R (.on γa) γc ∗ auth.authCur γc 1 ∗
      auth.authWBackendOkR (authBkIface abl) (.on γa) P f
        iprop(auth.authWTok γc ∗ backend.plHook d.γB func.nil) (backend.wbTok d.γB) ∗
      authWAtHook γa d γc ∗ authBkLend γa γc d ∗
      □ ({{ (auth.authWTok γc ∗ backend.plHook d.γB func.nil) ∗ backend.wbTok d.γB }} (App (Val #(methods
          (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty)
          go!"CreateAuthBuckets" #abl)) (Val #())) {{ RET #(); auth.authWTok γc ∗ backend.plHook d.γB func.nil }}) ∗
      (auth.authWTok γc ∗ backend.plHook d.γB func.nil) ∗ auth.authPubTok γa ∗
      auth.authBkLife γa γc (backend.bOpen d.γB authOpenQ) ∗
      srvApi.csContractA P f Pre Q Post ∗
      ([∗list] _x ∈ List.replicate (backend.authRdN - 1) (), R) ∗
      (Post -∗ backend.bOpen d.γB qo) ∗
      authSchemaSnap γa R)

instance authSchemaSrv_persistent : Persistent (authSchemaSrv (GF := GF)) := by
  unfold authSchemaSrv; infer_instance

end defs

end EtcdGrove
end Perennial
