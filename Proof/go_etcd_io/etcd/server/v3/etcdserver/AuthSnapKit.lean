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
`backend.authRdN` slots, a part of the constructor's partition, P1), which
the boot premise and the snapshot clause hand the realization for good (review R4's F1: a permission
check's read transaction may outlive `beMu`, `store.go:941-947`, so the release cannot give them
back; `backend.Close` takes only the open token, which the slots carry no share of). A ticket `R` is
redeemed against a slot of the backend current at `lockedReadTx` (with a share of its currency
`Cu`, which the release takes whole), so the same `R` works on every backend. -/
def authRdSlots (d : mvcc.KBReal) : IProp GF :=
  backend.rdAuth d.γB d.P d.be

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
unchanged. The client keeps the other tracked buckets. -/
def authSchemaSnap (γa : auth.AuthNames) (R : IProp GF) : IProp GF :=
  iprop(□ ∀ (lg abl : Loc) (d : mvcc.KBReal) (W Pk : IProp GF) (f : GoFunc)
      (r : GMap GoString backend.BktData) (st : auth.AuthState),
    ⌜lg ≠ null⌝ -∗ ⌜authBucketsAt st r⌝ -∗ ablOn abl d.be lg -∗
    -- (review R1's F5) the auth buckets in the backend's table, as `NewAuthStore.spec` takes them
    ⌜d.P.has mvcc.authBI ∧ d.P.has mvcc.authUsersBI ∧ d.P.has mvcc.authRolesBI⌝ -∗
    backend.isBackend d.γB d.P W Pk d.be -∗ backend.plHookRO d.γB f -∗ ⌜f ≠ func.nil⌝ -∗
    backend.rbOwnIn d.γB authBkts r -∗ authRdSlots d -∗
    backend.bOpen d.γB authOpenQ -∗
    auth.authLockI (.on γa) st -∗ auth.authSucc γa -∗
    |={⊤}=> ∃ γc : auth.AuthBkNames,
      auth.authBackendOk (authBkIface abl) R (.on γa) γc ∗ auth.authCur γc 1 ∗
      auth.authWBackendOkR (authBkIface abl) (.on γa) Pk #f (auth.authWTok γc) ∗
      authWAtHook γa d γc ∗ auth.authWTok γc ∗
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

end defs

end EtcdGrove
end Perennial
