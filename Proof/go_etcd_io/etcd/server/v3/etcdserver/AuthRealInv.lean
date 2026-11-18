/-
**The auth realization's per-backend invariant** (auth-schema-srv A6, 2026-11-18;
`notes/auth-schema-srv-handoff.md`, "A6 invariant, refined"). One invariant per backend `γc`, in the namespace
`authRealN` (disjoint from the backend's `rbClaimN` and from the store's `nroot.@"authRev"`), holding:
- **the buckets** (`bkSt`): the claimed halves of the three auth buckets' readers' contents (`rbRd ½`), each a
  recorded state (`authStateAt`), the `auth` bucket the latest (`j_u, j_r ≤ j_a`), all no older than the
  realization's quarter of the published index; idle (the batch lock's share of the history, the claimed part,
  the batch token: every bucket at the history's last), in a batch (the write token deposited), or gone (after
  the retirement);
- **the life** (`lifeSt`): live (the succession right and the retired token, the two reader pools and the rest of
  the open share), retired (the write token and the publication quarter, the pools), released (the write token,
  the whole currency, the retired token; the pools' remains).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthRealRead
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthRealPool
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthSnapKit
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ClaimedLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authReal

open Iris Iris.BI Iris.ProofMode backend

/-! ## The buckets' encodings -/

section pure
variable [GooseExts]

/-- The auth buckets, as a list (the claim's `Sc`). -/
def authBktL : List GoString := [go!"auth", go!"authUsers", go!"authRoles"]

/-- **The `auth` bucket `ca` holds the state `st`'s flag and revision**: what `unsafeReadAuthEnabled` and
`unsafeReadAuthRevision` read of it, and a revision of 8 bytes if any. Unlike `schema.authBucketsAre`, true of
the boot buckets (empty: disabled, revision `0`). -/
def authAt (st : auth.AuthState) (ca : BktData) : Prop :=
  schema.enabledOf ⟨ca, ∅, ∅⟩ = st.enabled ∧ uint.nat (schema.revisionOf ⟨ca, ∅, ∅⟩) = st.revision ∧
    schema.revWf ca

/-- **The auth buckets `D` hold the view `v`**: each bucket its state's. -/
def viewAt (v : auth.BkView) (D : schema.AuthData) : Prop :=
  authAt v.atAuth D.auth ∧ (∃ dU, schema.usersAt v.atUsers D.users dU) ∧
    (∃ dR, schema.rolesAt v.atRoles D.roles dR)

theorem enabledOf_auth (D : schema.AuthData) : schema.enabledOf D = schema.enabledOf ⟨D.auth, ∅, ∅⟩ := rfl
theorem revisionOf_auth (D : schema.AuthData) : schema.revisionOf D = schema.revisionOf ⟨D.auth, ∅, ∅⟩ := rfl

theorem viewAt_wf {v : auth.BkView} {D : schema.AuthData} (h : viewAt v D) : schema.authWf D := by
  obtain ⟨⟨-, -, hr⟩, ⟨dU, hu⟩, ⟨dR, hrl⟩⟩ := h
  exact ⟨schema.usersDec_wf (schema.usersAt_dec hu), schema.rolesDec_wf (schema.rolesAt_dec hrl), hr⟩

end pure

/-! ## The ghost names -/

/-- **The realization's names of one backend**: the store's (`γa`), the backend's auth names (`γc`), the
tickets' (`γt`), the ticket pool's (`γm`, `γh`), the reserved pool's (`γm'`, `γh'`) and the batch token's (`γk`). -/
structure RNames where
  γa : auth.AuthNames
  γc : auth.AuthBkNames
  γt : GName
  γm : GName
  γh : GName
  γm' : GName
  γh' : GName
  γk : GName

/-- The realization's invariants' namespace. -/
def authRealN : Namespace := nroot.@"authReal"

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- The reader slots' count of the ticket pool (one slot of the store's share is the reserved pool's). -/
def ticketN : Nat := authRdN - 1

/-- **What a reader of the ticket pool deposits** (its lent `L`): a share of the currency (the read contract's
first two clauses) or the write token (its third clause). -/
def depT (γ : RNames) : Option Qp → IProp GF
  | some q => auth.authCur γ.γc q
  | none => auth.authWTok γ.γc

/-- **The batch token** (exclusive): the idle and gone branches hold it, a batch's lock token holds it. -/
def batchTok (γ : RNames) : IProp GF := token γ.γk

/-- **The buckets' branch**: idle (the lock's share of a history `hs` whose last is every bucket's state, at
its last index; the claimed part at contents `rc` that the readers see; the batch token), in a batch (the write
token), or gone (the batch token, after the retirement). -/
def bkBranch (γ : RNames) (d : mvcc.KBReal) (sa su sr : auth.AuthState) (ja ju jr : Nat)
    (cs : GoString → BktData) : IProp GF :=
  iprop((∃ (hs : List auth.AuthState) (rc : GMap GoString BktData), auth.authLockQ γ.γa hs ∗
      rbOwnInR d.γB (fun n => n ∈ authBktL) rc ∗ batchTok γ ∗
      ⌜hs.getLast? = some sa ∧ su = sa ∧ sr = sa ∧ ja = hs.length - 1 ∧ ju = ja ∧ jr = ja ∧
        ∀ n, n ∈ authBktL → bktOf rc n = cs n⌝) ∨
    auth.authWTok γ.γc ∨ batchTok γ)

/-- **The buckets** (see the file header): the readers' contents `cs` of the three buckets, their states
`sa su sr` recorded at `ja ju jr`, the realization's quarter of the published index at `p`, the branch. -/
def bkSt (γ : RNames) (d : mvcc.KBReal) : IProp GF :=
  iprop(∃ (cs : GoString → BktData) (sa su sr : auth.AuthState) (ja ju jr p : Nat),
    rbRd d.γB go!"auth" (1 : Qp).half (cs go!"auth") ∗
    rbRd d.γB go!"authUsers" (1 : Qp).half (cs go!"authUsers") ∗
    rbRd d.γB go!"authRoles" (1 : Qp).half (cs go!"authRoles") ∗
    auth.authStateAt γ.γa ja sa ∗ auth.authStateAt γ.γa ju su ∗ auth.authStateAt γ.γa jr sr ∗
    auth.authPubQ γ.γa (1 : Qp).half.half p ∗
    ⌜viewAt ⟨sa, su, sr⟩ ⟨cs go!"auth", cs go!"authUsers", cs go!"authRoles"⟩ ∧
      ju ≤ ja ∧ jr ≤ ja ∧ p ≤ ju ∧ p ≤ jr⌝ ∗
    bkBranch γ d sa su sr ja ju jr cs)

/-- **The two reader pools** (`AuthRealPool`), each slot a reader slot of the backend with the share `s0` of
its open token: the ticket pool (`ticketN` slots, the tickets deposited, the readers' lent `depT`) and the
reserved pool (one slot, for the write token's reads: the write token deposited, nothing lent). -/
def pools (γ : RNames) (d : mvcc.KBReal) (s0 : Qp) : IProp GF :=
  iprop(poolSt γ.γm γ.γh (ticketsIn γ.γt ticketN) (depT γ) (rdTok d.γB d.P d.be) (bOpen d.γB s0) ticketN ∗
    poolSt γ.γm' γ.γh' (tokIn (auth.authWTok γ.γc)) (fun _ => iprop(True)) (rdTok d.γB d.P d.be)
      (bOpen d.γB s0) 1)

/-- **The pools after the release**: the held slots' receipts and tickets, the deposits' maps empty. -/
def poolsRel (γ : RNames) : IProp GF :=
  iprop(poolRel γ.γm γ.γh (ticketsIn γ.γt ticketN) ∗ poolRel γ.γm' γ.γh' (tokIn (auth.authWTok γ.γc)))

/-- **The life** (see the file header), with the rest `q0` of the realization's open share. -/
def lifeSt (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) : IProp GF :=
  iprop((auth.authSucc γ.γa ∗ auth.authRetired γ.γc ∗ pools γ d s0 ∗ bOpen d.γB q0) ∨
    (auth.authWTok γ.γc ∗ auth.authPubTok γ.γa ∗ pools γ d s0 ∗ bOpen d.γB q0) ∨
    (auth.authWTok γ.γc ∗ auth.authCur γ.γc 1 ∗ auth.authRetired γ.γc ∗ poolsRel γ))

/-- **The realization's invariant of one backend.** -/
def realInv (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) : IProp GF :=
  iprop(inv authRealN (iprop(bkSt γ d ∗ lifeSt γ d s0 q0)))

instance realInv_persistent (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) :
    Persistent (realInv (GF := GF) γ d s0 q0) := by
  unfold realInv; infer_instance

end defs

end authReal
end EtcdGrove
end Perennial
