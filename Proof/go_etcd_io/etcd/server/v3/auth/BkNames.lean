/-
**The auth store's per-backend ghost names** (the auth-on snapshot plan's decision 3b; moved from
its Draft, `SnapAuthOnDraft.lean`, at the Prove step, 2026-11-03). Each backend the store runs on has
names `γc : AuthBkNames`: its write token `authWTok` (the apply thread's right to the backend's auth
batch), its currency `authCur` (fractional: readers hold a part; the release needs all of it) and
its retired token `authRetired`. The store's names `γa` gain the current backend's names
(`authBkCur`, at `γa.bk`: half in `beMu`'s guard, half with the write token, `authWHeld`) and the
succession right (`authSucc`, at `γa.succ`: one live backend at a time). `authBkLife` is a backend's
lifecycle (retire, release, publish), which the trusted premise gives with each backend; the
published index's authority is shared (`authPubQ`; the apply thread's quarter `authPubTok`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Steps

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace auth

open Iris Iris.BI Iris.ProofMode

section ghost
variable [GooseExts] {GF : BundledGFunctors} [AllG GF]

/-- **A backend's auth ghost names** (the write token's, the currency's, the retired token's). -/
abbrev AuthBkNames : Type := GName × GName × GName

/-- **The backend `γc`'s write token** `T` (exclusive): the apply thread's right to the backend's
auth batch, held outside a batch transaction (`Lock()` takes it, `Unlock()` gives it back). -/
def authWTok (γc : AuthBkNames) : IProp GF := token γc.1

/-- **The backend `γc`'s currency** `Cu q` (fractional): `beP` holds it with the backend, readers
under `beMu`'s read lock a part; `Recover` hands the old backend's whole `Cu 1` back. -/
def authCur (γc : AuthBkNames) (q : Qp) : IProp GF := ghostVar γc.2.1 q ()

/-- **The backend `γc` retired** (exclusive; what retiring `T` leaves). -/
def authRetired (γc : AuthBkNames) : IProp GF := token γc.2.2

/-- **The right to make a new backend current** (exclusive; review round A1's attack A): only the
retirement of the current backend's write token produces it, and the premises take it (boot's,
from the store's allocation, which mints it: review round A2's 1; the snapshot clause's, from the
previous backend's retirement), so at most one backend of the store is live (its write contract, its
latest clause and its publication) at a time. -/
def authSucc (γa : AuthNames) : IProp GF := token γa.succ

/-- **The share `q` of the current backend's name**: `beP` holds half (at its fraction), the apply
thread the other half with the write token (`authWHeld`); the tie of `beP`'s `T` to the apply
thread's (review round 3's B). -/
def authBkCur (γa : AuthNames) (q : Qp) (γc : AuthBkNames) : IProp GF :=
  ghostVar γa.bk q γc

theorem authBkCur_agree (γa : AuthNames) (q1 q2 : Qp) (γc γc' : AuthBkNames) :
    ⊢ authBkCur (GF := GF) γa q1 γc -∗ authBkCur γa q2 γc' -∗ ⌜γc = γc'⌝ := by
  unfold authBkCur
  exact ghostVar_agree γa.bk γc q1 γc' q2

/-- **The apply thread's write token on the current backend**: `T` and its half of the name. -/
def authWHeld (γa : AuthNames) (γc : AuthBkNames) : IProp GF :=
  iprop(authWTok γc ∗ authBkCur γa (1 : Qp).half γc)

/-- **The apply thread's write token on the current backend, in the mode `M`** (the auth-on
snapshot plan's Prove step, 2026-11-03): in `on γa`, `authWHeld` at the backend names `γc` (a
reader holding it finds them `beP`'s backend's, as the name's halves agree); nothing in the other
modes. What the latest-state reads (`lockedReadTx.specL` and the checks' `specL`s) take and give
back at the same `γc`, so that the apply thread lends it with its write contract at `authWTok γc`
and takes it back (`latestResC`). -/
def authWHeldM (M : AuthMode) (γc : AuthBkNames) : IProp GF :=
  match M with
  | .on γa => iprop(authWHeld γa γc)
  | _ => iprop(True)

/-- **A share of the published index's authority** (`authPubAuth` is the whole). -/
def authPubQ (γa : AuthNames) (q : Qp) (p : Nat) : IProp GF := monoNatAuthOwn γa.pub q p

/-- **The apply thread's quarter of the published index's authority** (decision 2): with the
store's half (`revFresh`) and `T`, publication; retiring `T` gives it to the realization until the
release. -/
def authPubTok (γa : AuthNames) : IProp GF :=
  iprop(∃ p : Nat, authPubQ γa (1 : Qp).half.half p)

/-- A share of the published index's authority gives its lower bound. -/
theorem authPubQ_lb (γa : AuthNames) (q : Qp) (p : Nat) :
    authPubQ (GF := GF) γa q p ⊢ authPubQ γa q p ∗ authPubLb γa p := by
  unfold authPubQ authPubLb
  iintro H
  ihave #Hlb := monoNatLbOwn_get γa.pub q p $$ H
  iframe H Hlb

/-- A lower bound is below any share of the authority. -/
theorem authPubQ_lb_le (γa : AuthNames) (q : Qp) (p i : Nat) :
    authPubQ (GF := GF) γa q p ∗ authPubLb γa i ⊢ ⌜i ≤ p⌝ := by
  unfold authPubQ authPubLb
  iintro ⟨H, #Hlb⟩
  icases monoNatLbOwn_valid γa.pub q p i $$ H Hlb with %Hv
  ipureintro; exact Hv.2

/-- **The published index's authority in shares**: the store's half (`revFresh`), the apply
thread's quarter (`authPubTok`) and the realization's quarter. -/
theorem authPubAuth_split (γa : AuthNames) (p : Nat) :
    authPubAuth (GF := GF) γa p ⊢
      authPubQ γa (1 : Qp).half p ∗ authPubTok γa ∗ authPubQ γa (1 : Qp).half.half p := by
  unfold authPubAuth authPubTok authPubQ
  iintro H
  ihave H : monoNatAuthOwn γa.pub ((1 : Qp).half + ((1 : Qp).half.half + (1 : Qp).half.half)) p
    $$ [H]
  · rw [Qp.half_add_half, Qp.half_add_half]; iexact H
  icases ((monoNatAuthOwn_fractional γa.pub p).fractional (1 : Qp).half
    ((1 : Qp).half.half + (1 : Qp).half.half)).1 $$ H with ⟨H1, H2⟩
  icases ((monoNatAuthOwn_fractional γa.pub p).fractional (1 : Qp).half.half
    (1 : Qp).half.half).1 $$ H2 with ⟨H2, H3⟩
  iframe H1 H3
  iexact H2

/-- **The store's ghost at its allocation** (the auth plan's E3h, 2026-10-27): the half of the
latest state's ghost variable and the history's quarter with the cap's lower bound at it (H5) that the
store's revision invariant takes (`revCur`), and the store's half of the published index's
authority at `0` (the invariant's freshness, `revFresh`; the auth-on snapshot plan's Freeze,
2026-11-03: the other half is the realization's, `authSchemaSrv`'s; until then the whole, and the
definition was in `Model.lean`). -/
def authStoreInit (γa : AuthNames) (hs : List AuthState) (st : AuthState) : IProp GF :=
  iprop(authCurHalf γa st ∗ authHistRev γa hs ∗ capLb γa hs ∗ authPubQ γa (1 : Qp).half 0 ∗
    (∃ b : Bool, ghostVar γa.fen 1 b) ∗ ∃ v : Loc × Nat, ghostVar γa.fca 1 v)

theorem authPubAuth_halves (γa : AuthNames) (p : Nat) :
    authPubAuth (GF := GF) γa p ⊢ authPubQ γa (1 : Qp).half p ∗ authPubQ γa (1 : Qp).half p := by
  unfold authPubAuth authPubQ
  iintro H
  ihave H : monoNatAuthOwn γa.pub ((1 : Qp).half + (1 : Qp).half) p $$ [H]
  · rw [Qp.half_add_half]; iexact H
  icases ((monoNatAuthOwn_fractional γa.pub p).fractional (1 : Qp).half (1 : Qp).half).1 $$ H
    with ⟨H1, H2⟩
  iframe H1 H2

end ghost

section life
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A backend's lifecycle** (persistent; trusted, given by the premise with each backend's `γc`;
`K` what its realization keeps, `bOpen γB authOpenQ` for the server's backends):
- **retire**: `T` and the publication quarter for the lock's share of the history (the share is at
  rest in the realization while `T` is out of a batch; `Lock()` moves it out, `Unlock()` back), the
  retired token and the succession right (`authSucc`, for the next backend's snapshot clause): the
  backend's write contract and latest clause end with it;
- **release**: the retired token and the whole currency (no reader can begin a read) for `K` (the
  backend's open share, for its `Close`: decision 3a) and the publication quarter back. Reads begun
  before the release may still be running (`Cu` comes back at `RLock`): this is realizable only over
  a backend whose `Close` waits for the read transaction's holders (Go's does: `commit` takes
  `readTx.Lock()`), which today's `backend__Close` spec (`bOpen 1`, with every reader's open share
  back) does not state: a backend-level change (review round A1's 3);
- **publish**: with `T` (no batch open, the backend holds the history's last state), the
  publication quarter, the history's half at `hs` and the store's half at `p`, the published index
  raised to `hs`'s last.
Fancy updates at `⊤` (review R2's N2: the released share `K` is exclusive and its ghost names are
not `bOpen`'s, so the realization keeps it in an invariant, which a basic update cannot open);
publish's at `⊤ ∖ ↑(nroot.@"authRev")`, as the store's half of the published index is in the
store's revision invariant, open when it runs (the user's decision at the Prove step, 2026-11-03):
the realization keeps its invariants out of that namespace. -/
def authBkLife (γa : AuthNames) (γc : AuthBkNames) (K : IProp GF) : IProp GF :=
  iprop(□ (authWTok γc ∗ authPubTok γa ={⊤}=∗
        (∃ st : AuthState, authLockI (.on γa) st) ∗ authRetired γc ∗
          authSucc γa) ∗
    □ (authRetired γc ∗ authCur γc 1 ={⊤}=∗ K ∗ authPubTok γa) ∗
    □ (∀ (hs : List AuthState) (p : Nat), authWTok γc -∗ authPubTok γa -∗
        authHistHalf γa hs -∗ authPubQ γa (1 : Qp).half p -∗ ⌜p + 1 ≤ hs.length⌝
        ={⊤ ∖ ↑(nroot.@"authRev")}=∗
      authWTok γc ∗ authPubTok γa ∗ authHistHalf γa hs ∗
        authPubQ γa (1 : Qp).half (hs.length - 1)))

instance authBkLife_persistent (γa : AuthNames) (γc : AuthBkNames) (K : IProp GF) :
    Persistent (authBkLife γa γc K) := by
  unfold authBkLife; infer_instance

/-- **What publication takes beside the authority, in the mode `M`**: in `on γa`, the current
backend's lifecycle (its publish clause), its write token and the apply thread's quarter of the
published index (`authPubTok`); nothing in the other modes. -/
def authPubRes (M : AuthMode) (γc : AuthBkNames) (K : IProp GF) : IProp GF :=
  match M with
  | .on γa => iprop(authBkLife γa γc K ∗ authWTok γc ∗ authPubTok γa)
  | _ => iprop(True)


end life

end auth
end EtcdGrove
end Perennial
