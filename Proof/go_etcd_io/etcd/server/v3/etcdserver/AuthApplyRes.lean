/-
**The apply thread's auth resource** (the auth plan's E2k, 2026-10-26, moved here by E2m so that
the apply thread's state `srvApplyKV`, `InvApplier.lean`, can hold it; `notes/decisions.md`, "E2m
of the auth plan"). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRequest
public import Proof.go_etcd_io.etcd.server.v3.auth.Fuel
public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth
public import Proof.go_etcd_io.etcd.server.v3.auth.TieRes
public import Proof.go_etcd_io.etcd.server.v3.auth.Tokens

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The apply thread's auth resource** of the store `stl` in the mode `M` (the auth plan's E2k,
2026-10-26; `notes/decisions.md`, "E2l of the auth plan", the apply thread's auth resource): in the
mode `on γa`, the admin side's authority with its fuel (`auth.authOwnFu`), its write resource
`auth.authWR` but for the store's user's half of `be` (the backend's write side, the write token,
the half of `be` stays in the server's rest, `authBeOn`, which the admin request's application
borrows: "E2m of the auth plan"), the admin side's halves of `enabled` and of the permission cache
tied to the latest state of the history (`auth.tieRes`, E2v: what the checks at the latest state
need, `auth.latestRes`, and what the admin steps keep, `auth.X.specT`), and the provider's admin
share (`auth.tpAdmin`); `True` in the other modes. `NewServer.specM`'s construction hands it to the apply
thread (`applyBuiltNA`, then `srvApplyKV`). -/
def authApplyRes (M : auth.AuthMode) (stl : Loc) : IProp GF :=
  match M with
  | .on γa => iprop(∃ (hs : List auth.AuthState) (P : IProp GF) (f : val) (T : IProp GF)
      (be : GoInterface), auth.authOwnFu γa hs ∗ auth.tieRes stl (.on γa) hs ∗
      auth.authWBackendOk be (.on γa) P f T ∗ T ∗ auth.tpAdmin stl (.on γa))
  | _ => iprop(True)

/-- **The server's auth resource for its apply thread** (E2k): the store its `authStore` field
holds, with `authApplyRes` in the environment's mode. -/
def srvAuthApplyRes (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(∃ stl : Loc, structFieldRef go_etcd_io.etcd.server.v3.etcdserver.EtcdServer go!"authStore" s ↦□
    (auth.authIface stl) ∗ authApplyRes E.authMode stl)

/-- **The apply thread's auth resource with the latest state of its history** (the auth plan's E3c,
2026-10-27): `authApplyRes`'s, with the history's latest state `st` (in the mode `on γa`; `True` in
the other modes). What ties the apply thread's auth state to the model's (`kvRunOn`'s): at the
server's start, the store's history `[bootState, bump bootState]` (`authStoreKit`'s post, at
`bump bootState`, `srvAuthSt0`). -/
def authApplyResAt (M : auth.AuthMode) (stl : Loc) (st : auth.AuthState) : IProp GF :=
  match M with
  | .on γa => iprop(∃ (hs : List auth.AuthState) (P : IProp GF) (f : val) (T : IProp GF)
      (be : GoInterface), auth.authOwnFu γa hs ∗ auth.tieRes stl (.on γa) hs ∗
      auth.authWBackendOk be (.on γa) P f T ∗ T ∗ auth.tpAdmin stl (.on γa) ∗
      ⌜hs.getLast? = some st⌝)
  | _ => iprop(True)

/-- **The server's auth resource for its apply thread, at the latest state `st`** (E3c). -/
def srvAuthApplyResAt (s : Loc) (E : apply.AEnv GF) (st : auth.AuthState) : IProp GF :=
  iprop(∃ stl : Loc, structFieldRef go_etcd_io.etcd.server.v3.etcdserver.EtcdServer go!"authStore" s ↦□
    (auth.authIface stl) ∗ authApplyResAt E.authMode stl st)

/-- **The apply thread's rights to issue tokens, at the consistent index `k`** (C1's A1,
2026-10-28; `notes/c1-plan.md`, "A1's design"): with auth on, the rights' authority whose minted
tokens are of an index below one at most `k` (`auth.freshBelow`), so that an `Authenticate` entry,
which issues `<prefix>.<k>` with the consistent index `k` before it, can mint its right; nothing
in the other modes. Carried beside the apply thread's state at `k = ciEff γ st.k`, which only
grows. -/
def srvTokRights (E : apply.AEnv GF) (k : w64) : IProp GF :=
  match E.authMode with
  | .on γa => iprop(∃ n : Int, auth.freshBelow γa.fresh n ∗ ⌜n ≤ uint.Z k⌝)
  | _ => iprop(True)

/-- **The rights' empty authority** in the mode `M` (A1): with auth on, `NewTokenProvider`'s, which
the store's construction hands to the server's (`authApplyResPre`); `True` in the other modes. -/
def authFreshInit (M : auth.AuthMode) : IProp GF :=
  match M with
  | .on γa => iprop(ghostMapAuth γa.fresh 1 (∅ : GMap GoString Unit))
  | _ => iprop(True)

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

open Iris.ProofMode in
/-- `authApplyResAt` forgets its latest state into `authApplyRes`. -/
theorem authApplyRes_of_At (M : auth.AuthMode) (stl : Loc) (st : auth.AuthState) :
    authApplyResAt (GF := GF) M stl st ⊢ authApplyRes M stl := by
  cases M with
  | on γa =>
    unfold authApplyResAt authApplyRes
    iintro ⟨%hs, %P, %f, %T, %be, Ho, HX, Hw, HT, Htp, -⟩
    iexists hs, P, f, T, be
    iframe Ho HX Hw HT Htp
  | off => unfold authApplyResAt authApplyRes; iintro -; itrivial
  | any => unfold authApplyResAt authApplyRes; iintro -; itrivial

open Iris.ProofMode in
/-- `srvAuthApplyResAt` forgets its latest state into `srvAuthApplyRes`. -/
theorem srvAuthApplyRes_of_At (s : Loc) (E : apply.AEnv GF) (st : auth.AuthState) :
    srvAuthApplyResAt (GF := GF) s E st ⊢ srvAuthApplyRes s E := by
  unfold srvAuthApplyResAt srvAuthApplyRes
  iintro ⟨%stl, #Hf, H⟩
  iexists stl
  iframe Hf
  iapply authApplyRes_of_At $$ H

open Iris.ProofMode in
theorem srvTokRights_mono (E : apply.AEnv GF) (k k' : w64) (h : uint.Z k ≤ uint.Z k') :
    srvTokRights (GF := GF) E k ⊢ srvTokRights E k' := by
  unfold srvTokRights
  split
  · iintro ⟨%n, H, %Hn⟩
    iexists n
    iframe H
    ipureintro; omega
  · iintro H; iexact H

theorem srvTokRights_congr (E E' : apply.AEnv GF) (k : w64) (h : E.authMode = E'.authMode) :
    srvTokRights (GF := GF) E k ⊢ srvTokRights E' k := by
  unfold srvTokRights
  rw [h]

open Iris.ProofMode in
/-- **The rights at the entry after `x`** (C1's A2): at an index `k` above `x`, either kept (an
entry that issues nothing) or, with auth on, after the right to the token `<pre>.<x>` is minted
(an `Authenticate` entry: `x` is the consistent index it reads); the two alternatives of one
resource (`∧`). -/
theorem srvTokRights_next (E : apply.AEnv GF) (x k : w64) (h : uint.Z x < uint.Z k) :
    srvTokRights (GF := GF) E x ⊢ srvTokRights E k ∧
      ∀ (γa : auth.AuthNames) (pre : GoString), ⌜E.authMode = .on γa⌝ -∗
        |==> (srvTokRights E k ∗ auth.tokFresh γa (auth.simpleTok pre x)) := by
  iintro H
  isplit
  · iapply srvTokRights_mono E x k (Int.le_of_lt h) $$ H
  iintro %γa %pre %hM
  unfold srvTokRights
  rw [hM]
  simp only
  icases H with ⟨%n, Hf, %hn⟩
  imod auth.freshBelow_mint γa.fresh n x pre hn $$ Hf with ⟨Hf, Ht⟩
  imodintro
  isplitl [Hf]
  · iexists (uint.Z x + 1)
    iframe Hf
    ipureintro; omega
  iunfold auth.tokFresh
  iexact Ht

open Iris.ProofMode in
/-- The rights at the boot, of the provider's empty authority. -/
theorem srvTokRights_init (E : apply.AEnv GF) (k : w64) :
    authFreshInit (GF := GF) E.authMode ⊢ srvTokRights E k := by
  unfold authFreshInit srvTokRights
  split
  · iintro H
    iexists 0
    isplitl [H]
    · iapply auth.freshBelow_init $$ H
    · ipureintro; word
  · iintro -; itrivial

end lemmas

end EtcdGrove
end Perennial
