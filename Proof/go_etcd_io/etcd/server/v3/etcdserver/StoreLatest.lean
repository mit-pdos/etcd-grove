/-
**The server's auth rows with auth on** (the auth plan's E3l, 2026-10-27; `notes/decisions.md`,
"E3l of the auth plan"). Lean-first (no Rocq counterpart).

What the server keeps of its auth store's invariant for the apply thread, with auth on:

- **the checks at the latest state** (`authStoreLatestM`): the store meets `apply.isAuthStoreL`
  for its reader resource and the apply thread's family `auth.latestRes`
  (`apply.isAuthStoreL_of_authInv`); `NewAuthStore`'s construction gives it (`authStoreKit`'s
  post), the built part keeps it (`srvUberBase`);
- **the range check at a reader's lower bound** (`authStoreLbM`, E3s): with auth on, the store's
  `IsRangePermitted` with its verdict no older than any lower bound of the published index
  (`apply.isAuthStoreRangeLb_of_authInv`); from the same construction, kept beside the above;
- **the admin steps' resource** (E3f's blocker 1, the user's decision 2026-10-27: a separate row).
  The store's half of its `be` field stays in the server's rest (`authBeOn stl bel`, in
  `srvObjsOn`, whose text and D22's `Recover` premise are unchanged) and an admin entry's
  application borrows it. The apply thread's resource (`authApplyResB`) holds, beside
  `authApplyResAt`'s, the backend's write contract at *every* schema auth backend on the server's
  backend `bel` (`authWBackendAt`; the persistent agreement: whichever `*authBackend` the rest's
  half names, its contract is the apply thread's) and the store's admin steps at the resource
  `adminW` (`apply.isAuthStepsX`, of the store's invariant through E3l's backend-keeping
  `X.specTB`); the server's row (`srvAuthApplyResB`) adds the equation of the backend names, the
  environment's write right lending `authBeOn stl bel` (`rwLens E.RW`). `adminW_of_beOn` and
  `beOn_of_adminW` turn the borrowed half into the admin steps' resource and back.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthLatest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthStepsX
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthCheckTxnLb
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthApplyRes

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

/-- **The store's checks at the latest state, in the mode `M`** (the auth plan's E3l, 2026-10-27;
persistent): in the mode `on γa`, the store `st` (`auth.authIface stl`) meets `apply.isAuthStoreL`
for its reader resource `RD` and the apply thread's family `auth.latestRes stl` (what the real
store's invariant gives, `apply.isAuthStoreL_of_authInv`); `True` in the other modes. What the
server's apply thread's latest-state KV triples need of the store (`srvStoreLatest`, `UberOn`). -/
def authStoreLatestM (M : auth.AuthMode) (st : GoInterface) (RD : IProp GF) (stl : Loc) : IProp GF :=
  match M with
  | .on γa => apply.isAuthStoreL st RD (.on γa) (auth.latestRes stl (.on γa))
  | _ => iprop(True)

/-- **The store's range check no older than a reader's lower bound, in the mode `M`** (the auth
plan's E3s, 2026-10-27; persistent): in the mode `on γa`, for every lower bound `n` of the published
index (`auth.authPubLbM`), the store's `IsRangePermitted` with its verdict at states no older than `n`
(`apply.isAuthStoreRangeLb`, of the store's invariant through E3j's `IsRangePermitted.specLb`);
`True` in the other modes. What a reader with auth on needs of the store (`Range.specOn`). -/
def authStoreLbM (M : auth.AuthMode) (st : GoInterface) (RD : IProp GF) : IProp GF :=
  match M with
  | .on γa => iprop(□ ∀ n : Nat, auth.authPubLbM (.on γa) n -∗
      apply.isAuthStoreRangeLb st RD (.on γa) n)
  | _ => iprop(True)

instance authStoreLbM_persistent (M : auth.AuthMode) (st : GoInterface) (RD : IProp GF) :
    Persistent (authStoreLbM (GF := GF) M st RD) := by
  cases M <;> unfold authStoreLbM <;> infer_instance

instance authStoreLatestM_persistent (M : auth.AuthMode) (st : GoInterface) (RD : IProp GF)
    (stl : Loc) : Persistent (authStoreLatestM (GF := GF) M st RD stl) := by
  cases M <;> unfold authStoreLatestM <;> infer_instance

/-- **The backend's write contract at every schema auth backend on the backend `bel`**
(persistent; E3l): any `*authBackend` `abl` whose `be` field is `bel` (and some logger) has the
contract. The persistent agreement of E3f's blocker 1: the rest's half of the store's `be` field
(`authBeOn stl bel`) names some such `abl`. -/
def authWBackendAt (bel : Loc) (M : auth.AuthMode) (P : IProp GF) (f : val) (T : IProp GF) :
    IProp GF :=
  iprop(□ ∀ (abl lg : Loc),
    structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"be" abl ↦□
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
        #bel : GoInterface) -∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"lg" abl ↦□ lg -∗
    auth.authWBackendOk (authBkIface abl) M P f T)

instance authWBackendAt_persistent (bel : Loc) (M : auth.AuthMode) (P : IProp GF) (f : val)
    (T : IProp GF) : Persistent (authWBackendAt (GF := GF) bel M P f T) := by
  unfold authWBackendAt; infer_instance

/-- **The store's backend `be` is a schema auth backend on `bel`** (persistent; E3l): what of
`authBeOn` is kept while its half of the field is lent. -/
def beOn (bel : Loc) (be : go_etcd_io.etcd.server.v3.auth.AuthBackend) : IProp GF :=
  iprop(∃ (abl lg : Loc), ⌜be = authBkIface abl ∧ lg ≠ null⌝ ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"be" abl ↦□
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
        #bel : GoInterface) ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"lg" abl ↦□ lg)

instance beOn_persistent (bel : Loc) (be : go_etcd_io.etcd.server.v3.auth.AuthBackend) :
    Persistent (beOn (GF := GF) bel be) := by
  unfold beOn; infer_instance

/-- **The admin steps' resource of the server's store** (E3l): the store's half of its `be` field
with the backend's write contract there, the write token `T`, the field's backend a schema auth
backend on `bel` (`beOn`), and the provider's admin share. -/
def adminW (stl bel : Loc) (M : auth.AuthMode) (P : IProp GF) (f : val) (T : IProp GF) :
    IProp GF :=
  iprop((∃ be : go_etcd_io.etcd.server.v3.auth.AuthBackend,
      ((auth.aF go!"be" stl ↦{DFrac.own (1 : Qp).half} be ∗ auth.authWBackendOk be M P f T) ∗ T) ∗
      beOn bel be) ∗ auth.tpAdmin stl M)

/-- **The apply thread's auth resource with the admin steps' facts at the hook `Pk f`** (E3l;
the hook a parameter since E3n): `authApplyResAt`'s, with, in the mode `on γa`, the write contract
at every schema auth backend on `bel` (`authWBackendAt`) and the store's admin steps at `adminW`
(`apply.isAuthStepsX`), both at the backend's post-lock hook `Pk f` (the server's: the apply
environment's `E.P`, `E.f`, `srvAuthApplyResB`). -/
def authApplyResB (M : auth.AuthMode) (stl : Loc) (st : auth.AuthState) (bel : Loc)
    (Pk : IProp GF) (f : val) : IProp GF :=
  match M with
  | .on γa => iprop(∃ (hs : List auth.AuthState) (P : IProp GF) (f0 : val) (T : IProp GF)
      (be : GoInterface), auth.authOwnFu γa hs ∗ auth.tieRes stl (.on γa) hs ∗
      auth.authWBackendOk be (.on γa) P f0 T ∗ T ∗ auth.tpAdmin stl (.on γa) ∗
      ⌜hs.getLast? = some st⌝ ∗ authWBackendAt bel (.on γa) Pk f T ∗
      apply.isAuthStepsX (auth.authIface stl) Pk f (.on γa) (auth.tieRes stl (.on γa))
        (adminW stl bel (.on γa) Pk f T))
  | _ => iprop(True)

/-- **The admin steps' facts at whichever post-lock hook the server will freeze** (E3n; persistent):
for the real backend `d` with its frozen hook `f'` (not `nil`) at the batch lock `Pk'`, the write
contract at every schema auth backend on `d`'s backend and the store's admin steps there, at the
write token `T`. -/
def authStepsAtHook (stl : Loc) (d : mvcc.KBReal) (γa : auth.AuthNames) (T : IProp GF) : IProp GF :=
  iprop(□ ∀ (W' Pk' : IProp GF) (f' : GoFunc),
    backend.isBackend d.γB d.P W' Pk' d.be -∗ backend.plHookRO d.γB f' -∗ ⌜f' ≠ func.nil⌝ -∗
    authWBackendAt d.be (.on γa) Pk' #f' T ∗
      apply.isAuthStepsX (auth.authIface stl) Pk' #f' (.on γa) (auth.tieRes stl (.on γa))
        (adminW stl d.be (.on γa) Pk' #f' T))

instance authStepsAtHook_persistent (stl : Loc) (d : mvcc.KBReal) (γa : auth.AuthNames) (T : IProp GF) :
    Persistent (authStepsAtHook (GF := GF) stl d γa T) := by
  unfold authStepsAtHook; infer_instance

/-- **The apply thread's auth resource before the hook is frozen** (E3n): `authApplyResB`'s with
its hook-dependent facts for every frozen hook (`authStepsAtHook`), what the store's construction
gives (`authStoreKit`'s post); `authApplyResB_of_pre` instantiates it at the server's hook. -/
def authApplyResPre (M : auth.AuthMode) (stl : Loc) (st : auth.AuthState) (d : mvcc.KBReal) :
    IProp GF :=
  match M with
  | .on γa => iprop(∃ (hs : List auth.AuthState) (P : IProp GF) (f0 : val) (T : IProp GF)
      (be : GoInterface), auth.authOwnFu γa hs ∗ auth.tieRes stl (.on γa) hs ∗
      auth.authWBackendOk be (.on γa) P f0 T ∗ T ∗ auth.tpAdmin stl (.on γa) ∗
      ⌜hs.getLast? = some st⌝ ∗ authStepsAtHook stl d γa T)
  | _ => iprop(True)

/-- **The rest resource lends the store's half of `be` at the same rest value** (E3n; persistent):
what the apply thread holds (`E.RO`, the rest buckets with the objects' backend parts) lends
`authBeOn stl bel` to an admin entry's application and takes it back, the rest buckets kept. -/
def roLendsAuthBe (RO : apply.RestM → IProp GF) (stl bel : Loc) : IProp GF :=
  iprop(□ ∀ r : apply.RestM, RO r -∗ authBeOn stl bel ∗ (authBeOn stl bel -∗ RO r))

instance roLendsAuthBe_persistent (RO : apply.RestM → IProp GF) (stl bel : Loc) :
    Persistent (roLendsAuthBe RO stl bel) := by
  unfold roLendsAuthBe; infer_instance

/-- **The server's row for its apply thread's auth resource** (E3l): the store its `authStore`
field holds, `authApplyResB` in the environment's mode on the backend `bel` at the environment's
hook (`E.P`, `E.f`), and the equation of the backend names: the environment's write right lends
the store's half of `be` on `bel`, and (E3n) so does its rest resource, at the same rest value. -/
def srvAuthApplyResB (s : Loc) (E : apply.AEnv GF) (st : auth.AuthState) : IProp GF :=
  iprop(∃ (stl bel : Loc), structFieldRef go_etcd_io.etcd.server.v3.etcdserver.EtcdServer
      go!"authStore" s ↦□ (auth.authIface stl) ∗ authApplyResB E.authMode stl st bel E.P E.f ∗
    rwLens E.RW (authBeOn stl bel) ∗ roLendsAuthBe E.RO stl bel)

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

open Iris.ProofMode

/-- `authApplyResB` forgets its admin steps' facts into `authApplyResAt`. -/
theorem authApplyResAt_of_B (M : auth.AuthMode) (stl : Loc) (st : auth.AuthState) (bel : Loc)
    (Pk : IProp GF) (f : val) :
    authApplyResB (GF := GF) M stl st bel Pk f ⊢ authApplyResAt M stl st := by
  cases M with
  | on γa =>
    unfold authApplyResB authApplyResAt
    iintro ⟨%hs, %P, %f0, %T, %be, Ho, HX, #Hw, HT, Htp, %Hl, -, -⟩
    iexists hs, P, f0, T, be
    iframe Ho HX Hw HT Htp
    ipureintro; exact Hl
  | off => unfold authApplyResB authApplyResAt; iintro -; itrivial
  | any => unfold authApplyResB authApplyResAt; iintro -; itrivial

/-- **The construction's auth resource at the server's frozen hook** (E3n): `authApplyResPre`
instantiated at a real backend `d` on `bel` with its frozen hook `f` at the batch lock `Pk`. -/
theorem authApplyResB_of_pre (M : auth.AuthMode) (stl : Loc) (st : auth.AuthState)
    (d : mvcc.KBReal) (W Pk : IProp GF) (f : GoFunc) :
    authApplyResPre (GF := GF) M stl st d ∗ backend.isBackend d.γB d.P W Pk d.be ∗
      backend.plHookRO d.γB f ∗ ⌜f ≠ func.nil⌝ ⊢ authApplyResB M stl st d.be Pk #f := by
  cases M with
  | on γa =>
    unfold authApplyResPre authApplyResB
    iintro ⟨⟨%hs, %P, %f0, %T, %be, Ho, HX, #Hw, HT, Htp, %Hl, #Hat⟩, #HB, #Hhk, %Hnn⟩
    iunfold authStepsAtHook at Hat
    ihave ⟨#Hwa, #Hst⟩ := Hat $$ %W %Pk %f HB Hhk []
    · ipureintro; exact Hnn
    iexists hs, P, f0, T, be
    iframe Ho HX Hw HT Htp Hwa Hst
    ipureintro; exact Hl
  | off => unfold authApplyResPre authApplyResB; iintro -; itrivial
  | any => unfold authApplyResPre authApplyResB; iintro -; itrivial

/-- `srvAuthApplyResB` forgets into `srvAuthApplyResAt`. -/
theorem srvAuthApplyResAt_of_B (s : Loc) (E : apply.AEnv GF) (st : auth.AuthState) :
    srvAuthApplyResB (GF := GF) s E st ⊢ srvAuthApplyResAt s E st := by
  unfold srvAuthApplyResB srvAuthApplyResAt
  iintro ⟨%stl, %bel, #Hf, H, -, -⟩
  iexists stl
  iframe Hf
  iapply authApplyResAt_of_B $$ H

/-- **The rest's half of the store's `be` field, as the admin steps' write resource** (E3l):
with the write contract at every schema auth backend on `bel` and the write token. -/
theorem adminW_of_beOn (stl bel : Loc) (M : auth.AuthMode) (P : IProp GF) (f : val)
    (T : IProp GF) :
    authBeOn (GF := GF) stl bel ∗ authWBackendAt bel M P f T ∗ T ⊢
      ∃ be : go_etcd_io.etcd.server.v3.auth.AuthBackend,
        ((auth.aF go!"be" stl ↦{DFrac.own (1 : Qp).half} be ∗ auth.authWBackendOk be M P f T) ∗ T) ∗
        beOn bel be := by
  iintro ⟨Hb, #Hall, HT⟩
  iunfold authBeOn at Hb
  icases Hb with ⟨%abl, %lg, %Hlg, Hbe, #Habbe, #Hablg⟩
  iexists (authBkIface abl)
  iunfold authWBackendAt at Hall
  ihave #Hok := Hall $$ %abl %lg Habbe Hablg
  iframe Hbe Hok HT
  iunfold beOn
  iexists abl, lg
  iframe Habbe Hablg
  ipureintro; exact ⟨rfl, Hlg⟩

/-- **The admin steps' write resource back as the rest's half** (E3l): the token stays. -/
theorem beOn_of_adminW (stl bel : Loc) (M : auth.AuthMode) (P : IProp GF) (f : val)
    (T : IProp GF) (be : go_etcd_io.etcd.server.v3.auth.AuthBackend) :
    ((auth.aF go!"be" stl ↦{DFrac.own (1 : Qp).half} be ∗ auth.authWBackendOk be M P f T) ∗ T) ∗
      beOn bel be ⊢ authBeOn (GF := GF) stl bel ∗ T := by
  iintro ⟨⟨⟨Hbe, -⟩, HT⟩, #Hon⟩
  iunfold beOn at Hon
  icases Hon with ⟨%abl, %lg, ⟨%Hab, %Hlg⟩, #Habbe, #Hablg⟩
  subst Hab
  iframe HT
  iunfold authBeOn
  iexists abl, lg
  iframe Hbe Habbe Hablg
  ipureintro; exact Hlg

/-- **The environment's write right lends the store's half on its backend** (E3l): of
`srvRestRWH`'s objects (`srvObjsOn`), as the server builds `E.RW`. -/
theorem rwLens_authBeOn (γB : backend.BNames) (al stl lp cl bel : Loc) :
    ⊢ rwLens (GF := GF) (srvRestRWH γB (srvObjsOn al stl lp cl bel)) (authBeOn stl bel) := by
  iunfold rwLens
  iintro !> HRW
  iunfold srvRestRWH at HRW
  icases HRW with ⟨Hrw, Hobj⟩
  iunfold srvObjsOn at Hobj
  icases Hobj with ⟨Hal, Hau, Hle, Hcl⟩
  iframe Hau
  iintro Hau
  iunfold srvRestRWH
  iframe Hrw
  iunfold srvObjsOn
  iframe Hal Hau Hle Hcl

/-- **The server's rest resource lends the store's half on its backend** (E3n): of
`srvRestOwnH`'s objects (`srvObjsOn`), as the server builds `E.RO`. -/
theorem roLends_authBeOn (γB : backend.BNames) (c al stl lp cl bel : Loc) :
    ⊢ roLendsAuthBe (GF := GF) (srvRestOwnH γB c (srvObjsOn al stl lp cl bel)) stl bel := by
  iunfold roLendsAuthBe
  iintro !> %r HRO
  iunfold srvRestOwnH at HRO
  icases HRO with ⟨Hr, Hobj⟩
  iunfold srvObjsOn at Hobj
  icases Hobj with ⟨Hal, Hau, Hle, Hcl⟩
  iframe Hau
  iintro Hau
  iunfold srvRestOwnH
  iframe Hr
  iunfold srvObjsOn
  iframe Hal Hau Hle Hcl

end lemmas

end EtcdGrove
end Perennial
