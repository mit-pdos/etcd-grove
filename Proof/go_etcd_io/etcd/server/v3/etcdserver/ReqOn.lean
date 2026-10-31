/-
**The request path in either auth mode** (the auth plan's E3b, 2026-10-26; `notes/decisions.md`,
"E3b of the auth plan"). The wait's results (`entryWit`, `resultΨ`, `reqWaitR`, `waitInv`), the
proposer's view of the server (`srvReqFieldsAt`, `isServerReq`) and the proposal's permission
(`reqPropOk`) name the mode-off KV model (`kvModel`, `kvInv`); E2z found that the mode-`on` server
needs each over the mode-`on` model (`kvModelOn`, `kvInvOn`, E2q). Here are their mode-indexed
counterparts, each today's at `on = false` by definition (`kvModelM_false`, `resultΨM_false`, ...:
the match reduces), so nothing mode-off changes:

- `kvModelM`: `kvModel` off, `kvModelOn … srvAuthSt0` on.
- `resultΨM`: the result the proposer expects, `resultΨ` off, `resultΨOn` on: the result with the
  auth state `st` and the log `lb` the entry met (`entryWitOn`: the mode-`on` model of the raft
  prefix before it is `(st, lb)`) and **the auth layer's verdict the model's** (`authTie`: a KV
  request was rejected by the auth layer exactly when `st` does not grant it), which the apply thread
  in the mode `on` hands over (E2t/E2y's `outcomeOn`). `reqWaitRM`, `waitInvM`, `srvReqFieldsAtM`,
  `isServerReqM`: the wait's registration and the proposer's view over it and `kvInvM` (E2w).
- `resPostM`: the applied result as `processInternalRaftRequestOnce.specM` reports it.
- `reqPropOkM`: the proposal's permission **at the wire request**. In the mode `on` the check reads
  the request's principal, the header `processInternalRaftRequestOnce` fills in from the context
  (`AuthInfoFromCtx`) before it proposes, so the result `Qh hm` is a function of that header: for
  every header `hm`, `reqPropOkOn` of `withHeader rq hm` (E2w's, at the request the apply thread
  decodes); off, `reqPropOk` with a result not reading the header.
- `kv_prop_au_M`: the proposal's update from `kvInvM`, at the decoded request (`irrWireOf`):
  `kv_prop_au` off (through `reqPropOk_wire`), `kv_prop_au_on` on (the wire request is the
  stamped one, `irrNoZeroEnd`).

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ServerOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ProposeOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthBound
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__AuthInfoFromCtx

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

/-- The header the server stamps is all `withHeader` changes: its kind, its KV operation, its
permissions and its shape facts are the request's. -/
theorem irrNoZeroEnd_withHeader (rq : apply.IRRModel) (hm : apply.HeaderModel) :
    irrNoZeroEnd (apply.withHeader rq hm) ↔ irrNoZeroEnd rq := Iff.rfl

theorem reqPerms_withHeader (rq : apply.IRRModel) (hm : apply.HeaderModel) :
    reqPerms (apply.withHeader rq hm) = reqPerms rq := rfl

theorem kvShapeAll_withHeader (rq : apply.IRRModel) (hm : apply.HeaderModel) :
    kvShapeAll (apply.withHeader rq hm) ↔ kvShapeAll rq := Iff.rfl

theorem reqKVOp_withHeader (rq : apply.IRRModel) (hm : apply.HeaderModel) :
    reqKVOp (apply.withHeader rq hm) = reqKVOp rq := rfl

/-- **The principal the check reads is the stamped header's** (`kvGranted`'s `principalOf`). -/
theorem principalOf_withHeader (rq : apply.IRRModel) (hm : apply.HeaderModel) :
    apply.principalOf (apply.withHeader rq hm) = ⟨hm.username, hm.authRevision⟩ := rfl

/-- **The wire request is the stamped one** when no range end is `[0]` (`irrWireOf`). -/
theorem irrWireOf_eq (rq rq' : apply.IRRModel) (hm : apply.HeaderModel)
    (hw : irrWireOf (apply.withHeader rq hm) rq') (hz : irrNoZeroEnd rq) :
    rq' = apply.withHeader rq hm :=
  hw.2.2.2 hz

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The auth layer's verdict is the model's** (`authTie st rq out`): an application of the KV
request `rq` dispatched to the outcome `o` was rejected by the auth layer exactly when the model's
auth state `st` (the state the entry met) does not grant it (`kvGranted`). What the apply thread in
the mode `on` knows of every KV entry it applies (E2t's `outcomeOn`, at the apply layer E2y's
`outcomeOn_of_kvOutL`), handed to the proposer with the result. -/
def authTie (st : auth.AuthState) (rq : apply.IRRModel) (out : apply.ApplyOut) : Prop :=
  apply.isKVKind (apply.dispatchKind rq) = true → ∀ o skip, out = .dispatched o skip →
    (o = .rejected .auth ↔ ¬ kvGranted st rq)

/-- **An `Authenticate` entry's response** (C1's A2, 2026-10-28): unless the entry is not an
`Authenticate` or was not dispatched, the result at `ar` holds the response (`Resp`, a pointer to
an `AuthenticateResponse`) and its error, and the response is what the store returned
(`apply.authnOut`: an error and no response, or a token issued to the request's user). -/
def adminAuthnAr (γa : auth.AuthNames) (ar : Loc) (rq : apply.IRRModel) (out : apply.ApplyOut) :
    IProp GF :=
  iprop(⌜apply.dispatchKind rq ≠ .authenticate ∨ ∀ o b, out ≠ .dispatched o b⌝ ∨
    ∃ (am : apply.AuthenticateModel) (v : go_etcd_io.etcd.server.v3.etcdserver.apply.Result)
      (resp : Loc),
      ⌜rq.authenticate = some am ∧
        v.Resp' = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.api.v3.etcdserverpb.AuthenticateResponse.ty)
          #resp⌝ ∗
      ar ↦□ v ∗ apply.authnOut γa am.name resp v.Err')

/-- **An `Authenticate` result's response, in the auth mode `on`** (C1's A3, 2026-10-28): `True`
off, and at an auth mode other than `.on` (`.any` promises nothing); at `.on γa`, `adminAuthnAr`,
the response the store returned, owned, for the waiter. -/
def authnArM (on : Bool) (E : apply.AEnv GF) (ar : Loc) (rq : apply.IRRModel) (out : apply.ApplyOut) :
    IProp GF :=
  match on with
  | false => iprop(True)
  | true =>
    match E.authMode with
    | .on γa => adminAuthnAr γa ar rq out
    | _ => iprop(True)

theorem authnArM_false (E : apply.AEnv GF) (ar : Loc) (rq : apply.IRRModel) (out : apply.ApplyOut) :
    authnArM (GF := GF) false E ar rq out = iprop(True) := rfl

/-- **Not an `Authenticate`: nothing to carry.** -/
theorem authnArM_of_ne (on : Bool) (E : apply.AEnv GF) (ar : Loc) (rq : apply.IRRModel)
    (out : apply.ApplyOut) (h : apply.dispatchKind rq ≠ .authenticate) :
    ⊢ authnArM (GF := GF) on E ar rq out := by
  cases on
  · simp only [authnArM]; itrivial
  simp only [authnArM]
  cases E.authMode with
  | off => itrivial
  | any => itrivial
  | on γa => iunfold adminAuthnAr; ileft; ipureintro; exact Or.inl h

/-- **At the server's auth mode `.on γa`**, `adminAuthnAr` is `authnArM`'s. -/
theorem authnArM_of_on (E : apply.AEnv GF) (γa : auth.AuthNames) (ar : Loc) (rq : apply.IRRModel)
    (out : apply.ApplyOut) (hM : E.authMode = .on γa) :
    adminAuthnAr (GF := GF) γa ar rq out ⊢ authnArM true E ar rq out := by
  simp only [authnArM, hM]
  iintro H; iexact H

/-- **The result `ar` of applying `rq`, with its witness, in the mode `on`** (`resultIsW`'s, with
the auth layer's verdict the model's at the auth state `st` the entry met, `authTie`; and (E3x) an
admin request's result without error the model's step from `st` succeeding, `adminTieAr`; and (C1's
A3) an `Authenticate`'s response, owned, `authnArM`). -/
def resultIsWOn (E : apply.AEnv GF) (γr : ReadNames) (rq : apply.IRRModel) (F : mvcc.Log)
    (ar : Loc) (lb : mvcc.Log) (st : auth.AuthState) : IProp GF :=
  iprop(⌜ar ≠ null⌝ ∗
    ∃ (y y' : apply.ApplyKV) (out : apply.ApplyOut),
      ⌜apply.applyStep rq true y y' out ∧ apply.applyFloorOk rq true F y.log out ∧ y.log = lb ∧
        out.waived = false ∧ authTie st rq out⌝ ∗
      apply.applyResultIs rq true y.log ar out ∗
      mvcc.idxCert E.γ.idx y'.log ∗ revMinted E y.log y'.log ∗ appliedWit γr y'.log ∗
      mvcc.certOk E.γ y'.log ∗ adminTieAr ar rq st (adminNext rq st) out ∗
      authnArM true E ar rq out)

/-- `resultIsWOn` forgets to `resultIsW`. -/
theorem resultIsW_of_on (E : apply.AEnv GF) (γr : ReadNames) (rq : apply.IRRModel) (F : mvcc.Log)
    (ar : Loc) (lb : mvcc.Log) (st : auth.AuthState) :
    resultIsWOn (GF := GF) E γr rq F ar lb st ⊢ resultIsW E γr rq F ar lb := by
  iunfold resultIsWOn
  iunfold resultIsW
  iintro ⟨%Hnn, %y, %y', %out, %Hs, Hr, Hc, Hm, Hw, Hk, -⟩
  isplitr
  · ipureintro; exact Hnn
  iexists y, y', out
  iframe Hr Hc Hm Hw Hk
  ipureintro; exact ⟨Hs.1, Hs.2.1, Hs.2.2.1, Hs.2.2.2.1⟩

/-- **The committed entry a result is of, in the mode `on`** (`entryWit`'s, see the file header):
the mode-`on` model of the raft prefix before it is `(st, lb)`, the auth state and the log the
entry met; (the auth plan's E3t, 2026-10-27) and the auth state after it, the model's of the prefix
through it, published (`authPubAt M`: a reader holding it is checked at states no older). -/
def entryWitOn (M : auth.AuthMode) (ρ : ReqNames) (rq : apply.IRRModel) (lb : mvcc.Log)
    (st : auth.AuthState) : IProp GF :=
  iprop(∃ (L : List EntryModel) (m : Nat) (e : EntryModel) (id : w64) (γf : GName),
    srvRLogLb ρ.raft L ∗ idClaim ρ.ids id e.data γf ∗
    ⌜L[m]? = some e ∧ e.typ = W32 0 ∧ apply.irrDecode e.data = some rq ∧
      apply.irrId rq = some id ∧
      kvRaftOfOn ρ.kv.c0 ρ.kv.ch0 (srvAuthSt0, ρ.kv.log0) (L.take m) = (st, lb)⌝ ∗
    authPubAt M (kvRaftOfOn ρ.kv.c0 ρ.kv.ch0 (srvAuthSt0, ρ.kv.log0) (L.take (m + 1))).1)

instance entryWitOn_persistent (M : auth.AuthMode) (ρ : ReqNames) (rq : apply.IRRModel)
    (lb : mvcc.Log) (st : auth.AuthState) :
    Persistent (entryWitOn (GF := GF) M ρ rq lb st) := by
  unfold entryWitOn; infer_instance

/-- **The result the proposer expects in the mode `on`** (`resultΨ`'s, with `resultIsWOn` and
`entryWitOn` at the auth state and the log the entry met, with the state after it published). -/
def resultΨOn (E : apply.AEnv GF) (ρ : ReqNames) (rq : apply.IRRModel) (F : mvcc.Log)
    (x : GoInterface) : IProp GF :=
  iprop(∃ (ar : Loc) (lb : mvcc.Log) (st : auth.AuthState),
    ⌜x = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.Result.ty) #ar⌝ ∗
    apply.resTrace ar ∗ resultIsWOn E ρ.rd rq F ar lb st ∗ entryWitOn E.authMode ρ rq lb st)

/-- **The result the proposer expects, in the auth mode `on`**: `resultΨ` off, `resultΨOn` on. -/
def resultΨM (on : Bool) (E : apply.AEnv GF) (ρ : ReqNames) (rq : apply.IRRModel) (F : mvcc.Log) :
    GoInterface → IProp GF :=
  match on with
  | false => resultΨ E ρ rq F
  | true => resultΨOn E ρ rq F

theorem resultΨM_false (E : apply.AEnv GF) (ρ : ReqNames) (rq : apply.IRRModel) (F : mvcc.Log) :
    resultΨM (GF := GF) false E ρ rq F = resultΨ E ρ rq F := rfl

theorem resultΨM_true (E : apply.AEnv GF) (ρ : ReqNames) (rq : apply.IRRModel) (F : mvcc.Log) :
    resultΨM (GF := GF) true E ρ rq F = resultΨOn E ρ rq F := rfl

/-- **What the proposer learns of the model at the entry its result is of**, the outcome `out` met
at the log `lb` after the committed prefix `L`: off, `lb` the mode-off model of `L`; on, `(st, lb)`
the mode-`on` model of `L` and the auth layer's verdict the model's grant at `st` (`authTie`). -/
def modelOutM (on : Bool) (γk : KVNames) (rq : apply.IRRModel) (L : List EntryModel)
    (lb : mvcc.Log) (out : apply.ApplyOut) : Prop :=
  match on with
  | false => kvModel γk L = lb
  | true => ∃ st, kvRaftOfOn γk.c0 γk.ch0 (srvAuthSt0, γk.log0) L = (st, lb) ∧ authTie st rq out

/-- **An admin result's tie as the proposer reports it, in the auth mode `on`** (E3x): `True` off;
on, `adminTieAr` at the auth state the mode-`on` model of the committed prefix `L` reaches (the
state the entry met) and the model's step from it. -/
def adminTieM (on : Bool) (γk : KVNames) (rq : apply.IRRModel) (L : List EntryModel) (ar : Loc)
    (out : apply.ApplyOut) : IProp GF :=
  match on with
  | false => iprop(True)
  | true =>
    let st := (kvRaftOfOn γk.c0 γk.ch0 (srvAuthSt0, γk.log0) L).1
    adminTieAr ar rq st (adminNext rq st) out

instance adminTieM_persistent (on : Bool) (γk : KVNames) (rq : apply.IRRModel)
    (L : List EntryModel) (ar : Loc) (out : apply.ApplyOut) :
    Persistent (adminTieM (GF := GF) on γk rq L ar out) := by
  cases on <;> unfold adminTieM <;> infer_instance

/-- **An admin request applied without error, as the proposer learns it, in the auth mode `on`**
(E3x): nothing off; on, an admin request's step from the state the mode-`on` model of the committed
prefix `L` reaches succeeded (`adminStepOk`), to the model's step (`adminNext`): the state after
the entry, `kvRaftOfOn` of `L` and the entry. -/
def adminDoneM (on : Bool) (γk : KVNames) (rq : apply.IRRModel) (L : List EntryModel) : Prop :=
  match on with
  | false => True
  | true =>
    let st := (kvRaftOfOn γk.c0 γk.ch0 (srvAuthSt0, γk.log0) L).1
    apply.needAdminPermission rq = true → adminStepOk rq st (adminNext rq st)

/-- **The applied result as the proposer reports it, in the auth mode `on`** (the success post of
`processInternalRaftRequestOnce.specM`): `resultIsW`'s, at the committed prefix `L` before the
entry, with what the proposer learns of the model there (`modelOutM`); (C1's A3) an
`Authenticate`'s response, `authnArM`. -/
def resPostM (on : Bool) (E : apply.AEnv GF) (ρ : ReqNames) (rq : apply.IRRModel) (F : mvcc.Log)
    (ar : Loc) (L : List EntryModel) : IProp GF :=
  iprop(⌜ar ≠ null⌝ ∗
    ∃ (y y' : apply.ApplyKV) (out : apply.ApplyOut),
      ⌜apply.applyStep rq true y y' out ∧ apply.applyFloorOk rq true F y.log out ∧
        out.waived = false ∧ modelOutM on ρ.kv rq L y.log out⌝ ∗
      apply.applyResultIs rq true y.log ar out ∗
      mvcc.idxCert E.γ.idx y'.log ∗ revMinted E y.log y'.log ∗ appliedWit ρ.rd y'.log ∗
      mvcc.certOk E.γ y'.log ∗ adminTieM on ρ.kv rq L ar out ∗ authnArM on E ar rq out)

/-- **The auth state after a request's entry, published, in the auth mode `on`** (the auth plan's
E3t, 2026-10-27; persistent): `True` off; on, the entry `e` of `rq'` committed right after the
prefix `L` (`L ++ [e]`), and the mode-`on` model's auth state after it published (`authPubAt`: a
reader holding it is checked at states no older, `Range.specOn`). What the apply thread hands the
waiter (`entryWitOn`), as the proposer reports it. -/
def pubAfterM (on : Bool) (E : apply.AEnv GF) (ρ : ReqNames) (rq' : apply.IRRModel)
    (L : List EntryModel) : IProp GF :=
  match on with
  | false => iprop(True)
  | true => iprop(∃ e : EntryModel, srvRLogLb ρ.raft (L ++ [e]) ∗
      ⌜e.typ = W32 0 ∧ e.data ≠ [] ∧ apply.irrDecode e.data = some rq'⌝ ∗
      authPubAt E.authMode (kvRaftOfOn ρ.kv.c0 ρ.kv.ch0 (srvAuthSt0, ρ.kv.log0) (L ++ [e])).1)

instance pubAfterM_persistent (on : Bool) (E : apply.AEnv GF) (ρ : ReqNames) (rq' : apply.IRRModel)
    (L : List EntryModel) : Persistent (pubAfterM (GF := GF) on E ρ rq' L) := by
  cases on <;> unfold pubAfterM <;> infer_instance

/-- **An `Authenticate`'s answer, as `raftRequest` reports it, in the auth mode `on`** (C1's A3,
2026-10-28): `True` off (and at an auth mode other than `.on`); on, unless the request is not an
`Authenticate`, the answer is a pointer to an `AuthenticateResponse`, owned (the reply the handler
sends), whose token is issued to the request's user (`auth.tokIssued`). The response's header (a
fresh `newHeader()`) is not owned: the handler returns the response as it is. -/
def authnAnsM (on : Bool) (E : apply.AEnv GF) (rq : apply.IRRModel) (resp : GoInterface) : IProp GF :=
  match on with
  | false => iprop(True)
  | true =>
    match E.authMode with
    | .on γa => iprop(⌜apply.dispatchKind rq ≠ .authenticate⌝ ∨
        ∃ (am : apply.AuthenticateModel) (rp : Loc) (v : go_etcd_io.etcd.api.v3.etcdserverpb.AuthenticateResponse),
          ⌜rq.authenticate = some am ∧
            resp = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.api.v3.etcdserverpb.AuthenticateResponse.ty) #rp⌝ ∗
          rp ↦ v ∗ auth.tokIssued γa v.Token' am.name)
    | _ => iprop(True)

theorem authnAnsM_false (E : apply.AEnv GF) (rq : apply.IRRModel) (resp : GoInterface) :
    authnAnsM (GF := GF) false E rq resp = iprop(True) := rfl

/-- **An `Authenticate`'s answer from its result** (C1's A3): a result `ar` dispatched without
error carries its response (`authnArM`), which `raftRequest` returns as its answer. -/
theorem authnAnsM_of_ar (on : Bool) (E : apply.AEnv GF) (ar : Loc) (rq : apply.IRRModel)
    (o : apply.Outcome) (skip : Bool) (v : go_etcd_io.etcd.server.v3.etcdserver.apply.Result)
    (hve : v.Err' = GoInterface.nil) :
    authnArM (GF := GF) on E ar rq (.dispatched o skip) ⊢ ar ↦□ v -∗ authnAnsM on E rq v.Resp' := by
  cases on
  · iintro - -; simp only [authnAnsM]; itrivial
  simp only [authnArM, authnAnsM]
  cases E.authMode with
  | off => iintro - -; itrivial
  | any => iintro - -; itrivial
  | on γa =>
    simp only
    iintro Hau #Hv
    iunfold adminAuthnAr at Hau
    icases Hau with (%Hn | ⟨%am, %v', %resp, %Hr, #Hv', Hout⟩)
    · ileft; ipureintro
      rcases Hn with Hn | Hn
      · exact Hn
      · exact absurd rfl (Hn o skip)
    icombine Hv Hv' gives %Hvv
    subst Hvv
    iright
    iunfold apply.authnOut at Hout
    icases Hout with (⟨%He, -⟩ | ⟨-, %w, Hw, #Ht⟩)
    · exact absurd hve He.1
    iexists am, resp, w
    iframe Hw Ht
    ipureintro; exact Hr

/-- **The apply thread's answer, as `raftRequest` reports it, in the auth mode `on`** (`appliedOk`'s
at the committed prefix `L` before the entry, with `modelOutM`; and (E3x) an admin request's step
succeeded, `adminDoneM`; (C1's A3) an `Authenticate`'s response and its token's issue,
`authnAnsM`). -/
def appliedOkM (on : Bool) (E : apply.AEnv GF) (ρ : ReqNames) (rq' : apply.IRRModel) (F : mvcc.Log)
    (resp : GoInterface) (L : List EntryModel) : IProp GF :=
  iprop(∃ (x x' : apply.ApplyKV) (o : apply.Outcome) (skip : Bool),
    ⌜apply.applyStep rq' true x x' (.dispatched o skip) ∧ apply.kvFloorOk rq' true F x.log o ∧
      skip = false ∧ modelOutM on ρ.kv rq' L x.log (.dispatched o skip) ∧ adminDoneM on ρ.kv rq' L⌝ ∗
    apply.dispatchAnswer rq' x.log skip resp GoInterface.nil null o ∗ mvcc.idxCert E.γ.idx x'.log ∗
    revMinted E x.log x'.log ∗ appliedWit ρ.rd x'.log ∗ mvcc.certOk E.γ x'.log ∗
    authnAnsM on E rq' resp)

/-- **The server's registration condition, in the auth mode `on`** (`reqWaitR` with `resultΨM`). -/
def reqWaitRM (on : Bool) (ρ : ReqNames) (E : apply.AEnv GF) (id : w64)
    (Ψ : GoInterface → IProp GF) : IProp GF :=
  iprop(∃ (d : List w8) (rq : apply.IRRModel) (γf : GName) (F : mvcc.Log), idClaim ρ.ids id d γf ∗
    floorAt γf F ∗ ⌜apply.irrDecode d = some rq ∧ Ψ = resultΨM on E ρ rq F ∧ idPfx id = ρ.ids.pfx⌝)

theorem reqWaitRM_false (ρ : ReqNames) (E : apply.AEnv GF) :
    reqWaitRM (GF := GF) false ρ E = reqWaitR ρ E := rfl

/-- **The server's wait, in the auth mode `on`** (`waitInv` with `reqWaitRM`). -/
def waitInvM (on : Bool) (w : GoInterface) (ρ : ReqNames) (E : apply.AEnv GF) : IProp GF :=
  iprop((∃ RD : IProp GF, isWait w ρ.ids ρ.wait (reqWaitRM on ρ E) RD) ∗
    idWaitIs ρ.ids ρ.ids.pfx ρ.wait)

instance waitInvM_persistent (on : Bool) (w : GoInterface) (ρ : ReqNames) (E : apply.AEnv GF) :
    Persistent (waitInvM (GF := GF) on w ρ E) := by
  unfold waitInvM; infer_instance

theorem waitInvM_false (w : GoInterface) (ρ : ReqNames) (E : apply.AEnv GF) :
    waitInvM (GF := GF) false w ρ E = waitInv w ρ E := rfl

/-- **The applied and committed indices' invariants in the auth mode `on`** (`srvIndexInvs` at
`false`, by definition; the auth plan's E3r, 2026-10-27: with auth on the server's applied index's
invariant is `srvAppliedInvM true`, the only one at its atomic). -/
def srvIndexInvsM (on : Bool) (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(∃ γr : ReadNames, srvAppliedInvM on s E γr ∗ srvCommittedInv s γr)

instance srvIndexInvsM_persistent (on : Bool) (s : Loc) (E : apply.AEnv GF) :
    Persistent (srvIndexInvsM (GF := GF) on s E) := by
  unfold srvIndexInvsM; infer_instance

theorem srvIndexInvsM_false (s : Loc) (E : apply.AEnv GF) :
    srvIndexInvsM (GF := GF) false s E = srvIndexInvs s E := rfl

/-- **The tie of the KV names' compaction mode, by the auth mode** (M2's apply side, item 19;
review round 6's R6-1): the server's with auth off; nothing with auth on (auth-on servers keep
retention `0`, and `start.specOn` has no producer for it). -/
def kvTieM (on : Bool) (cmp : Bool) (E : apply.AEnv GF) : Prop :=
  match on with
  | false => cmp = E.cmp
  | true => True

theorem kvTieM_off (cmp : Bool) (E : apply.AEnv GF) : kvTieM (GF := GF) false cmp E = (cmp = E.cmp) :=
  rfl

/-- **The server as a proposer sees it, in the auth mode `on`** (`srvReqFieldsAt` with `waitInvM`,
`kvInvM` from the server's start state, `srvAuthSt0`, and (E3r) `srvIndexInvsM`; M2's apply side, item 19:
the mode's tie `kvTieM` and certificates' invariant `kvCertInvM`). -/
def srvReqFieldsAtM (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (v : ReqFields) :
    IProp GF :=
  iprop(structFieldRef EtcdServer go!"reqIDGen" s ↦□ v.gen ∗ idGen ρ.ids v.gen (srvFloorFact E) ∗
    structFieldRef EtcdServer go!"w" s ↦□ v.w ∗ waitInvM on v.w ρ E ∗
    srvRaftNode s ρ.raft ∗
    srvCfgFieldAddr s go!"MaxRequestBytes" ↦□ v.maxReq ∗
    srvCfgFieldAddr s go!"ServerFeatureGate" ↦□ v.fg ∗ isFeatureGate v.fg ∗
    srvCfgFieldAddr s go!"ClientCertAuthEnabled" ↦□ v.cca ∗
    srvCfgFieldAddr s go!"ElectionTicks" ↦□ v.electionTicks ∗
    srvCfgFieldAddr s go!"TickMs" ↦□ v.tickMs ∗
    structFieldRef EtcdServer go!"authStore" s ↦□ v.auth ∗ isReqAuth v.auth E.RD ∗
    structFieldRef EtcdServer go!"done" s ↦□ v.done ∗ srvDoneChan v.done ∗
    structFieldRef EtcdServer go!"memberID" s ↦□ v.memberID ∗
    srvAtomicU64 (structFieldRef EtcdServer go!"lead" s) ∗
    structFieldRef EtcdServer go!"cluster" s ↦□ v.cluster ∗
    structFieldRef raftNodeConfig go!"transport"
      (structFieldRef raftNode go!"raftNodeConfig" (structFieldRef EtcdServer go!"r" s)) ↦□ v.tr ∗
    srvPeersOk v.cluster v.cid v.tr ∗
    srvIndexInvsM on s E ∗
    srvMintInv ρ ∗ kvInvM on ρ.raft ρ.kv srvAuthSt0 ∗ ⌜kvTieM on ρ.kv.cmp E⌝ ∗
    kvCertInvM on ρ.raft ρ.kv srvAuthSt0 ∗ ⌜structFieldRef EtcdServer go!"Cfg" s ≠ null⌝)

instance srvReqFieldsAtM_persistent (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (v : ReqFields) : Persistent (srvReqFieldsAtM (GF := GF) on s E ρ v) := by
  unfold srvReqFieldsAtM; infer_instance

theorem srvReqFieldsAtM_false (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (v : ReqFields) :
    srvReqFieldsAtM (GF := GF) false s E ρ v = srvReqFieldsAt s E ρ v := rfl

/-- **The server's store's bound request side, in the auth mode `on`** (persistent): off, the
environment's auth off (the auth-mode merge's step 5); on, `srvAuthBound` (`AuthInfoFromCtx`'s auth info bound to the request context's token; the auth
plan's E3zb), and the environment's auth on (the auth-mode merge, 2026-10-29: `AuthInfoFromCtx`'s
binding is gated by the mode). -/
def srvAuthBoundM (on : Bool) (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  match on with
  | false => iprop(⌜E.authOn = false⌝)
  | true => iprop(srvAuthBound s E ∗ ⌜E.authOn = true⌝)

instance srvAuthBoundM_persistent (on : Bool) (s : Loc) (E : apply.AEnv GF) :
    Persistent (srvAuthBoundM (GF := GF) on s E) := by
  cases on <;> unfold srvAuthBoundM <;> infer_instance

/-- **The header a request is stamped with names its context's principal, in the auth mode `on`**
(persistent; the auth plan's E3zb): `True` off; on, the header's user is the empty one (the
header of an `Authenticate`, or of a context without a user: the apply thread then grants it no
key), or the user, at the header's auth revision, is bound to the context `ctx` (`principalBound`:
its token was issued to that user, or the server's TLS fallback is on). -/
def hdrBoundM (on : Bool) (s : Loc) (E : apply.AEnv GF) (ctx : GoInterface)
    (hm : apply.HeaderModel) : IProp GF :=
  match on with
  | false => iprop(True)
  | true => iprop(⌜hm.username = (zeroValDef : GoString)⌝ ∨
      principalBound s E.authMode ctx
        (some (go_etcd_io.etcd.server.v3.auth.AuthInfo.mk hm.username hm.authRevision)))

instance hdrBoundM_persistent (on : Bool) (s : Loc) (E : apply.AEnv GF) (ctx : GoInterface)
    (hm : apply.HeaderModel) : Persistent (hdrBoundM (GF := GF) on s E ctx hm) := by
  cases on <;> unfold hdrBoundM <;> infer_instance

/-- **The auth info a read's check saw is the caller's** (persistent; E3zb: `hdrBoundM`'s, for an
auth info): with auth on, the empty user (`doSerialize`'s stand-in for a context with none), or one
bound to the context's token (`principalBound`). Off, `True`. -/
def infoBoundM (on : Bool) (s : Loc) (E : apply.AEnv GF) (ctx : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) : IProp GF :=
  match on with
  | false => iprop(True)
  | true => iprop(⌜info.Username' = (zeroValDef : GoString)⌝ ∨
      principalBound s E.authMode ctx (some info))

instance infoBoundM_persistent (on : Bool) (s : Loc) (E : apply.AEnv GF) (ctx : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) :
    Persistent (infoBoundM (GF := GF) on s E ctx info) := by
  cases on <;> unfold infoBoundM <;> infer_instance

/-- **A writing transaction's error in the auth mode `on`** (`txnErrOk`'s, E3zb): the apply's
error, at a header bound to the context `ctx` (`hdrBoundM`), or the proposal's. -/
def txnErrOkOn (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterface) (F : mvcc.Log)
    (t : TxnModel) (err : GoInterface) : IProp GF :=
  iprop(∃ tw : txn.TxnModelW, ⌜tw.toModel = t⌝ ∗
    ((∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel),
      ⌜irrWireOf (apply.withHeader (irrTxn tw) hm) rq'⌝ ∗ appliedErr E rq' F err ∗
        hdrBoundM true s E ctx hm) ∨
    srvMaybeDeposited ρ (irrTxn tw)))

theorem txnErrOk_of_on (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterface)
    (F : mvcc.Log) (t : TxnModel) (err : GoInterface) :
    txnErrOkOn (GF := GF) s E ρ ctx F t err ⊢ txnErrOk E ρ F t err := by
  unfold txnErrOkOn txnErrOk
  iintro ⟨%tw, %Ht, (⟨%hm, %rq', %Hw, Ha, -⟩ | Hd)⟩
  · iexists tw; isplitr
    · ipureintro; exact Ht
    ileft; iexists hm, rq'; iframe Ha; ipureintro; exact Hw
  · iexists tw; isplitr
    · ipureintro; exact Ht
    iright; iexact Hd

/-- A header with the empty user is bound (`hdrBoundM`). -/
theorem hdrBoundM_empty (on : Bool) (s : Loc) (E : apply.AEnv GF) (ctx : GoInterface)
    (hm : apply.HeaderModel) (h : hm.username = (zeroValDef : GoString)) :
    ⊢ hdrBoundM (GF := GF) on s E ctx hm := by
  cases on <;> unfold hdrBoundM
  · itrivial
  · ileft; ipureintro; exact h

/-- A header stamped from an auth info the store bound to the context (`ctxBoundOrTLS`, with auth
on) is bound (`hdrBoundM`). -/
theorem hdrBoundM_of_ctxBound (on : Bool) (s : Loc) (E : apply.AEnv GF) (ctx : GoInterface)
    (a : Loc) (id : w64) (user : GoString) (rev : w64) :
    (⌜on = true⌝ → ctxBoundOrTLS s E.authMode ctx a) ∗ authInfoIs a user rev ⊢
      hdrBoundM (GF := GF) on s E ctx ⟨id, user, rev⟩ := by
  cases on <;> unfold hdrBoundM
  · iintro -; itrivial
  · iintro ⟨Hb, #Hai⟩
    ihave #Hb' := Hb $$ %rfl
    iright
    iapply principalBound_of_ctxBoundOrTLS s E.authMode ctx a user rev $$ [$Hb' $Hai]

/-- A header bound to a context is bound to any context with the same incoming metadata (the
contexts the server derives from a request's: `Tracer.Start`'s, `WithValue`'s). -/
theorem hdrBoundM_ctx (on : Bool) (s : Loc) (E : apply.AEnv GF) (c c' : GoInterface)
    (hm : apply.HeaderModel) (h : metadata.incomingOf c = metadata.incomingOf c') :
    hdrBoundM (GF := GF) on s E c hm ⊢ hdrBoundM on s E c' hm := by
  have ht : auth.ctxTokenOf c = auth.ctxTokenOf c' := by unfold auth.ctxTokenOf; rw [h]
  cases on <;> unfold hdrBoundM
  · iintro -; itrivial
  · unfold principalBound; rw [ht]

/-- An auth info with the empty user is bound. -/
theorem infoBoundM_empty (on : Bool) (s : Loc) (E : apply.AEnv GF) (ctx : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (h : info.Username' = (zeroValDef : GoString)) :
    ⊢ infoBoundM (GF := GF) on s E ctx info := by
  cases on <;> unfold infoBoundM
  · itrivial
  · ileft; ipureintro; exact h

/-- An auth info the store bound to the context (`ctxBoundOrTLS`, with auth on) is bound. -/
theorem infoBoundM_of_ctxBound (on : Bool) (s : Loc) (E : apply.AEnv GF) (ctx : GoInterface)
    (a : Loc) (user : GoString) (rev : w64) :
    (⌜on = true⌝ → ctxBoundOrTLS s E.authMode ctx a) ∗ authInfoIs a user rev ⊢
      infoBoundM (GF := GF) on s E ctx ⟨user, rev⟩ := by
  cases on <;> unfold infoBoundM
  · iintro -; itrivial
  · iintro ⟨Hb, #Hai⟩
    ihave #Hb' := Hb $$ %rfl
    iright
    iapply principalBound_of_ctxBoundOrTLS s E.authMode ctx a user rev $$ [$Hb' $Hai]

/-- An auth info bound to a context is bound to any context with the same incoming metadata. -/
theorem infoBoundM_ctx (on : Bool) (s : Loc) (E : apply.AEnv GF) (c c' : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (h : metadata.incomingOf c = metadata.incomingOf c') :
    infoBoundM (GF := GF) on s E c info ⊢ infoBoundM on s E c' info := by
  have ht : auth.ctxTokenOf c = auth.ctxTokenOf c' := by unfold auth.ctxTokenOf; rw [h]
  cases on <;> unfold infoBoundM
  · iintro -; itrivial
  · unfold principalBound; rw [ht]

/-- **The server, as a proposer sees it, in the auth mode `on`** (persistent): its fields
(`srvReqFieldsAtM`) and, with auth on, its store's bound request side (`srvAuthBound`, E3zb: the
header a request is stamped with names its context's principal). Off, `isServerReq` by
definition. -/
def isServerReqM (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) : IProp GF :=
  match on with
  | false => iprop((∃ v : ReqFields, srvReqFieldsAtM false s E ρ v) ∗ ⌜E.authOn = false⌝)
  | true => iprop((∃ v : ReqFields, srvReqFieldsAtM true s E ρ v) ∗ srvAuthBound s E ∗
      ⌜E.authOn = true⌝)

instance isServerReqM_persistent (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) :
    Persistent (isServerReqM (GF := GF) on s E ρ) := by
  cases on <;> unfold isServerReqM <;> infer_instance

/-- The server's built part's store has the bound request side (`srvUberBase`'s, E3zb). -/
theorem srvAuthBound_of_uberBase (s : Loc) (ua : GoInterface) (E : apply.AEnv GF)
    (h : E.authMode.isOn = true) :
    srvUberBase (GF := GF) s ua E ⊢ srvAuthBound s E := by
  iintro #Hb
  iunfold srvUberBase at Hb
  icases Hb with ⟨%au, %le, #Hauf, -, -, -, %stl, -, -, -, #HbB⟩
  iunfold srvAuthBound
  iexists au
  iframe Hauf
  iapply HbB
  ipureintro; exact h

theorem isServerReqM_split (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) :
    isServerReqM (GF := GF) on s E ρ ⊣⊢
      (∃ v : ReqFields, srvReqFieldsAtM on s E ρ v) ∗ srvAuthBoundM on s E := by
  cases on <;> unfold isServerReqM srvAuthBoundM <;> constructor <;> (iintro #H; iexact H)

theorem isServerReqM_false (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) :
    isServerReqM (GF := GF) false s E ρ = isServerReq s E ρ := rfl

/-- The proposer's view at the mode `on` fixes the environment's mode (the auth-mode merge's step 5:
a spec over `E.authOn` gives its instance at `on`, `ModeSpecs.lean`). -/
theorem isServerReqM_authOn (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) :
    isServerReqM (GF := GF) on s E ρ ⊢ ⌜E.authOn = on⌝ := by
  cases on <;> unfold isServerReqM
  · iintro ⟨-, %h⟩; ipureintro; exact h
  · iintro ⟨-, -, %h⟩; ipureintro; exact h

/-- **What a proposal of `rq` needs, in the auth mode `on`, with its result at the stamped header**
(see the file header): off, `reqPropOk` with a result `Qr` the header does not change (`Qh` constant);
on, for every header `hm` the server may stamp, `reqPropOkOn` of `withHeader rq hm` with the result
`Qh hm` (one resource: the client's update is spent once, at the header actually stamped). -/
def reqPropOkM (on : Bool) (γ : ServerRaftNames) (γk : KVNames) (Gb : apply.HeaderModel → IProp GF)
    (rq : apply.IRRModel) (Qh : apply.HeaderModel → List EntryModel → IProp GF) : IProp GF :=
  match on with
  | false => iprop(∃ Qr : List EntryModel → IProp GF, reqPropOk γk rq Qr ∗ ⌜Qh = fun _ => Qr⌝)
  | true => iprop(∀ hm : apply.HeaderModel, reqPropOkOn γ γk srvAuthSt0 Gb rq hm (Qh hm))

/-- `reqPropOk` gives the mode-off `reqPropOkM` at a constant result. -/
theorem reqPropOkM_of_false (γ : ServerRaftNames) (γk : KVNames) (Gb : apply.HeaderModel → IProp GF)
    (rq : apply.IRRModel) (Qr : List EntryModel → IProp GF) :
    reqPropOk (GF := GF) γk rq Qr ⊢ reqPropOkM false γ γk Gb rq (fun _ => Qr) := by
  iintro H
  iunfold reqPropOkM
  iexists Qr
  iframe H
  ipureintro; rfl

/-- **A mode-`on` KV write's permission at any header** (`reqPropOkM true`'s write case): a plain
write of `op` (no range end `[0]`, of a good shape, every permission of the cache's shape), its
client's update fired at most once, told its grant at the client's lower bound `L₀` of the requested
log (`writeGrantG`), the result at the stamped header's grant (`grantedRes`). -/
theorem reqPropOkM_true_write (γ : ServerRaftNames) (γk : KVNames)
    (Gb : apply.HeaderModel → IProp GF) (rq : apply.IRRModel) (op : KVOp)
    (Q : KVState → IProp GF) (γc : GName) (L₀ : List EntryModel) (hp : plainReq rq)
    (hop : reqKVOp rq = some op) (hz : irrNoZeroEnd rq) (hs : rqShape rq) (ha : kvShapeAll rq) :
    srvReqLogLb (GF := GF) γ L₀ ∗ kvAu1G γk (kvOpStep op) (writeGrantG γk srvAuthSt0 Gb rq L₀) Q ⊢
      reqPropOkM true γ γk Gb rq
        (fun hm => grantedRes γk srvAuthSt0 (apply.withHeader rq hm) γc Q) := by
  iintro ⟨#HL₀, Hau⟩
  iunfold reqPropOkM
  iintro %hm
  iunfold reqPropOkOn
  iright
  ileft
  iexists op, Q, γc, L₀
  iframe HL₀ Hau
  ipureintro
  exact ⟨⟨hp.1, putgetKind_header _ _ hp.2⟩, hop, hz, hs, ha, rfl⟩

/-- **A mode-`on` write-free proposal's permission at any header** (`reqPropOkM true`'s first
case). -/
theorem reqPropOkM_true_nowrite (γ : ServerRaftNames) (γk : KVNames)
    (Gb : apply.HeaderModel → IProp GF) (rq : apply.IRRModel) (hp : plainReq rq)
    (hnw : ¬ writeKind (apply.dispatchKind rq)) (hz : irrNoZeroEnd rq) (hs : rqShape rq)
    (ha : kvShapeAll rq) :
    ⊢ reqPropOkM (GF := GF) true γ γk Gb rq (fun _ _ => iprop(True)) := by
  iunfold reqPropOkM
  iintro %hm
  iunfold reqPropOkOn
  ileft
  ipureintro
  exact ⟨⟨hp.1, putgetKind_header _ _ hp.2⟩, hnw, hz, hs, ha, rfl⟩

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- A mode-`on` proposal's request has no range end `[0]` (either case of `reqPropOkOn`). -/
theorem reqPropOkOn_noZero (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState)
    (Gb : apply.HeaderModel → IProp GF) (rq : apply.IRRModel) (hm : apply.HeaderModel)
    (Qr : List EntryModel → IProp GF) :
    reqPropOkOn (GF := GF) γ γk st₀ Gb rq hm Qr ⊢
      ⌜irrNoZeroEnd (apply.withHeader rq hm)⌝ ∗ reqPropOkOn γ γk st₀ Gb rq hm Qr := by
  iunfold reqPropOkOn
  iintro (%Hno | ⟨%op, %Q, %γc, %L₀, %Hop, #HL₀, Hau⟩ | (%Had | ⟨%Qa, %Had, #Hha⟩))
  · isplitr
    · ipureintro; exact Hno.2.2.1
    · ileft; ipureintro; exact Hno
  · isplitr
    · ipureintro; exact Hop.2.2.1
    · iright; ileft; iexists op, Q, γc, L₀; iframe HL₀ Hau; ipureintro; exact Hop
  · isplitr
    · ipureintro; exact Had.2.1
    · iright; iright; ileft; ipureintro; exact Had
  · isplitr
    · ipureintro; exact Had.2.1
    · iright; iright; iright; iexists Qa; iframe Hha; ipureintro; exact Had

/-- **A proposal's update in the auth mode `on`, at the request the wire decodes** (`kv_prop_au`
off, `kv_prop_au_on` on; see the file header): for data `d` decoding to `rq'`, the encoding of `rq`
stamped with the header `hm`, claimed under `rq'`'s id; the result `Qh hm`. With auth on, the
header bound as the caller's binding `Gb` says (the write's grant, step 5). -/
theorem kv_prop_au_M (on : Bool) (γ : ServerRaftNames) (γk : KVNames) (d : List w8)
    (Gb : apply.HeaderModel → IProp GF) (rq rq' : apply.IRRModel) (hm : apply.HeaderModel)
    (Qh : apply.HeaderModel → List EntryModel → IProp GF) (hd : d ≠ [])
    (hdec : apply.irrDecode d = some rq') (hw : irrWireOf (apply.withHeader rq hm) rq')
    (id : w64) (γf : GName) (hid : apply.irrId rq' = some id) (E : CoPset) (hE : ↑kvN ⊆ E)
    (hE1 : ↑kvcN ⊆ E) (hE2 : ↑srvRaftN ⊆ E) :
    ⊢ kvInvM (GF := GF) on γ γk srvAuthSt0 -∗ kvCertInvM on γ γk srvAuthSt0 -∗ srvRaftLogInv γ -∗
      idClaim γk.ids id d γf -∗ idRegd γk.ids id -∗
      □ (⌜on = true⌝ → Gb hm) -∗
      reqPropOkM on γ γk Gb rq Qh ={E}=∗ srvPropAu1 γ d (Qh hm) ∗ srvQInv γ (Qh hm) := by
  cases on
  · rw [kvInvM_false]
    simp only [kvCertInvM]
    iintro #Hinv #Hci #Hrl #Hcl #Hreg - Hok
    iunfold reqPropOkM at Hok
    icases Hok with ⟨%Qr, Hok, %HQh⟩
    subst HQh
    ihave Hok' := reqPropOk_wire γk rq rq' hm Qr hw $$ Hok
    ihave ⟨Hok', Hq⟩ := reqPropOk_qinv γ γk rq' Qr $$ Hok'
    imod kv_prop_au γ γk d rq' Qr hd hdec id γf hid E hE hE1 hE2 $$ Hinv Hci Hrl Hcl Hreg Hok'
      with Hau
    imodintro
    iframe Hau
    iapply Hq $$ Hinv
  · rw [kvInvM_true]
    iintro #Hinv - - #Hcl #Hreg #Hgb Hok
    ihave #Hgb' : □ Gb hm $$ []
    · iintro !>; iapply Hgb; ipureintro; rfl
    iunfold reqPropOkM at Hok
    ispecialize Hok $$ %hm
    -- the stamped request's `irrNoZeroEnd` (either case of `reqPropOkOn`) makes it the wire's
    ihave ⟨%Hz, Hok⟩ := reqPropOkOn_noZero γ γk srvAuthSt0 Gb rq hm (Qh hm) $$ Hok
    have he := irrWireOf_eq rq rq' hm hw Hz
    subst he
    ihave ⟨Hok, Hq⟩ := reqPropOkOn_qinv γ γ γk srvAuthSt0 Gb rq hm (Qh hm) $$ Hok
    imod kv_prop_au_on γ γk srvAuthSt0 d Gb rq hm (Qh hm) hd hdec id γf hid E hE
      $$ Hinv Hcl Hreg Hgb' Hok with Hau
    imodintro
    iframe Hau
    iapply Hq $$ Hinv

/-- **An admin result without error, as the proposer reads it** (E3x): the tie (`adminTieM`) of a
dispatched result whose `Err` is `nil` gives the step's success (`adminDoneM`). -/
theorem adminDoneM_of_tie (on : Bool) (γk : KVNames) (rq : apply.IRRModel) (L : List EntryModel)
    (ar : Loc) (o : apply.Outcome) (skip : Bool)
    (v : go_etcd_io.etcd.server.v3.etcdserver.apply.Result) (hv : v.Err' = GoInterface.nil) :
    adminTieM (GF := GF) on γk rq L ar (.dispatched o skip) -∗ ar ↦□ v -∗
      ⌜adminDoneM on γk rq L⌝ := by
  cases on
  · iintro - -; ipureintro; trivial
  · simp only [adminTieM, adminDoneM]
    iunfold adminTieAr
    iintro (%h | ⟨%v', #Hv', %h⟩) #Hv
    · ipureintro
      intro hn
      rcases h with h | h
      · rw [hn] at h; cases h
      · exact absurd rfl (h o skip)
    · icombine Hv Hv' gives %Heq
      subst Heq
      ipureintro
      exact fun _ => h hv

variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions] in
/-- **`AuthInfoFromCtx` in the auth mode `on`** (E3zb): its spec, and with auth on, over the
store's bound request side (`srvAuthBoundM`), the auth info bound to the context too
(`boundSpec`'s `ctxBoundOrTLS`). -/
theorem EtcdServer.AuthInfoFromCtx.wpM (on : Bool)
    (hAuth : EtcdServer.AuthInfoFromCtx.spec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (st : GoInterface) (cca : Bool) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      structFieldRef EtcdServer go!"authStore" s ↦□ st ∗ isReqAuth st E.RD ∗
      srvAuthBoundM on s E ∗
      srvCfgFieldAddr s go!"ClientCertAuthEnabled" ↦□ cca ∗ mvcc.txnCtx ctx cd ∗ E.RD }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"AuthInfoFromCtx"))
      (Val #(GoInterface.ok ctx)))
  {{ (a : Loc) (err : GoInterface), RET (PairV #a #err); E.RD ∗ authInfoOpt a ∗ applyErrIs err ∗
      □ (⌜on = true⌝ → ctxBoundOrTLS s E.authMode (GoInterface.ok ctx) a) }} := by
  cases on
  · iintro %Φ ⟨#Hpkg, #Hst, #Hauth, -, #Hcca, #Hctx, Hrd⟩ HΦ
    iapply (hAuth s st E.RD .off cca ctx cd) $$ [Hrd] [HΦ]
    · iframe Hrd; iframe #
      iintro !> %h; exact absurd h (by decide)
    · iintro !> %a %err ⟨Hrd, Ha, #Herr, -⟩
      iapply HΦ; iframe Hrd Ha Herr
      iintro !> %h; cases h
  · iintro %Φ ⟨#Hpkg, #Hst, #Hauth, #Hbd, #Hcca, #Hctx, Hrd⟩ HΦ
    unfold srvAuthBoundM
    icases Hbd with ⟨#Hbd, %hon⟩
    ihave #Hbd2 : □ (⌜E.authOn = true⌝ → srvAuthBound s E) $$ []
    · iintro !> -; iexact Hbd
    ihave #Hreqb := srvAuthBound_gate s E st $$ [$Hst $Hbd2]
    iapply (hAuth s st E.RD E.authMode cca ctx cd) $$ [Hrd] [HΦ]
    · iframe Hrd; iframe #
    · iintro !> %a %err ⟨Hrd, Ha, #Herr, #Hb⟩
      iapply HΦ; iframe Hrd Ha Herr
      iintro !> -
      iapply Hb; ipureintro; exact hon

end lemmas

/-! ## A put in the mode `on` -/

section put
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **What a put of `op` needs in the mode `on`** (`putPermit`'s, and a key not empty: the
permission cache decides the put's check, `kvShapeAll`; the gRPC layer refuses an empty key,
`ErrGRPCEmptyKey`). The client's update is told its grant when it fires (`writeGrantG`, at the
caller's binding `Gb` and its lower bound `L₀` of the requested log; the auth-mode merge's step 5). -/
def putPermitOn (γ : ServerRaftNames) (γk : KVNames) (Gb : apply.HeaderModel → IProp GF)
    (op : OpFull) (Q : KVState → IProp GF) : IProp GF :=
  iprop(⌜op.leaseID = W64 0 ∧ op.key ≠ []⌝ ∗ ∃ L₀ : List EntryModel, srvReqLogLb γ L₀ ∗
    kvAu1G γk (kvOpStep (.put op)) (writeGrantG γk srvAuthSt0 Gb (irrPut op) L₀) Q)

/-- **A put's result in the mode `on`** at the header `hm` the server stamps and the committed log
`L` before its entry: `grantedRes` of the stamped request. -/
def putQhOn (γk : KVNames) (op : OpFull) (γc : GName) (Q : KVState → IProp GF)
    (hm : apply.HeaderModel) (L : List EntryModel) : IProp GF :=
  grantedRes γk srvAuthSt0 (apply.withHeader (irrPut op) hm) γc Q L

theorem irrPut_kind (op : OpFull) : apply.dispatchKind (irrPut op) = .put := by
  simp [apply.dispatchKind, irrPut, apply.irrEmpty]

/-- **A put's permission in the mode `on` is its proposal's** (`putPermit_reqPropOk`'s). -/
theorem putPermitOn_reqPropOk (γ : ServerRaftNames) (γk : KVNames)
    (Gb Gb' : apply.HeaderModel → IProp GF) (op : OpFull) (Q : KVState → IProp GF) (γc : GName)
    (hb : ∀ hm, Gb' hm ⊢ Gb hm) :
    putPermitOn (GF := GF) γ γk Gb op Q ⊢
      reqPropOkM true γ γk Gb' (irrPut op) (putQhOn γk op γc Q) := by
  unfold putPermitOn
  iintro ⟨%Hlk, %L₀, #HL₀, Hau⟩
  ihave Hau := kvAu1G_mono γk _ _ (writeGrantG γk srvAuthSt0 Gb' (irrPut op) L₀) Q
    (fun σ => writeGrantG_mono γk srvAuthSt0 Gb Gb' _ L₀ σ hb) $$ Hau
  obtain ⟨Hl, Hk⟩ := Hlk
  have hk := irrPut_kind op
  have hpl : plainCover (irrPut op) := by
    unfold plainCover
    rw [hk]
    refine ⟨by simp [apply.noSideEffect, irrPut, apply.irrEmpty],
      by simp [apply.needAdminPermission, irrPut, apply.irrEmpty], ?_⟩
    intro op' hop'
    simp only [irrPut, Option.some.injEq] at hop'
    subst hop'
    exact Hl
  have hp : plainReq (irrPut op) := ⟨hpl, putgetKind_kv _ (by simp only [hk]; simp)⟩
  have hop : reqKVOp (irrPut op) = some (.put op) := by unfold reqKVOp; rw [hk]; rfl
  have hz : irrNoZeroEnd (irrPut op) := by
    refine ⟨?_, ?_, ?_⟩ <;> intro _ h <;> simp [irrPut, apply.irrEmpty] at h
  have hs : rqShape (irrPut op) := rqShape_of_plain _ hpl (by rw [hk]; decide)
  have ha : kvShapeAll (irrPut op) := by
    intro x hx
    have hr : reqPerms (irrPut op) = apply.putPerms op := by unfold reqPerms; rw [hk]; rfl
    rw [hr] at hx
    have hsh : auth.reqShape op.key [] := ⟨Hk, Or.inl rfl⟩
    unfold apply.putPerms at hx
    cases hpk : op.base.prevKV <;> rw [hpk] at hx <;> simp at hx
    · subst hx; exact hsh
    · rcases hx with rfl | rfl <;> exact hsh
  have hq : putQhOn (GF := GF) γk op γc Q =
      fun hm => grantedRes γk srvAuthSt0 (apply.withHeader (irrPut op) hm) γc Q := rfl
  rw [hq]
  iapply reqPropOkM_true_write γ γk Gb' (irrPut op) (.put op) Q γc L₀ hp hop hz hs ha $$ [$HL₀ $Hau]

/-- **An applied plain write was granted** at the committed log before its entry (`grantedAt`):
the auth layer's verdict is the model's grant there (`modelOutM true`'s tie). -/
theorem grantedAt_of_applied (γk : KVNames) (rq : apply.IRRModel) (L : List EntryModel)
    (lb log' : mvcc.Log) (skip : Bool)
    (hkv : apply.isKVKind (apply.dispatchKind rq) = true)
    (h : modelOutM true γk rq L lb (.dispatched (.applied log' false) skip)) :
    grantedAt γk srvAuthSt0 rq L := by
  obtain ⟨st, hst, htie⟩ := h
  have hg : kvGranted st rq := by
    have := htie hkv _ _ rfl
    exact Classical.byContradiction fun hn => apply.Outcome.noConfusion (this.2 hn)
  unfold grantedAt; rw [hst]; exact hg

/-- **A KV write applied without an error was granted, so its client's result is there** (the
mode-`on` success): the apply thread's outcome `.applied` is not the auth layer's rejection, so the
model's auth state the entry met grants it (`authTie`), and `grantedRes` gives the result at the
state of the log the entry met. -/
theorem grantedRes_applied (γk : KVNames) (rq : apply.IRRModel) (γc : GName)
    (Q : KVState → IProp GF) (L : List EntryModel) (lb log' : mvcc.Log) (skip : Bool)
    (hkv : apply.isKVKind (apply.dispatchKind rq) = true)
    (h : modelOutM true γk rq L lb (.dispatched (.applied log' false) skip)) :
    grantedRes (GF := GF) γk srvAuthSt0 rq γc Q L ⊢ kvRes γc Q (kvStateOf lb) := by
  have hga := grantedAt_of_applied γk rq L lb log' skip hkv h
  obtain ⟨st, hst, -⟩ := h
  have hlb : kvModelOn γk srvAuthSt0 L = lb := by unfold kvModelOn; rw [hst]
  unfold grantedRes
  rw [hlb]
  iintro (⟨-, H⟩ | %Hn)
  · iexact H
  · exact absurd hga Hn


/-- A put's permission at a binding admitting more is one at a binding admitting less
(`Gb' ⊢ Gb`: the server's header bound, `hdrBoundM`, is a token's, `hdrBoundT`). -/
theorem putPermitOn_mono (γ : ServerRaftNames) (γk : KVNames) (Gb Gb' : apply.HeaderModel → IProp GF)
    (op : OpFull) (Q : KVState → IProp GF) (hb : ∀ hm, Gb' hm ⊢ Gb hm) :
    putPermitOn (GF := GF) γ γk Gb op Q ⊢ putPermitOn γ γk Gb' op Q := by
  unfold putPermitOn
  iintro ⟨%Hlk, %L₀, #HL₀, Hau⟩
  isplitr
  · ipureintro; exact Hlk
  iexists L₀
  iframe HL₀
  ihave Hau := kvAu1G_mono γk _ _ (writeGrantG γk srvAuthSt0 Gb' (irrPut op) L₀) Q
    (fun σ => writeGrantG_mono γk srvAuthSt0 Gb Gb' _ L₀ σ hb) $$ Hau
  iexact Hau

/-- `grantedRes_applied` for a put. -/
theorem putQhOn_res (γk : KVNames) (op : OpFull) (γc : GName) (Q : KVState → IProp GF)
    (hm : apply.HeaderModel) (L : List EntryModel) (lb log' : mvcc.Log) (skip : Bool)
    (h : modelOutM true γk (apply.withHeader (irrPut op) hm) L lb
      (.dispatched (.applied log' false) skip)) :
    putQhOn (GF := GF) γk op γc Q hm L ⊢ kvRes γc Q (kvStateOf lb) :=
  grantedRes_applied γk _ γc Q L lb log' skip
    (by rw [dispatchKind_withHeader, irrPut_kind]; rfl) h

/-- **What a delete of `op` needs in the mode `on`** (`deletePermit`'s, and its key and range end
of the shape the permission cache decides, `auth.reqShape`). -/
def deletePermitOn (γ : ServerRaftNames) (γk : KVNames) (Gb : apply.HeaderModel → IProp GF)
    (op : OpFull) (Q : KVState → IProp GF) : IProp GF :=
  iprop(⌜op.base.rangeEnd ≠ [W8 0] ∧ auth.reqShape op.key op.base.rangeEnd⌝ ∗
    ∃ L₀ : List EntryModel, srvReqLogLb γ L₀ ∗
      kvAu1G γk (kvOpStep (.deleteRange op)) (writeGrantG γk srvAuthSt0 Gb (irrDeleteRange op) L₀) Q)

/-- **What a put of `op` needs, in the auth mode `on`** (the auth-mode merge's step 5): off,
`putPermit`; on, `putPermitOn` (its key not empty, its update told its grant under the caller's
binding `Gb`). -/
def putPermitM (on : Bool) (γ : ServerRaftNames) (γk : KVNames) (Gb : apply.HeaderModel → IProp GF)
    (op : OpFull) (Q : KVState → IProp GF) : IProp GF :=
  match on with
  | false => putPermit γk op Q
  | true => putPermitOn γ γk Gb op Q

/-- **What a delete of `op` needs, in the auth mode `on`** (`putPermitM`'s). -/
def deletePermitM (on : Bool) (γ : ServerRaftNames) (γk : KVNames)
    (Gb : apply.HeaderModel → IProp GF) (op : OpFull) (Q : KVState → IProp GF) : IProp GF :=
  match on with
  | false => deletePermit γk op Q
  | true => deletePermitOn γ γk Gb op Q

/-- **A delete's result in the mode `on`** (`putQhOn`'s). -/
def deleteQhOn (γk : KVNames) (op : OpFull) (γc : GName) (Q : KVState → IProp GF)
    (hm : apply.HeaderModel) (L : List EntryModel) : IProp GF :=
  grantedRes γk srvAuthSt0 (apply.withHeader (irrDeleteRange op) hm) γc Q L

theorem irrDeleteRange_kind (op : OpFull) :
    apply.dispatchKind (irrDeleteRange op) = .deleteRange := by
  simp [apply.dispatchKind, irrDeleteRange, apply.irrEmpty]

/-- `putPermitOn_mono` for a delete. -/
theorem deletePermitOn_mono (γ : ServerRaftNames) (γk : KVNames)
    (Gb Gb' : apply.HeaderModel → IProp GF) (op : OpFull) (Q : KVState → IProp GF)
    (hb : ∀ hm, Gb' hm ⊢ Gb hm) :
    deletePermitOn (GF := GF) γ γk Gb op Q ⊢ deletePermitOn γ γk Gb' op Q := by
  unfold deletePermitOn
  iintro ⟨%Hlk, %L₀, #HL₀, Hau⟩
  isplitr
  · ipureintro; exact Hlk
  iexists L₀
  iframe HL₀
  ihave Hau := kvAu1G_mono γk _ _ (writeGrantG γk srvAuthSt0 Gb' (irrDeleteRange op) L₀) Q
    (fun σ => writeGrantG_mono γk srvAuthSt0 Gb Gb' _ L₀ σ hb) $$ Hau
  iexact Hau

/-- A mode-`on` delete's range end is not `[0]`. -/
theorem deletePermitOn_nz (γ : ServerRaftNames) (γk : KVNames) (Gb : apply.HeaderModel → IProp GF)
    (op : OpFull) (Q : KVState → IProp GF) :
    deletePermitOn (GF := GF) γ γk Gb op Q ⊢
      ⌜op.base.rangeEnd ≠ [W8 0]⌝ ∗ deletePermitOn γ γk Gb op Q := by
  unfold deletePermitOn
  iintro ⟨%Hzs, H⟩
  isplitr
  · ipureintro; exact Hzs.1
  iframe H
  ipureintro; exact Hzs

/-- **A delete's permission in the mode `on` is its proposal's** (`deletePermit_reqPropOk`'s). -/
theorem deletePermitOn_reqPropOk (γ : ServerRaftNames) (γk : KVNames)
    (Gb Gb' : apply.HeaderModel → IProp GF) (op : OpFull) (Q : KVState → IProp GF) (γc : GName)
    (hb : ∀ hm, Gb' hm ⊢ Gb hm) :
    deletePermitOn (GF := GF) γ γk Gb op Q ⊢
      reqPropOkM true γ γk Gb' (irrDeleteRange op) (deleteQhOn γk op γc Q) := by
  unfold deletePermitOn
  iintro ⟨%Hzs, %L₀, #HL₀, Hau⟩
  ihave Hau := kvAu1G_mono γk _ _ (writeGrantG γk srvAuthSt0 Gb' (irrDeleteRange op) L₀) Q
    (fun σ => writeGrantG_mono γk srvAuthSt0 Gb Gb' _ L₀ σ hb) $$ Hau
  obtain ⟨Hz, Hs⟩ := Hzs
  have hk := irrDeleteRange_kind op
  have hpl : plainCover (irrDeleteRange op) := by
    unfold plainCover
    rw [hk]
    exact ⟨by simp [apply.noSideEffect, irrDeleteRange, apply.irrEmpty],
      by simp [apply.needAdminPermission, irrDeleteRange, apply.irrEmpty]⟩
  have hp : plainReq (irrDeleteRange op) := ⟨hpl, putgetKind_kv _ (by simp only [hk]; simp)⟩
  have hop : reqKVOp (irrDeleteRange op) = some (.deleteRange op) := by
    unfold reqKVOp; rw [hk]; rfl
  have hz : irrNoZeroEnd (irrDeleteRange op) := by
    refine ⟨?_, ?_, ?_⟩
    · intro _ h; simp [irrDeleteRange, apply.irrEmpty] at h
    · intro o h; simp only [irrDeleteRange, Option.some.injEq] at h; subst h; exact Hz
    · intro _ h; simp [irrDeleteRange, apply.irrEmpty] at h
  have hs : rqShape (irrDeleteRange op) := rqShape_of_plain _ hpl (by rw [hk]; decide)
  have ha : kvShapeAll (irrDeleteRange op) := by
    intro x hx
    have hr : reqPerms (irrDeleteRange op) = (op.key, op.base.rangeEnd, .write) ::
        if op.base.prevKV then [(op.key, op.base.rangeEnd, .read)] else [] := by
      unfold reqPerms; rw [hk]; rfl
    rw [hr] at hx
    cases hpk : op.base.prevKV <;> rw [hpk] at hx <;> simp at hx
    · subst hx; exact Hs
    · rcases hx with rfl | rfl <;> exact Hs
  have hq : deleteQhOn (GF := GF) γk op γc Q =
      fun hm => grantedRes γk srvAuthSt0 (apply.withHeader (irrDeleteRange op) hm) γc Q := rfl
  rw [hq]
  iapply reqPropOkM_true_write γ γk Gb' (irrDeleteRange op) (.deleteRange op) Q γc L₀ hp hop hz hs ha
    $$ [$HL₀ $Hau]

/-- **What a writing transaction of `t` needs in the mode `on`** (the auth plan's E3d,
2026-10-27): `txnPermit`'s, and every permission the transaction's checks need of the shape the
permission cache decides (`kvShapeAll`: its comparisons' and operations' keys and range ends), for
whichever wire transaction of `t` the request holds (E3e: a put's `PrevKv` read is of its key and
its write's range end, so the shape is `t`'s). -/
def txnPermitOn (γ : ServerRaftNames) (γk : KVNames) (Gb : apply.HeaderModel → IProp GF)
    (t : TxnModel) (Q : KVState → IProp GF) : IProp GF :=
  iprop(⌜txn.txnPlain t ∧ txnNoZeroEnd t ∧ txn.txnShape t⌝ ∗
    ⌜∀ tw : txn.TxnModelW, tw.toModel = t → kvShapeAll (irrTxn tw)⌝ ∗
    ∃ L₀ : List EntryModel, srvReqLogLb γ L₀ ∗
      kvAu1G γk (kvOpStep (.txn t)) (fun σ => iprop(∃ tw : txn.TxnModelW, ⌜tw.toModel = t⌝ ∗
        writeGrantG γk srvAuthSt0 Gb (irrTxn tw) L₀ σ)) Q)

/-- **A writing transaction's result in the mode `on`** (`putQhOn`'s), of the wire transaction
`tw` (E3e). -/
def txnQhOn (γk : KVNames) (tw : txn.TxnModelW) (γc : GName) (Q : KVState → IProp GF)
    (hm : apply.HeaderModel) (L : List EntryModel) : IProp GF :=
  grantedRes γk srvAuthSt0 (apply.withHeader (irrTxn tw) hm) γc Q L

theorem irrTxn_kind (tw : txn.TxnModelW) : apply.dispatchKind (irrTxn tw) = .txn := by
  simp [apply.dispatchKind, irrTxn, apply.irrEmpty]

/-- **A writing transaction's permission in the mode `on` is its proposal's**
(`txnPermit_reqPropOk`'s), for its wire transaction `tw`. -/
theorem txnPermitOn_reqPropOk (γ : ServerRaftNames) (γk : KVNames)
    (Gb Gb' : apply.HeaderModel → IProp GF) (tw : txn.TxnModelW) (Q : KVState → IProp GF)
    (γc : GName) (hb : ∀ hm, Gb' hm ⊢ Gb hm) :
    txnPermitOn (GF := GF) γ γk Gb tw.toModel Q ⊢
      reqPropOkM true γ γk Gb' (irrTxn tw) (txnQhOn γk tw γc Q) := by
  unfold txnPermitOn
  iintro ⟨%Ht, %Ha, %L₀, #HL₀, Hau⟩
  -- the grant of this wire transaction is one of `t`'s
  ihave Hau := kvAu1G_mono γk _ _ (writeGrantG γk srvAuthSt0 Gb' (irrTxn tw) L₀) Q
    (fun σ => by
      iintro Hg; iexists tw
      isplitr
      · ipureintro; rfl
      iapply writeGrantG_mono γk srvAuthSt0 Gb Gb' _ L₀ σ hb $$ Hg) $$ Hau
  have hk := irrTxn_kind tw
  have hpl : plainCover (irrTxn tw) := by
    unfold plainCover
    rw [hk]
    refine ⟨by simp [apply.noSideEffect, irrTxn, apply.irrEmpty],
      by simp [apply.needAdminPermission, irrTxn, apply.irrEmpty], ?_⟩
    intro t' h; simp only [irrTxn_txn, Option.some.injEq] at h; subst h; exact Ht.1
  have hp : plainReq (irrTxn tw) := ⟨hpl, putgetKind_kv _ (by simp only [hk]; simp)⟩
  have hop : reqKVOp (irrTxn tw) = some (.txn tw.toModel) := by unfold reqKVOp; rw [hk]; rfl
  have hz : irrNoZeroEnd (irrTxn tw) := by
    refine ⟨?_, ?_, ?_⟩
    · intro _ h; simp [irrTxn, apply.irrEmpty] at h
    · intro _ h; simp [irrTxn, apply.irrEmpty] at h
    · intro t' h; simp only [irrTxn_txn, Option.some.injEq] at h; subst h; exact Ht.2.1
  have hs : rqShape (irrTxn tw) := rqShape_of_txn _ hpl hk (fun t' h => by
    simp only [irrTxn_txn, Option.some.injEq] at h; subst h; exact Ht.2.2)
  have hq : txnQhOn (GF := GF) γk tw γc Q =
      fun hm => grantedRes γk srvAuthSt0 (apply.withHeader (irrTxn tw) hm) γc Q := rfl
  rw [hq]
  iapply reqPropOkM_true_write γ γk Gb' (irrTxn tw) (.txn tw.toModel) Q γc L₀ hp hop hz hs (Ha tw rfl)
    $$ [$HL₀ $Hau]


/-- `putPermitOn_mono` for a writing transaction. -/
theorem txnPermitOn_mono (γ : ServerRaftNames) (γk : KVNames)
    (Gb Gb' : apply.HeaderModel → IProp GF) (t : TxnModel) (Q : KVState → IProp GF)
    (hb : ∀ hm, Gb' hm ⊢ Gb hm) :
    txnPermitOn (GF := GF) γ γk Gb t Q ⊢ txnPermitOn γ γk Gb' t Q := by
  unfold txnPermitOn
  iintro ⟨%Ht, %Ha, %L₀, #HL₀, Hau⟩
  isplitr
  · ipureintro; exact Ht
  isplitr
  · ipureintro; exact Ha
  iexists L₀
  iframe HL₀
  ihave Hau := kvAu1G_mono γk _ _ (fun σ => iprop(∃ tw : txn.TxnModelW, ⌜tw.toModel = t⌝ ∗
      writeGrantG γk srvAuthSt0 Gb' (irrTxn tw) L₀ σ)) Q
    (fun σ => by
      iintro ⟨%tw, %htw, Hg⟩
      iexists tw
      isplitr
      · ipureintro; exact htw
      iapply writeGrantG_mono γk srvAuthSt0 Gb Gb' _ L₀ σ hb $$ Hg) $$ Hau
  iexact Hau

/-- `grantedRes_applied` for a writing transaction. -/
theorem txnQhOn_res (γk : KVNames) (tw : txn.TxnModelW) (γc : GName) (Q : KVState → IProp GF)
    (hm : apply.HeaderModel) (L : List EntryModel) (lb log' : mvcc.Log) (skip : Bool)
    (h : modelOutM true γk (apply.withHeader (irrTxn tw) hm) L lb
      (.dispatched (.applied log' false) skip)) :
    txnQhOn (GF := GF) γk tw γc Q hm L ⊢ kvRes γc Q (kvStateOf lb) :=
  grantedRes_applied γk _ γc Q L lb log' skip
    (by rw [dispatchKind_withHeader, irrTxn_kind]; rfl) h

end put

end EtcdGrove
end Perennial
