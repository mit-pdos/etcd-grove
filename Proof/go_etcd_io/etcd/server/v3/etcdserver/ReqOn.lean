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

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [ext : FfiSyntax]

/-- **The KV model of the committed log `L` in the auth mode `on`**: `kvModel` off, the mode-`on`
model from the server's start state (`kvModelOn … srvAuthSt0`) on. -/
def kvModelM (on : Bool) (γk : KVNames) (L : List EntryModel) : mvcc.Log :=
  match on with
  | false => kvModel γk L
  | true => kvModelOn γk srvAuthSt0 L

theorem kvModelM_false (γk : KVNames) (L : List EntryModel) :
    kvModelM false γk L = kvModel γk L := rfl

theorem kvModelM_true (γk : KVNames) (L : List EntryModel) :
    kvModelM true γk L = kvModelOn γk srvAuthSt0 L := rfl

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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The auth layer's verdict is the model's** (`authTie st rq out`): an application of the KV
request `rq` dispatched to the outcome `o` was rejected by the auth layer exactly when the model's
auth state `st` (the state the entry met) does not grant it (`kvGranted`). What the apply thread in
the mode `on` knows of every KV entry it applies (E2t's `outcomeOn`, at the apply layer E2y's
`outcomeOn_of_kvOutL`), handed to the proposer with the result. -/
def authTie (st : auth.AuthState) (rq : apply.IRRModel) (out : apply.ApplyOut) : Prop :=
  apply.isKVKind (apply.dispatchKind rq) = true → ∀ o skip, out = .dispatched o skip →
    (o = .rejected .auth ↔ ¬ kvGranted st rq)

/-- **The result `ar` of applying `rq`, with its witness, in the mode `on`** (`resultIsW`'s, with
the auth layer's verdict the model's at the auth state `st` the entry met, `authTie`). -/
def resultIsWOn (E : apply.AEnv GF) (γr : ReadNames) (rq : apply.IRRModel) (F : mvcc.Log)
    (ar : Loc) (lb : mvcc.Log) (st : auth.AuthState) : IProp GF :=
  iprop(⌜ar ≠ null⌝ ∗
    ∃ (y y' : apply.ApplyKV) (out : apply.ApplyOut),
      ⌜apply.applyStep rq true y y' out ∧ apply.applyFloorOk rq true F y.log out ∧ y.log = lb ∧
        out.waived = false ∧ authTie st rq out⌝ ∗
      apply.applyResultIs rq true y.log ar out ∗
      mvcc.idxCert E.γ.idx y'.log ∗ revMinted E y.log y'.log ∗ appliedWit γr y'.log ∗
      mvcc.certOk E.γ y'.log)

/-- `resultIsWOn` forgets to `resultIsW`. -/
theorem resultIsW_of_on (E : apply.AEnv GF) (γr : ReadNames) (rq : apply.IRRModel) (F : mvcc.Log)
    (ar : Loc) (lb : mvcc.Log) (st : auth.AuthState) :
    resultIsWOn (GF := GF) E γr rq F ar lb st ⊢ resultIsW E γr rq F ar lb := by
  iunfold resultIsWOn
  iunfold resultIsW
  iintro ⟨%Hnn, %y, %y', %out, %Hs, Hr, Hc, Hm, Hw, Hk⟩
  isplitr
  · ipureintro; exact Hnn
  iexists y, y', out
  iframe Hr Hc Hm Hw Hk
  ipureintro; exact ⟨Hs.1, Hs.2.1, Hs.2.2.1, Hs.2.2.2.1⟩

/-- **The committed entry a result is of, in the mode `on`** (`entryWit`'s, see the file header):
the mode-`on` model of the raft prefix before it is `(st, lb)`, the auth state and the log the
entry met. -/
def entryWitOn (ρ : ReqNames) (rq : apply.IRRModel) (lb : mvcc.Log) (st : auth.AuthState) :
    IProp GF :=
  iprop(∃ (L : List EntryModel) (m : Nat) (e : EntryModel) (id : w64) (γf : GName),
    srvRLogLb ρ.raft L ∗ idClaim ρ.ids id e.data γf ∗
    ⌜L[m]? = some e ∧ e.typ = W32 0 ∧ apply.irrDecode e.data = some rq ∧
      apply.irrId rq = some id ∧
      kvRaftOfOn ρ.kv.c0 ρ.kv.ch0 (srvAuthSt0, ρ.kv.log0) (L.take m) = (st, lb)⌝)

instance entryWitOn_persistent (ρ : ReqNames) (rq : apply.IRRModel) (lb : mvcc.Log)
    (st : auth.AuthState) : Persistent (entryWitOn (GF := GF) ρ rq lb st) := by
  unfold entryWitOn; infer_instance

/-- **The result the proposer expects in the mode `on`** (`resultΨ`'s, with `resultIsWOn` and
`entryWitOn` at the auth state and the log the entry met). -/
def resultΨOn (E : apply.AEnv GF) (ρ : ReqNames) (rq : apply.IRRModel) (F : mvcc.Log)
    (x : GoInterface) : IProp GF :=
  iprop(∃ (ar : Loc) (lb : mvcc.Log) (st : auth.AuthState),
    ⌜x = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.Result.ty) #ar⌝ ∗
    apply.resTrace ar ∗ resultIsWOn E ρ.rd rq F ar lb st ∗ entryWitOn ρ rq lb st)

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

/-- **The applied result as the proposer reports it, in the auth mode `on`** (the success post of
`processInternalRaftRequestOnce.specM`): `resultIsW`'s, at the committed prefix `L` before the
entry, with what the proposer learns of the model there (`modelOutM`). -/
def resPostM (on : Bool) (E : apply.AEnv GF) (ρ : ReqNames) (rq : apply.IRRModel) (F : mvcc.Log)
    (ar : Loc) (L : List EntryModel) : IProp GF :=
  iprop(⌜ar ≠ null⌝ ∗
    ∃ (y y' : apply.ApplyKV) (out : apply.ApplyOut),
      ⌜apply.applyStep rq true y y' out ∧ apply.applyFloorOk rq true F y.log out ∧
        out.waived = false ∧ modelOutM on ρ.kv rq L y.log out⌝ ∗
      apply.applyResultIs rq true y.log ar out ∗
      mvcc.idxCert E.γ.idx y'.log ∗ revMinted E y.log y'.log ∗ appliedWit ρ.rd y'.log ∗
      mvcc.certOk E.γ y'.log)

/-- **The apply thread's answer, as `raftRequest` reports it, in the auth mode `on`** (`appliedOk`'s
at the committed prefix `L` before the entry, with `modelOutM`). -/
def appliedOkM (on : Bool) (E : apply.AEnv GF) (ρ : ReqNames) (rq' : apply.IRRModel) (F : mvcc.Log)
    (resp : GoInterface) (L : List EntryModel) : IProp GF :=
  iprop(∃ (x x' : apply.ApplyKV) (o : apply.Outcome) (skip : Bool),
    ⌜apply.applyStep rq' true x x' (.dispatched o skip) ∧ apply.kvFloorOk rq' true F x.log o ∧
      skip = false ∧ modelOutM on ρ.kv rq' L x.log (.dispatched o skip)⌝ ∗
    apply.dispatchAnswer rq' x.log skip resp GoInterface.nil o ∗ mvcc.idxCert E.γ.idx x'.log ∗
    revMinted E x.log x'.log ∗ appliedWit ρ.rd x'.log ∗ mvcc.certOk E.γ x'.log)

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

/-- **The server as a proposer sees it, in the auth mode `on`** (`srvReqFieldsAt` with `waitInvM`
and `kvInvM` from the server's start state, `srvAuthSt0`). -/
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
    srvIndexInvs s E ∗
    srvMintInv ρ ∗ kvInvM on ρ.raft ρ.kv srvAuthSt0 ∗ ⌜structFieldRef EtcdServer go!"Cfg" s ≠ null⌝)

instance srvReqFieldsAtM_persistent (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (v : ReqFields) : Persistent (srvReqFieldsAtM (GF := GF) on s E ρ v) := by
  unfold srvReqFieldsAtM; infer_instance

theorem srvReqFieldsAtM_false (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (v : ReqFields) :
    srvReqFieldsAtM (GF := GF) false s E ρ v = srvReqFieldsAt s E ρ v := rfl

/-- **The server, as a proposer sees it, in the auth mode `on`** (persistent). -/
def isServerReqM (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) : IProp GF :=
  iprop(∃ v : ReqFields, srvReqFieldsAtM on s E ρ v)

instance isServerReqM_persistent (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) :
    Persistent (isServerReqM (GF := GF) on s E ρ) := by
  unfold isServerReqM; infer_instance

theorem isServerReqM_false (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) :
    isServerReqM (GF := GF) false s E ρ = isServerReq s E ρ := rfl

/-- **What a proposal of `rq` needs, in the auth mode `on`, with its result at the stamped header**
(see the file header): off, `reqPropOk` with a result `Qr` the header does not change (`Qh` constant);
on, for every header `hm` the server may stamp, `reqPropOkOn` of `withHeader rq hm` with the result
`Qh hm` (one resource: the client's update is spent once, at the header actually stamped). -/
def reqPropOkM (on : Bool) (γk : KVNames) (rq : apply.IRRModel)
    (Qh : apply.HeaderModel → List EntryModel → IProp GF) : IProp GF :=
  match on with
  | false => iprop(∃ Qr : List EntryModel → IProp GF, reqPropOk γk rq Qr ∗ ⌜Qh = fun _ => Qr⌝)
  | true => iprop(∀ hm : apply.HeaderModel, reqPropOkOn γk srvAuthSt0 (apply.withHeader rq hm) (Qh hm))

/-- `reqPropOk` gives the mode-off `reqPropOkM` at a constant result. -/
theorem reqPropOkM_of_false (γk : KVNames) (rq : apply.IRRModel) (Qr : List EntryModel → IProp GF) :
    reqPropOk (GF := GF) γk rq Qr ⊢ reqPropOkM false γk rq (fun _ => Qr) := by
  iintro H
  iunfold reqPropOkM
  iexists Qr
  iframe H
  ipureintro; rfl

/-- **A mode-`on` KV write's permission at any header** (`reqPropOkM true`'s write case): a plain
write of `op` (no range end `[0]`, of a good shape, every permission of the cache's shape), its
client's update fired at most once, the result at the stamped header's grant (`grantedRes`). -/
theorem reqPropOkM_true_write (γk : KVNames) (rq : apply.IRRModel) (op : KVOp)
    (Q : KVState → IProp GF) (γc : GName) (hp : plainReq rq) (hop : reqKVOp rq = some op)
    (hz : irrNoZeroEnd rq) (hs : rqShape rq) (ha : kvShapeAll rq) :
    kvOpAu1 (GF := GF) γk op Q ⊢
      reqPropOkM true γk rq (fun hm => grantedRes γk srvAuthSt0 (apply.withHeader rq hm) γc Q) := by
  iintro Hau
  iunfold reqPropOkM
  iintro %hm
  iunfold reqPropOkOn
  iright
  iexists op, Q, γc
  iframe Hau
  ipureintro
  exact ⟨⟨hp.1, putgetKind_header _ _ hp.2⟩, hop, hz, hs, ha, rfl⟩

/-- **A mode-`on` write-free proposal's permission at any header** (`reqPropOkM true`'s first
case). -/
theorem reqPropOkM_true_nowrite (γk : KVNames) (rq : apply.IRRModel) (hp : plainReq rq)
    (hnw : ¬ writeKind (apply.dispatchKind rq)) (hz : irrNoZeroEnd rq) (hs : rqShape rq)
    (ha : kvShapeAll rq) :
    ⊢ reqPropOkM (GF := GF) true γk rq (fun _ _ => iprop(True)) := by
  iunfold reqPropOkM
  iintro %hm
  iunfold reqPropOkOn
  ileft
  ipureintro
  exact ⟨⟨hp.1, putgetKind_header _ _ hp.2⟩, hnw, hz, hs, ha, rfl⟩

end defs

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A mode-`on` proposal's request has no range end `[0]` (either case of `reqPropOkOn`). -/
theorem reqPropOkOn_noZero (γk : KVNames) (st₀ : auth.AuthState) (rq : apply.IRRModel)
    (Qr : List EntryModel → IProp GF) :
    reqPropOkOn (GF := GF) γk st₀ rq Qr ⊢ ⌜irrNoZeroEnd rq⌝ ∗ reqPropOkOn γk st₀ rq Qr := by
  iunfold reqPropOkOn
  iintro (%Hno | ⟨%op, %Q, %γc, %Hop, Hau⟩)
  · isplitr
    · ipureintro; exact Hno.2.2.1
    · ileft; ipureintro; exact Hno
  · isplitr
    · ipureintro; exact Hop.2.2.1
    · iright; iexists op, Q, γc; iframe Hau; ipureintro; exact Hop

/-- **A proposal's update in the auth mode `on`, at the request the wire decodes** (`kv_prop_au`
off, `kv_prop_au_on` on; see the file header): for data `d` decoding to `rq'`, the encoding of `rq`
stamped with the header `hm`, claimed under `rq'`'s id; the result `Qh hm`. -/
theorem kv_prop_au_M (on : Bool) (γ : ServerRaftNames) (γk : KVNames) (d : List w8)
    (rq rq' : apply.IRRModel) (hm : apply.HeaderModel)
    (Qh : apply.HeaderModel → List EntryModel → IProp GF) (hd : d ≠ [])
    (hdec : apply.irrDecode d = some rq') (hw : irrWireOf (apply.withHeader rq hm) rq')
    (id : w64) (γf : GName) (hid : apply.irrId rq' = some id) (E : CoPset) (hE : ↑kvN ⊆ E) :
    ⊢ kvInvM (GF := GF) on γ γk srvAuthSt0 -∗ idClaim γk.ids id d γf -∗ idRegd γk.ids id -∗
      reqPropOkM on γk rq Qh ={E}=∗ srvPropAu1 γ d (Qh hm) := by
  cases on
  · rw [kvInvM_false]
    iintro #Hinv #Hcl #Hreg Hok
    iunfold reqPropOkM at Hok
    icases Hok with ⟨%Qr, Hok, %HQh⟩
    subst HQh
    ihave Hok' := reqPropOk_wire γk rq rq' hm Qr hw $$ Hok
    iapply kv_prop_au γ γk d rq' Qr hd hdec id γf hid E hE $$ Hinv Hcl Hreg Hok'
  · rw [kvInvM_true]
    iintro #Hinv #Hcl #Hreg Hok
    iunfold reqPropOkM at Hok
    ispecialize Hok $$ %hm
    -- the stamped request's `irrNoZeroEnd` (either case of `reqPropOkOn`) makes it the wire's
    ihave ⟨%Hz, Hok⟩ := reqPropOkOn_noZero γk srvAuthSt0 (apply.withHeader rq hm) (Qh hm) $$ Hok
    have he := irrWireOf_eq rq rq' hm hw Hz
    subst he
    iapply kv_prop_au_on γ γk srvAuthSt0 d (apply.withHeader rq hm) (Qh hm) hd hdec id γf hid E hE
      $$ Hinv Hcl Hreg Hok

end lemmas

end EtcdGrove
end Perennial
