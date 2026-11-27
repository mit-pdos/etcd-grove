/-
**The server's contract with auth on** (the auth plan's E3zb, 2026-10-28; `ServerKV.lean`'s, in
the auth mode `on`): the parameters `A : KVAns GF` of `raftKV s A` for the server `s` started with
auth on (`srvKVAnsOn s E ρ γr c F d n tok`). Since the auth component's stage 4 (2026-11-04), the
rows merged over the mode (`srvKVAnsM on`, with `kvOpAuM`, `kvDepOwnM`, `kvDepPreM`; `srvKVAns` and
`srvKVAnsOn` its two rows), and every conjunct of `raftKV` proved once, at `E.authOn`, from the
server's merged linked specs (`EtcdServer.{Put,DeleteRange,Range,Txn}.spec`):
`kvPutOk_of_serverM`, ..., `raftKV_of_serverM`.

**What changes from `srvKVAns`**:
- a call also holds a lower bound `n` of the auth store's published index (`auth.authPubLbM`;
  `0` is free, `authPubLbM_zero`);
- a request must also be of the shape the permission cache decides (`kvDepPreOn`: a delete's key
  and range end, a writing transaction's every permission, `kvShapeAll`; a put's non-empty key is
  the gRPC check's);
- a read's deposit is at the mode-`on` model's state (`rangeDepQOn`, `kvStM true`), and a
  successful read's log is the mode-`on` model's of a committed raft log (`rangeAnsOkOn`,
  `txnReadAnsOn`), with its check's class: the permissions it saw granted at states recorded at an
  index `m ≥ n` (`apply.rangeClassFrom`, `txnClassFrom`), and for a linearizable read no older than
  the auth state the committed log through the read index left (`authFloorAt`);
- a call is at a context carrying the token `tok` (`auth.ctxToken`, gated by the mode; perheap C1a; the parameter is the
  caller's, as the deposit `d` is);
- a successful write's answer is `srvKVAns`'s and the grant (`writeGrantOn`, 2026-10-28): the
  request with the header the server stamped (`hm`) was granted at the committed log `L` before
  its entry (`grantedAt`), the header's user is the empty one or the one `tok` was issued to
  (`hdrBoundT`), and `L` followed by the write's own entry is committed (`pubAfterM`, with the auth
  state after it published). An error answer says nothing more: a refused request's caller needs
  nothing from it (`examples/lib/authwork`'s `Work` panics only when a refused request succeeds).

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ModeSpecs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ServerKV

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- A range's result over committed logs under the deposit, at the mode-`on` model's state
(`rangeDepQM` with auth on). -/
abbrev rangeDepQOn (γk : KVNames) : KVDep GF → List EntryModel → IProp GF :=
  rangeDepQM true γk

/-- **The shape the permission cache decides**: a delete's key and range end (`auth.reqShape`), a
writing transaction's every permission (`kvShapeAll`). -/
def kvReqShape (q : KVReq) : Prop :=
  match q with
  | .deleteRange o => auth.reqShape o.key o.base.rangeEnd
  | .txn cs ts es => ∀ t, txnModelOf cs ts es = some t → txn.txnReadonly t = false →
      ∀ tw : txn.TxnModelW, tw.toModel = t → kvShapeAll (irrTxn tw)
  | _ => True

/-- **What a request must be under the deposit, leases admitted when `lr`** (auth-lease S4 item 5,
Freeze §1.5): `kvDepPre`'s rows, but when `lr` (with auth on at the revocable lease mode, the server's
`putPermitOn`/`txnPermitOn`) a put's lease is free and a writing transaction is plain but for its
puts' leases (`txnPlainL`). -/
def kvDepPreL (lr : Prop) (d : KVDep GF) : KVReq → Prop
  | .put o => (∃ Q, d = .op1 (.put o) Q) ∧ (o.leaseID = W64 0 ∨ lr)
  | .range o => kvDepPre d (.range o)
  | .deleteRange o => kvDepPre d (.deleteRange o)
  | .txn cs ts es => ∀ t, txnModelOf cs ts es = some t →
      (txn.txnReadonly t = true ∧ ∀ Q, d = .read Q → txn.txnSerializable t = false) ∨
      ((∃ Q, d = .op1 (.txn t) Q) ∧ (txn.txnPlain t ∨ (lr ∧ txnPlainL t)) ∧ txnNoZeroEnd t ∧
        ReqOp.siblingSafeL ts ∧ ReqOp.siblingSafeL es ∧ txn.OpsNoCut t.thenOps ∧
        txn.OpsNoCut t.elseOps)

theorem kvDepPreL_mono (lr lr' : Prop) (h : lr → lr') (d : KVDep GF) (q : KVReq)
    (hq : kvDepPreL lr d q) : kvDepPreL lr' d q := by
  cases q with
  | put o => exact ⟨hq.1, hq.2.imp id h⟩
  | range o => exact hq
  | deleteRange o => exact hq
  | txn cs ts es =>
    intro t ht
    exact (hq t ht).imp id (fun h' => ⟨h'.1, h'.2.1.imp id (fun h'' => ⟨h h''.1, h''.2⟩), h'.2.2⟩)

/-- `kvDepPre` (lease `0`, plain transactions) is `kvDepPreL`'s at any `lr`. -/
theorem kvDepPreL_of_pre (lr : Prop) (d : KVDep GF) (q : KVReq) (hq : kvDepPre d q) :
    kvDepPreL lr d q := by
  cases q with
  | put o => exact ⟨hq.1, Or.inl hq.2⟩
  | range o => exact hq
  | deleteRange o => exact hq
  | txn cs ts es =>
    intro t ht
    exact (hq t ht).imp id (fun h' => ⟨h'.1, Or.inl h'.2.1, h'.2.2⟩)

/-- **What a request must be with auth on** (`kvDepPre`'s, leases admitted at the revocable lease
mode `lm`, `kvDepPreL`; and of the shape the permission cache decides, `kvReqShape`; a put's
non-empty key is the gRPC check's). -/
def kvDepPreOn (lm : lease.Mode) (d : KVDep GF) (q : KVReq) : Prop :=
  kvDepPreL (lm = .revocable) d q ∧ kvReqShape q

/-- **What a request must be, in the auth mode `on`**: `kvDepPre`, and with auth on the shape. -/
def kvDepPreM (on : Bool) (d : KVDep GF) (q : KVReq) : Prop :=
  kvDepPre d q ∧ (on = true → kvReqShape q)

/-- **What a request must be, in the auth mode `on` and the lease mode `lm`** (auth-lease S4 item 5):
`kvDepPreM`'s, leases admitted with auth on at the revocable lease mode (`kvDepPreL`). -/
def kvDepPreML (on : Bool) (lm : lease.Mode) (d : KVDep GF) (q : KVReq) : Prop :=
  kvDepPreL (on = true ∧ lm = .revocable) d q ∧ (on = true → kvReqShape q)

theorem kvDepPreML_of_M (on : Bool) (lm : lease.Mode) (d : KVDep GF) (q : KVReq)
    (h : kvDepPreM on d q) : kvDepPreML on lm d q :=
  ⟨kvDepPreL_of_pre _ d q h.1, h.2⟩

theorem kvDepPreML_of_on (lm : lease.Mode) (d : KVDep GF) (q : KVReq) (h : kvDepPreOn lm d q) :
    kvDepPreML true lm d q :=
  ⟨kvDepPreL_mono _ _ (fun h' => ⟨rfl, h'⟩) d q h.1, fun _ => h.2⟩

/-- **A successful `Range` of `o` with auth on** (`rangeAnsOkM` with auth on). -/
abbrev rangeAnsOkOn (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (F : mvcc.Log) (o : OpFull)
    (resp : Loc) (r : w64) (Q : List EntryModel → IProp GF) : IProp GF :=
  rangeAnsOkM true E γr c F o resp r Q

/-- **A successful read-only `Txn` of `t` with auth on** (`txnReadAnsM` with auth on). -/
abbrev txnReadAnsOn (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (F : mvcc.Log) (t : TxnModel)
    (Q : List EntryModel → IProp GF) (resp : Loc) (r : w64) : IProp GF :=
  txnReadAnsM true E γr c F t Q resp r

/-- An auth info bound to the token (`infoBoundM` with auth on) is `infoBoundT`'s. -/
theorem infoBoundM_tok (s : Loc) (E : apply.AEnv GF) (tok : Option GoString)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) :
    infoBoundM (GF := GF) true s E tok info ⊢ infoBoundT (srvTLSId s) E.authMode tok info := by
  unfold infoBoundM infoBoundT principalBound
  iintro H; iexact H

end defs

section defsHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **A read's check, as the answer reports it** (persistent): the permissions the check of `o`
saw granted at states recorded at an index `m` at least the caller's bound `n`, the store
published through `m` (`auth.authPubLbM`; the auth3 A2 read barrier, 2026-11-14), and for a
linearizable read no older than the auth state the committed log through the read index `c` left;
the auth info checked the caller's (`infoBoundT`, E3zb, 2026-10-28). -/
def rangeAuthed (T : IProp GF) (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (n : Nat)
    (tok : Option GoString) (o : OpFull) : IProp GF :=
  iprop(∃ (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (m : Nat), ⌜n ≤ m⌝ ∗
    apply.rangeClassFrom E.authMode m info o ∗ infoBoundT T E.authMode tok info ∗
    auth.authPubLbM E.authMode m ∗
    (if o.base.serializable then iprop(True) else authFloorAt E.authMode γr c m))

instance rangeAuthed_persistent (T : IProp GF) [Persistent T] (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (n : Nat)
    (tok : Option GoString) (o : OpFull) : Persistent (rangeAuthed (GF := GF) T E γr c n tok o) := by
  unfold rangeAuthed; split <;> infer_instance

/-- **A read-only transaction's checks, as the answer reports them** (`rangeAuthed`'s). -/
def txnAuthed (T : IProp GF) (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (n : Nat)
    (tok : Option GoString) (t : TxnModel) : IProp GF :=
  iprop(∃ (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (m : Nat), ⌜n ≤ m⌝ ∗
    txnClassFrom E.authMode m info t ∗ infoBoundT T E.authMode tok info ∗
    (if txn.txnSerializable t then iprop(True) else authFloorAt E.authMode γr c m))

instance txnAuthed_persistent (T : IProp GF) [Persistent T] (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (n : Nat)
    (tok : Option GoString) (t : TxnModel) : Persistent (txnAuthed (GF := GF) T E γr c n tok t) := by
  unfold txnAuthed; split <;> infer_instance

/-- **A header's user is the caller's** (persistent): the empty user, or the one the caller's
token `tok` was issued to (`auth.tokOk`), or the TLS fact `T` (the server's `srvTLSId s`, its TLS
fallback on; a parameter since O2, 2026-11-23) (`principalBound`'s,
over the token instead of the context: `hdrBoundM_tok`). -/
def hdrBoundT (T : IProp GF) (M : auth.AuthMode) (tok : Option GoString) (hm : apply.HeaderModel) :
    IProp GF :=
  iprop(⌜hm.username = (zeroValDef : GoString)⌝ ∨
    ((∃ token : GoString, ⌜tok = some token⌝ ∗ auth.tokOk M token hm.username) ∨ T))

instance hdrBoundT_persistent (T : IProp GF) [Persistent T] (M : auth.AuthMode) (tok : Option GoString)
    (hm : apply.HeaderModel) : Persistent (hdrBoundT (GF := GF) T M tok hm) := by
  unfold hdrBoundT; infer_instance

/-- **A successful write's grant** (persistent; see the file header): for the request `rq0` with
the header the server stamped, granted at the committed log `L` before its entry, the header's user
the caller's, and `L` with the entry committed. -/
def writeGrantOn (T : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (rq0 : apply.IRRModel) : IProp GF :=
  iprop(∃ (hm : apply.HeaderModel) (L : List EntryModel),
    ⌜grantedAt ρ.kv srvAuthSt0 (apply.withHeader rq0 hm) L⌝ ∗ hdrBoundT T E.authMode tok hm ∗
    pubAfterM true E ρ (apply.withHeader rq0 hm) L)

instance writeGrantOn_persistent (T : IProp GF) [Persistent T] (E : apply.AEnv GF) (ρ : ReqNames)
    (tok : Option GoString) (rq0 : apply.IRRModel) :
    Persistent (writeGrantOn (GF := GF) T E ρ tok rq0) := by
  unfold writeGrantOn; infer_instance

end defsHF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]


/-- A header bound to the token (`hdrBoundM` with auth on) is `hdrBoundT`'s. -/
theorem hdrBoundM_tok (s : Loc) (E : apply.AEnv GF) (tok : Option GoString) (hm : apply.HeaderModel) :
    hdrBoundM (GF := GF) true s E tok hm ⊢ hdrBoundT (srvTLSId s) E.authMode tok hm := by
  unfold hdrBoundM hdrBoundT principalBound
  iintro H; iexact H

end defs

section defsHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **A write's grant, as the server tells the client's update** (the auth-mode merge's step 5,
2026-10-29): `writeGrantG` of the write's request (for a transaction, of some wire transaction of
it), the header bound to the caller's token (`hdrBoundT`), past the client's lower bound `L₀` of
the requested log. (Auth-lease S4, Freeze C1) A lease grant's and revocation's likewise (`irrLeaseGrant`,
`irrLeaseRevoke`: the grant `leaseGrantPermitM`/`leaseRevokePermitM` hand the server). -/
def opGrantT (T : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString) :
    KVOp → List EntryModel → KVState → IProp GF
  | .put o, L₀ => writeGrantG ρ.kv srvAuthSt0 (hdrBoundT T E.authMode tok) (irrPut o) L₀
  | .deleteRange o, L₀ =>
    writeGrantG ρ.kv srvAuthSt0 (hdrBoundT T E.authMode tok) (irrDeleteRange o) L₀
  | .txn t, L₀ => fun σ => iprop(∃ tw : txn.TxnModelW, ⌜tw.toModel = t⌝ ∗
      writeGrantG ρ.kv srvAuthSt0 (hdrBoundT T E.authMode tok) (irrTxn tw) L₀ σ)
  | .leaseGrant id ttl, L₀ =>
    writeGrantG ρ.kv srvAuthSt0 (hdrBoundT T E.authMode tok) (irrLeaseGrant id ttl) L₀
  | .leaseRevoke id, L₀ =>
    writeGrantG ρ.kv srvAuthSt0 (hdrBoundT T E.authMode tok) (irrLeaseRevoke id) L₀
  | _, _ => fun _ => iprop(True)

/-- **A write's update with auth on, at the token `tok`** (the auth-mode merge's 5a, 2026-10-29):
fired at most once, at a lower bound `L₀` of the requested log the caller holds (`srvReqLogLb`),
told the write's grant (`opGrantT`) when it fires. -/
def kvOpAuOn (T : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString) (op : KVOp)
    (Q : KVState → IProp GF) : IProp GF :=
  iprop(∃ L₀ : List EntryModel, srvReqLogLb ρ.raft L₀ ∗
    kvAu1G ρ.kv (kvOpStep op) (opGrantT T E ρ tok op L₀) Q)

end defsHF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]


/-- **The deposit with auth on** (step 5): `kvDepOwn`'s, a write's update told its grant when it
fires (`opGrantT`), at a lower bound `L₀` of the requested log the caller holds
(`srvReqLogLb`). One that ignores the grant is one (`kvDepOwnOn_of_dep`). -/
def kvDepOwnOn (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (tok : Option GoString) : KVDep GF → IProp GF
  | .op1 o Q => kvOpAuOn (srvTLSId s) E ρ tok o Q
  | d => kvDepOwn ρ γr d

/-- A deposit not told its grant is one (at the empty lower bound). -/
theorem kvDepOwnOn_of_dep (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (tok : Option GoString) (d : KVDep GF) :
    kvDepOwn (GF := GF) ρ γr d ⊢ |==> kvDepOwnOn s E ρ γr tok d := by
  cases d with
  | op1 o Q =>
    simp only [kvDepOwn, kvDepOwnOn, kvOpAuOn]
    iintro H
    imod srvReqLogLb_nil (GF := GF) ρ.raft with #H0
    imodintro
    iexists []
    iframe H0
    unfold kvOpAu1
    iapply kvAu1_G $$ H
  | none => simp only [kvDepOwn, kvDepOwnOn]; iintro H; imodintro; iexact H
  | op o Q => simp only [kvDepOwn, kvDepOwnOn]; iintro H; imodintro; iexact H
  | read Q => simp only [kvDepOwn, kvDepOwnOn]; iintro H; imodintro; iexact H

/-- **The server's parameters of `raftKV` with auth on** (see the file header): `srvKVAns`'s, with
the caller's lower bound `n` of the published auth index, and a write's deposit told its grant
(`kvDepOwnOn`). -/
def srvKVAnsOn (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64)
    (F : mvcc.Log) (d : KVDep GF) (n : Nat) (tok : Option GoString) : KVAns GF where
  call ctx := iprop(srvCall s ρ ctx ∗ srvRdCall s E γr c ∗ kvDepOwnOn s E ρ γr tok d ∗
    srvApi.kvLogLb E.γs F ∗ auth.authPubLbM E.authMode n ∗ □ auth.ctxToken ctx tok)
  pre q := (match q with
    | .txn cs ts es => txnInModel cs ts es
    | _ => True) ∧ kvDepPreOn ρ.kv.lm d q
  ok q resp _h r := iprop(srvRdCall s E γr c ∗ match q with
    | .put o => iprop(putAppliedOk s E ρ.rd F o (opDepQ d) resp r ∗
        writeGrantOn (srvTLSId s) E ρ tok (irrPut o))
    | .deleteRange o => iprop(deleteAppliedOk s E ρ.rd F o (opDepQ d) resp r ∗
        writeGrantOn (srvTLSId s) E ρ tok (irrDeleteRange o))
    | .range o => iprop(idCred ρ.ids 1 ∗ srvLeadTimeReader s ∗
        rangeAnsOkOn E γr c F o resp r (rangeDepQOn γr.kv d) ∗ rangeAuthed (srvTLSId s) E γr c n tok o)
    | .txn cs ts es => iprop(srvLeadTimeReader s ∗ ∃ t, ⌜txnModelOf cs ts es = some t⌝ ∗
        if txn.txnReadonly t then iprop(idCred ρ.ids 1 ∗
          txnReadAnsOn E γr c F t (rangeDepQOn γr.kv d) resp r ∗ txnAuthed (srvTLSId s) E γr c n tok t)
        else iprop(txnAppliedAns E ρ.rd F t (opDepQ d) resp r ∗
          ∃ tw : txn.TxnModelW, ⌜tw.toModel = t⌝ ∗ writeGrantOn (srvTLSId s) E ρ tok (irrTxn tw))))
  err q e := iprop(srvRdCall s E γr c ∗ match q with
    | .put o => putErrOk s E ρ F o e
    | .deleteRange o => deleteErrOk s E ρ F o e
    | .range _ => iprop(idCred ρ.ids 1 ∗ srvLeadTimeReader s)
    | .txn cs ts es => iprop(srvLeadTimeReader s ∗ ∃ t, ⌜txnModelOf cs ts es = some t⌝ ∗
        if txn.txnReadonly t then idCred ρ.ids 1 else txnErrOk E ρ F t e))
  revR := mvcc.api.mvccReaders E.γ 1

end defs

section defsHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **A write's update in the auth mode `on`** (`kvOpAuOn`'s, the auth component's stage 4): fired at
most once, at a lower bound `L₀` of the requested log the caller holds, told the write's grant
(`opGrantT`) when it fires with auth on (`⌜on = true⌝ → …`). -/
def kvOpAuM (on : Bool) (T : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (op : KVOp) (Q : KVState → IProp GF) : IProp GF :=
  iprop(∃ L₀ : List EntryModel, srvReqLogLb ρ.raft L₀ ∗
    kvAu1G ρ.kv (kvOpStep op) (fun σ => iprop(⌜on = true⌝ → opGrantT T E ρ tok op L₀ σ)) Q)

end defsHF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]


/-- **A request's deposit in the auth mode `on`**: a write's update by `kvOpAuM`; the rest as
`kvDepOwn`. Off, it is `kvDepOwn` (`kvDepOwnM_of_dep`, `kvDepOwnM_false`); on, `kvDepOwnOn`
(`kvDepOwnM_true`). -/
def kvDepOwnM (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (tok : Option GoString) : KVDep GF → IProp GF
  | .op1 o Q => kvOpAuM on (srvTLSId s) E ρ tok o Q
  | d => kvDepOwn ρ γr d

/-- A deposit not told its grant is one in any mode (at the empty lower bound). -/
theorem kvDepOwnM_of_dep (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (tok : Option GoString) (d : KVDep GF) :
    kvDepOwn (GF := GF) ρ γr d ⊢ |==> kvDepOwnM on s E ρ γr tok d := by
  cases d with
  | op1 o Q =>
    simp only [kvDepOwn, kvDepOwnM, kvOpAuM]
    iintro H
    imod srvReqLogLb_nil (GF := GF) ρ.raft with #H0
    imodintro
    iexists []
    iframe H0
    unfold kvOpAu1
    iapply kvAu1_G $$ H
  | none => simp only [kvDepOwn, kvDepOwnM]; iintro H; imodintro; iexact H
  | op o Q => simp only [kvDepOwn, kvDepOwnM]; iintro H; imodintro; iexact H
  | read Q => simp only [kvDepOwn, kvDepOwnM]; iintro H; imodintro; iexact H

/-- Off, a deposit is `kvDepOwn`'s (the committer supplies the vacuous gate). -/
theorem kvDepOwnM_false (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (tok : Option GoString) (d : KVDep GF) :
    kvDepOwnM (GF := GF) false s E ρ γr tok d ⊢ kvDepOwn ρ γr d := by
  cases d with
  | op1 o Q =>
    simp only [kvDepOwn, kvDepOwnM, kvOpAuM]
    iintro ⟨%L₀, -, Hau⟩
    have hG : kvAu1G (GF := GF) ρ.kv (kvOpStep o)
        (fun σ => iprop(⌜false = true⌝ → opGrantT (srvTLSId s) E ρ tok o L₀ σ)) Q ⊢
        kvAu1 ρ.kv (kvOpStep o) Q := by
      unfold kvAu1G kvAu1
      exact aupd_post_mono (fun _ _ => sep_mono_right (sep_emp.2.trans (sep_mono_right (by
        iintro - %h; cases h))))
    unfold kvOpAu1
    iapply hG $$ Hau
  | none => simp only [kvDepOwn, kvDepOwnM]; iintro H; iexact H
  | op o Q => simp only [kvDepOwn, kvDepOwnM]; iintro H; iexact H
  | read Q => simp only [kvDepOwn, kvDepOwnM]; iintro H; iexact H

/-- On, a deposit is `kvDepOwnOn`'s. -/
theorem kvDepOwnM_true (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (tok : Option GoString) (d : KVDep GF) :
    kvDepOwnM (GF := GF) true s E ρ γr tok d ⊣⊢ kvDepOwnOn s E ρ γr tok d := by
  cases d with
  | op1 o Q =>
    simp only [kvDepOwnM, kvDepOwnOn, kvOpAuM, kvOpAuOn]
    constructor
    · iintro ⟨%L₀, #HL₀, Hau⟩
      iexists L₀
      iframe HL₀
      iapply (kvAu1G_mono ρ.kv _ _ _ Q (fun σ => by iintro H %_; iexact H)) $$ Hau
    · iintro ⟨%L₀, #HL₀, Hau⟩
      iexists L₀
      iframe HL₀
      iapply (kvAu1G_mono ρ.kv _ _ _ Q (fun σ => by iintro H; iapply H; ipureintro; first | rfl | trivial)) $$ Hau
  | none => simp only [kvDepOwnM, kvDepOwnOn]; exact .rfl
  | op o Q => simp only [kvDepOwnM, kvDepOwnOn]; exact .rfl
  | read Q => simp only [kvDepOwnM, kvDepOwnOn]; exact .rfl

/-- **The server's answers to the KV calls, in the auth mode `on`** (`raftKV`'s parameter; the auth
component's stage 4): with auth off, `srvKVAns`'s; with auth on, `srvKVAnsOn`'s. Each mode-specific
row is gated (`⌜on = true⌝ → …`) or reads the model at the mode. The gates are not under `□`:
`KVAns.ok` need not be persistent. `rangeAuthed`/`txnAuthed` are gated, not stated off: their
`infoBoundT s .off` asks for a token the off server does not check. -/
def srvKVAnsM (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64)
    (F : mvcc.Log) (d : KVDep GF) (n : Nat) (tok : Option GoString) : KVAns GF where
  call ctx := iprop(srvCall s ρ ctx ∗ srvRdCall s E γr c ∗ kvDepOwnM on s E ρ γr tok d ∗
    srvApi.kvLogLb E.γs F ∗ auth.authPubLbM E.authMode n ∗
    □ (⌜on = true⌝ → auth.ctxToken ctx tok))
  pre q := (match q with
    | .txn cs ts es => txnInModel cs ts es
    | _ => True) ∧ kvDepPreML on ρ.kv.lm d q
  ok q resp _h r := iprop(srvRdCall s E γr c ∗ match q with
    | .put o => iprop(putAppliedOk s E ρ.rd F o (opDepQ d) resp r ∗
        (⌜on = true⌝ → writeGrantOn (srvTLSId s) E ρ tok (irrPut o)))
    | .deleteRange o => iprop(deleteAppliedOk s E ρ.rd F o (opDepQ d) resp r ∗
        (⌜on = true⌝ → writeGrantOn (srvTLSId s) E ρ tok (irrDeleteRange o)))
    | .range o => iprop(idCred ρ.ids 1 ∗ srvLeadTimeReader s ∗
        rangeAnsOkM on E γr c F o resp r (rangeDepQM on γr.kv d) ∗
        (⌜on = true⌝ → rangeAuthed (srvTLSId s) E γr c n tok o))
    | .txn cs ts es => iprop(srvLeadTimeReader s ∗ ∃ t, ⌜txnModelOf cs ts es = some t⌝ ∗
        if txn.txnReadonly t then iprop(idCred ρ.ids 1 ∗
          txnReadAnsM on E γr c F t (rangeDepQM on γr.kv d) resp r ∗
          (⌜on = true⌝ → txnAuthed (srvTLSId s) E γr c n tok t))
        else iprop(txnAppliedAns E ρ.rd F t (opDepQ d) resp r ∗
          (⌜on = true⌝ → ∃ tw : txn.TxnModelW, ⌜tw.toModel = t⌝ ∗ writeGrantOn (srvTLSId s) E ρ tok (irrTxn tw)))))
  err q e := iprop(srvRdCall s E γr c ∗ match q with
    | .put o => putErrOk s E ρ F o e
    | .deleteRange o => deleteErrOk s E ρ F o e
    | .range o => iprop(idCred ρ.ids 1 ∗ srvLeadTimeReader s ∗
        rangeErrOut on E γr c F o (rangeDepQM on γr.kv d) e)
    | .txn cs ts es => iprop(srvLeadTimeReader s ∗ ∃ t, ⌜txnModelOf cs ts es = some t⌝ ∗
        if txn.txnReadonly t then idCred ρ.ids 1 else txnErrOk E ρ F t e))
  errP q m := match q with
    | .range _ => rangeErrMsgOk m
    | _ => True
  revR := mvcc.api.mvccReaders E.γ 1

/-- A deposit is a read deposit at the mode's model state (`kvDep`'s form). -/
theorem kvDep_of_depM (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (tok : Option GoString) (d : KVDep GF) :
    kvDepOwnM on s E ρ γr tok d ⊢ kvDep γr.kv (rangeDepQM on γr.kv d) (kvStM on γr.kv) := by
  iintro H
  iunfold kvDep
  cases d with
  | none => iright; ipureintro; rfl
  | op o Q => iright; ipureintro; rfl
  | op1 o Q => iright; ipureintro; rfl
  | read Q =>
    ileft
    iexists Q
    simp only [kvDepOwnM, kvDepOwn]
    iframe H
    ipureintro; rfl

/-- A put's permit in the mode `on` (`putPermitM`) from its deposit and the gRPC check, at a binding
`Gb` of the header that, with auth on, binds it to the caller's token. -/
theorem putPermitM_of_dep (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (tok : Option GoString) (d : KVDep GF) (o : OpFull) (Gb : apply.HeaderModel → IProp GF)
    (hGb : on = true → ∀ hm, Gb hm ⊢ hdrBoundT (srvTLSId s) E.authMode tok hm)
    (hc : putReqOk o) (hd : kvDepPreML on ρ.kv.lm d (.put o)) :
    kvDepOwnM on s E ρ γr tok d ⊢ putPermitM on ρ.raft ρ.kv Gb o (opDepQ d) := by
  have hd1 := hd.1
  simp only [kvDepPreL] at hd1
  obtain ⟨⟨Q, rfl⟩, hl⟩ := hd1
  cases on with
  | false =>
    have hl0 : o.leaseID = W64 0 := hl.resolve_right (fun h => by cases h.1)
    iintro H
    simp only [putPermitM]
    iapply putPermit_of_dep ρ γr _ o ⟨⟨Q, rfl⟩, hl0⟩
    iapply kvDepOwnM_false $$ H
  | true =>
    iintro H
    ihave H := (kvDepOwnM_true s E ρ γr tok _).1 $$ H
    simp only [putPermitM]
    iapply putPermitOn_mono ρ.raft ρ.kv (hdrBoundT (srvTLSId s) E.authMode tok) Gb o _ (hGb rfl)
    simp only [kvDepOwnOn, kvOpAuOn, opDepQ, opGrantT]
    iunfold putPermitOn
    isplitr
    · ipureintro
      refine ⟨hl.imp id (fun h => h.2), fun hk => ?_⟩
      simp [putReqOk, putCheck, hk] at hc
    iexact H

/-- A delete's permit in the mode `on` (`deletePermitM`) from its deposit (and with auth on its
shape), at a binding `Gb` as `putPermitM_of_dep`'s. -/
theorem deletePermitM_of_dep (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (γr : ReadNames) (tok : Option GoString) (d : KVDep GF) (o : OpFull)
    (Gb : apply.HeaderModel → IProp GF)
    (hGb : on = true → ∀ hm, Gb hm ⊢ hdrBoundT (srvTLSId s) E.authMode tok hm)
    (hd : kvDepPreML on ρ.kv.lm d (.deleteRange o)) :
    kvDepOwnM on s E ρ γr tok d ⊢ deletePermitM on ρ.raft ρ.kv Gb o (opDepQ d) := by
  have hd1 := hd.1
  simp only [kvDepPreL, kvDepPre] at hd1
  obtain ⟨⟨Q, rfl⟩, hz⟩ := hd1
  cases on with
  | false =>
    iintro H
    simp only [deletePermitM]
    iapply deletePermit_of_dep ρ γr _ o hd.1
    iapply kvDepOwnM_false $$ H
  | true =>
    iintro H
    ihave H := (kvDepOwnM_true s E ρ γr tok _).1 $$ H
    simp only [deletePermitM]
    iapply deletePermitOn_mono ρ.raft ρ.kv (hdrBoundT (srvTLSId s) E.authMode tok) Gb o _ (hGb rfl)
    simp only [kvDepOwnOn, kvOpAuOn, opDepQ, opGrantT]
    iunfold deletePermitOn
    isplitr
    · ipureintro; exact ⟨hz, hd.2 rfl⟩
    iexact H

/-- A writing transaction's permit in the mode `on` (`txnPermitM`) from its deposit, its shape and
(with auth on) the permission cache's shape, at a binding `Gb` as `putPermitM_of_dep`'s. -/
theorem txnPermitM_of_dep (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (tok : Option GoString) (d : KVDep GF) (t : TxnModel) (Gb : apply.HeaderModel → IProp GF)
    (hGb : on = true → ∀ hm, Gb hm ⊢ hdrBoundT (srvTLSId s) E.authMode tok hm)
    (hd : (∃ Q, d = .op1 (.txn t) Q) ∧ (txn.txnPlain t ∨ (on = true ∧ ρ.kv.lm = .revocable ∧ txnPlainL t)) ∧
      txnNoZeroEnd t) (hs : txn.txnShape t ∧ txn.txnKeysNodup t)
    (hsh : on = true → ∀ tw : txn.TxnModelW, tw.toModel = t → kvShapeAll (irrTxn tw)) :
    kvDepOwnM on s E ρ γr tok d ⊢ txnPermitM on ρ.raft ρ.kv Gb t (opDepQ d) := by
  obtain ⟨⟨Q, rfl⟩, hp, hz⟩ := hd
  simp only [kvDepOwnM, kvOpAuM, opDepQ, opGrantT]
  iintro ⟨%L₀, #HL₀, Hau⟩
  iunfold txnPermitM
  isplitr
  · ipureintro; exact ⟨hp, hz, hs⟩
  isplitr
  · ipureintro; exact hsh
  iexists L₀
  iframe HL₀
  iapply (kvAu1G_mono ρ.kv _ _ _ Q (fun σ => by
    iintro H %h
    ihave ⟨%tw, %htw, Hg⟩ := H $$ %h
    iexists tw
    isplitr
    · ipureintro; exact htw
    iapply writeGrantG_mono ρ.kv srvAuthSt0 (hdrBoundT (srvTLSId s) E.authMode tok) Gb _ L₀ σ (hGb h) $$ Hg))
    $$ Hau

end defs

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`raftKV`'s `Put` conjunct in the server's auth mode, from `EtcdServer.Put.spec`** (the auth
component's stage 4). -/
theorem kvPutOk_of_serverM (hPut : EtcdServer.Put.spec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64) (F : mvcc.Log)
    (d : KVDep GF) (n : Nat) (tok : Option GoString) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReqM E.authOn s E ρ ⊢
      kvPutOk s (srvKVAnsM E.authOn s E ρ γr c F d n tok) := by
  iintro ⟨#Hpkg, #Hsrv⟩
  iunfold kvPutOk
  iintro %ctx %r %o !> %Φ ⟨Hcall, #Hr, %Hok⟩ HΦ
  have hd : kvDepPreML E.authOn ρ.kv.lm d (.put o) := Hok.2.2
  simp only [srvKVAnsM]
  icases Hcall with ⟨Hcall, Hrc, Hdep, #HF, -, #HtokK⟩
  iunfold srvCall at Hcall
  icases Hcall with ⟨%ci, %cd, %Hci, #Hctx, #Hlib, #Hspan, -, -, Hcred, Hrd⟩
  subst Hci
  ihave ⟨Hard, Hrc⟩ := srvRdCall_rd s E γr c $$ Hrc
  wp_apply hPut s E ρ ci cd tok r o (opDepQ d) F $$ [Hrd Hard Hcred Hdep] as %resp %err ⟨Hrd, Hard, Hres⟩
  · iframe #; iframe Hrd Hard Hcred
    -- the gate is `Put.spec`'s, found by unification (off, the permit ignores it)
    iapply putPermitM_of_dep E.authOn s E ρ γr tok d o _ ?hGb Hok.1 hd $$ Hdep
    case hGb => intro h hm; exact hdrBoundM_tok s E _ hm
  ihave Hrc := Hrc $$ Hard
  iapply HΦ
  iunfold kvAnswer
  icases Hres with (⟨%Herr, %hm, %x, %x', %oc, %skip, %Hst, Hpo, Hhdr, #Hcert, HMint, #Hwit, Hcok,
    Hrcpt, %Hwf, ⟨%ltq, %Hltq, HQv⟩, #Hhb, #Hgate⟩ | ⟨%Hre, #HaE, Hfail⟩)
  · obtain ⟨Hstep, ⟨l, rfl⟩, HFx⟩ := Hst
    subst Herr
    -- (auth-lease S3b D3) the success's lease liveness: the handler's answer does not carry it
    ihave HQv : iprop(∃ lt, ⌜E.authOn = false ∨ ρ.kv.lm = .none → lt = []⌝ ∗ opDepQ d (kvStateOf x.log lt)) $$ [HQv]
    · iexists ltq; iframe HQv; ipureintro; exact Hltq.1
    simp only [apply.putOutcomeIs, apply.noSpaceErrIs, Bool.false_eq_true, ↓reduceIte]
    icases Hpo with ⟨#Hresp, -⟩
    ihave #Hresp' := Hresp
    iunfold txn.putResponseIs at Hresp'
    icases Hresp' with ⟨%Hrn, %h, %pk, #Hhf, %Hhn, #Hrev, -⟩
    iunfold apply.appliedHdr at Hhdr
    icases Hhdr with ⟨Hown, %Hlen⟩
    ileft
    isplitr
    · ipureintro; exact ⟨trivial, Hrn⟩
    iexists h, W64 (x.log.length : Int)
    ihave ⟨#Hhf2, Hw, Hri⟩ := hdr_of_own _ h (W64 (x.log.length : Int)) (mvcc.api.mvccReaders E.γ 1)
      (w64_rev_ne_zero _ (by omega) (by have := Hlen.2; omega)) $$ [$Hown]
    · iframe #; ipureintro; exact Hhn
    iframe Hhf2 Hw Hri
    iframe Hrc
    isplitl; rotate_left
    · iintro %hon
      ihave ⟨%L, %Hga, #HpAf⟩ := Hgate $$ %hon
      iunfold writeGrantOn
      iexists hm, L
      iframe HpAf
      isplitr
      · ipureintro; exact Hga
      rw [hon]
      iapply hdrBoundM_tok $$ Hhb
    iunfold putAppliedOk
    iframe Hrd
    iunfold putApplied
    iexists hm, x, x', l, skip
    iframe Hcert HMint Hwit Hcok Hrcpt HQv
    isplitr
    · ipureintro; exact ⟨Hstep, rfl, HFx, Hlen.1, Hlen.2⟩
    simp only [apply.putOutcomeIs, apply.noSpaceErrIs, Bool.false_eq_true, ↓reduceIte]
    iframe Hresp
    try (ipureintro; exact Hwf)
  · obtain ⟨rfl, Hne⟩ := Hre
    iright
    isplitr
    · iapply srvErrIs_of_applyErrIs _ Hne $$ HaE
    isplitr
    · iapply errMsgP_of_srvErrIs_of _ _ (fun _ => trivial)
      iapply srvErrIs_of_applyErrIs _ Hne $$ HaE
    simp only
    iframe Hrc
    iunfold putErrOk
    iframe Hrd
    iunfold putErr
    icases Hfail with (⟨%hm, Herr, -⟩ | Hdep)
    · ileft; iexists hm; iexact Herr
    · iright; iexact Hdep

/-- **`raftKV`'s `DeleteRange` conjunct in the server's auth mode, from
`EtcdServer.DeleteRange.spec`**. -/
theorem kvDeleteOk_of_serverM (hDel : EtcdServer.DeleteRange.spec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64) (F : mvcc.Log)
    (d : KVDep GF) (n : Nat) (tok : Option GoString) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReqM E.authOn s E ρ ⊢
      kvDeleteOk s (srvKVAnsM E.authOn s E ρ γr c F d n tok) := by
  iintro ⟨#Hpkg, #Hsrv⟩
  iunfold kvDeleteOk
  iintro %ctx %r %o !> %Φ ⟨Hcall, #Hr, %Hok⟩ HΦ
  have hd : kvDepPreML E.authOn ρ.kv.lm d (.deleteRange o) := Hok.2.2
  have Hnz0 : o.base.rangeEnd ≠ [W8 0] := by
    have h1 := hd.1; simp only [kvDepPreL, kvDepPre] at h1; exact h1.2
  simp only [srvKVAnsM]
  icases Hcall with ⟨Hcall, Hrc, Hdep, #HF, -, #HtokK⟩
  have HnzW : irrNoZeroEnd (irrDeleteRange o) := by
    refine ⟨?_, ?_, ?_⟩
    · intro _ h; simp [irrDeleteRange, apply.irrEmpty] at h
    · intro o' h; simp only [irrDeleteRange, Option.some.injEq] at h; subst h; exact Hnz0
    · intro _ h; simp [irrDeleteRange, apply.irrEmpty] at h
  iunfold srvCall at Hcall
  icases Hcall with ⟨%ci, %cd, %Hci, #Hctx, #Hlib, #Hspan, #Hst, -, Hcred, Hrd⟩
  subst Hci
  ihave ⟨Hard, Hrc⟩ := srvRdCall_rd s E γr c $$ Hrc
  wp_apply hDel s E ρ ci cd tok r o (opDepQ d) F $$ [Hrd Hard Hcred Hdep] as %resp %err ⟨Hrd, Hard, Hres⟩
  · iframe #; iframe Hrd Hard Hcred
    -- the gate is `DeleteRange.spec`'s, as in the put
    iapply deletePermitM_of_dep E.authOn s E ρ γr tok d o _ ?hGb hd $$ Hdep
    case hGb => intro h hm; exact hdrBoundM_tok s E _ hm
  ihave Hrc := Hrc $$ Hard
  iapply HΦ
  iunfold kvAnswer
  icases Hres with (⟨%Herr, %hm, %rq', %op', %x, %x', %oc, %skip, %Hst, Hpo, Hhdr, #Hcert, HMint, #Hwit,
    Hcok, Hrcpt, %Hwf, HQv, #Hhb, #Hgate⟩ | ⟨%Hre, #HaE, Hfail⟩)
  · obtain ⟨Hwire, Hop', Hnz, Hstep, ⟨l, rfl⟩, HFx⟩ := Hst
    have Hrq : rq' = apply.withHeader (irrDeleteRange o) hm := Hwire.2.2.2 HnzW
    subst Herr
    simp only [apply.deleteOutcomeIs, apply.noSpaceErrIs, Bool.false_eq_true, ↓reduceIte]
    icases Hpo with ⟨#Hresp, -⟩
    ihave #Hresp' := Hresp
    iunfold txn.deleteRangeResponseIs at Hresp'
    icases Hresp' with ⟨%Hrn, %h, %sl, %ps, #Hhf, %Hhn, #Hrev, -⟩
    iunfold apply.appliedHdr at Hhdr
    icases Hhdr with ⟨Hown, %Hlen⟩
    ileft
    isplitr
    · ipureintro; exact ⟨trivial, Hrn⟩
    iexists h, W64 ((mvcc.writeRev x.log (txn.delChanges (mvcc.stateAfter x.log) op') : Nat) : Int)
    ihave ⟨#Hhf2, Hw, Hri⟩ := hdr_of_own _ h _ (mvcc.api.mvccReaders E.γ 1)
      (writeRev_ne_zero _ _ Hlen.1 (by have := Hlen.2; omega)) $$ [$Hown]
    · iframe #; ipureintro; exact Hhn
    iframe Hhf2 Hw Hri
    iframe Hrc
    isplitl; rotate_left
    · iintro %hon
      ihave ⟨%L, %Hga, #HpAf⟩ := Hgate $$ %hon
      iunfold writeGrantOn
      iexists hm, L
      rw [← Hrq]
      iframe HpAf
      isplitr
      · ipureintro; exact Hga
      rw [hon]
      iapply hdrBoundM_tok $$ Hhb
    iunfold deleteAppliedOk
    iframe Hrd
    iunfold deleteApplied
    iexists hm, rq', op', x, x', l, skip
    iframe Hcert HMint Hwit Hcok Hrcpt HQv
    isplitr
    · ipureintro; exact ⟨Hwire, Hop', Hnz, Hstep, rfl, HFx, Hlen.1, Hlen.2⟩
    simp only [apply.deleteOutcomeIs, apply.noSpaceErrIs, Bool.false_eq_true, ↓reduceIte]
    iframe Hresp
    try (ipureintro; exact Hwf)
  · obtain ⟨rfl, Hne⟩ := Hre
    iright
    isplitr
    · iapply srvErrIs_of_applyErrIs _ Hne $$ HaE
    isplitr
    · iapply errMsgP_of_srvErrIs_of _ _ (fun _ => trivial)
      iapply srvErrIs_of_applyErrIs _ Hne $$ HaE
    simp only
    iframe Hrc
    iunfold deleteErrOk
    iframe Hrd
    iunfold deleteErr
    icases Hfail with (⟨%hm, %rq', %Hw, Herr, -⟩ | Hdep)
    · ileft; iexists hm, rq'; iframe Herr; ipureintro; exact Hw
    · iright; iexact Hdep

/-- A message none of `etcdserver/errors`' variables has. -/
theorem errorsMsgs_ne_of (m : GoString)
    (h : m ∉ go_etcd_io.etcd.server.v3.etcdserver.errors.errorsMsgs.map Prod.snd) :
    ∀ p ∈ go_etcd_io.etcd.server.v3.etcdserver.errors.errorsMsgs, p.2 ≠ m := by
  intro p hp heq
  apply h
  rw [← heq]
  exact List.mem_map_of_mem hp

local macro "mem_tac" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

open Iris.ProofMode in
/-- An `errors.New` variable's error: its `Error()` returns its message. -/
theorem errMsgP_of_newVar (X msg : GoString) (P : GoString → Prop) (hP : P msg) (err : GoInterface) :
    EtcdGrove.errorsNewVar (GF := GF) X msg ⊢ globalAddr X ↦□ err -∗ errMsgP err P := by
  iintro #Hv #He
  iunfold EtcdGrove.errorsNewVar at Hv
  icases Hv with ⟨%x, #Hx, #HE⟩
  icombine He Hx gives %Heq
  subst Heq
  iunfold errMsgP
  iexists ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩
  isplitr
  · ipureintro; rfl
  iintro %Φ !> - HΦ
  iapply HE
  inext
  iapply HΦ
  ipureintro; exact hP

open Iris.ProofMode in
/-- An `errors.New` variable with its message cell (`errVarCell`) holds an `errors.New` error
(`*errorString`'s `Error()` returns its `s` field). -/
theorem errorsNewVar_of_errVarCell [_root_.Perennial.errors.Assumptions] (X msg : GoString) :
    EtcdGrove.errVarCell (GF := GF) X msg ⊢ EtcdGrove.errorsNewVar X msg := by
  iintro #H
  iunfold EtcdGrove.errVarCell at H
  icases H with ⟨%x, #Hx, #Hs⟩
  iunfold EtcdGrove.errStrCell at Hs
  iunfold EtcdGrove.errorsNewVar
  iexists x
  iframe Hx
  iintro !> %Φ HΦ
  rw [method_unfold]
  wp_auto
  iexact HΦ

open Iris.ProofMode in
/-- A context's error (`isCtxErr`): its `Error()` returns `"context canceled"` or
`"context deadline exceeded"`. -/
theorem errMsgP_of_isCtxErr (P : GoString → Prop)
    (hP : P go!"context canceled" ∧ P go!"context deadline exceeded") (err : GoInterface) :
    context.isCtxErr (GF := GF) err ⊢ errMsgP err P := by
  iintro #He
  iunfold context.isCtxErr at He
  iunfold errMsgP
  icases He with (⟨-, %x, %hx, #Hs⟩ | ⟨-, %hv⟩)
  · subst hx
    iexists ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩
    isplitr
    · ipureintro; rfl
    iintro %Φ !> - HΦ
    rw [method_unfold]
    wp_auto
    iapply HΦ
    ipureintro; exact hP.1
  · subst hv
    iexists ⟨context.deadlineExceededError.ty, #(zero_val context.deadlineExceededError)⟩
    isplitr
    · ipureintro; rfl
    iintro %Φ !> - HΦ
    wp_method_call
    unfold context.deadlineExceededError.Error.impl
    wp_auto
    iapply HΦ
    ipureintro; exact hP.2

theorem rangeErrMsgOk_of_prefix (pre s : GoString)
    (h1 : ¬ pre <+: go_etcd_io.etcd.cache.v3.futureRevDesc)
    (h2 : ¬ pre <+: go_etcd_io.etcd.cache.v3.compactedDesc) : rangeErrMsgOk (pre ++ s) :=
  ⟨fun h => h1 ⟨s, h⟩, fun h => h2 ⟨s, h⟩⟩

open Iris.ProofMode in
/-- **The `Error()` of each of `Range`'s errors** (`rangeErrOut`; k8s etcd3 7c-2 part 2, S5) returns
neither read error's gRPC description (`rangeErrMsgOk`): mvcc's two (`mvcc: …`), the auth package's
variables (`auth: …`), the read index's (`context …`, `etcdserver: …`), the `rangeKeys` wrap
(`rangeKeys: …`). -/
theorem errMsgP_of_rangeErrOut (on : Bool) (E : apply.AEnv GF) (γr : ReadNames) (c : w64)
    (F : mvcc.Log) (o : OpFull) (Q : List EntryModel → IProp GF) (err : GoInterface)
    (hne : err ≠ GoInterface.nil) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ⊢
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth -∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.errors -∗
      rangeErrOut on E γr c F o Q err -∗ errMsgP err rangeErrMsgOk := by
  iintro #Pm #Pa #Pe #H
  ihave #Hm : (go_etcd_io.etcd.server.v3.storage.mvcc.mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Pm
  ihave #Ha : (go_etcd_io.etcd.server.v3.auth.authInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Pa
  ihave #Hei : (go_etcd_io.etcd.server.v3.etcdserver.errors.errorsInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Pe
  icases Hei with ⟨-, #Hev, -⟩
  iunfold rangeErrOut at H
  icases H with (⟨%ef, #Hf, %He, -⟩ | ⟨%ec, #Hc, %He, -⟩ | #Hau | #Hrd | #Hk)
  · subst He
    icases Hm with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #HNF, -⟩
    iapply errMsgP_of_newVar _ _ _ (by unfold rangeErrMsgOk; decide) $$ HNF Hf
  · subst He
    icases Hm with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #HNC, -⟩
    iapply errMsgP_of_newVar _ _ _ (by unfold rangeErrMsgOk; decide) $$ HNC Hc
  · iunfold authErrVarIs at Hau
    icases Hau with (%Hn | ⟨%g, %e, %Hg, #Hge, %He⟩)
    · exact absurd Hn hne
    subst He
    obtain ⟨⟨g', m⟩, hmem, rfl⟩ := List.mem_map.1 Hg.1
    icases Ha with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #HAC⟩
    ihave #Hcell := EtcdGrove.errVarCells_mem hmem $$ HAC
    ihave #Hnv := errorsNewVar_of_errVarCell _ _ $$ Hcell
    have hm1 : rangeErrMsgOk m := by
      constructor
      · intro h
        exact go_etcd_io.etcd.server.v3.auth.authErrMsgs_ne_of _
          (by unfold go_etcd_io.etcd.cache.v3.futureRevDesc; decide) _ hmem h
      · intro h
        exact go_etcd_io.etcd.server.v3.auth.authErrMsgs_ne_of _
          (by unfold go_etcd_io.etcd.cache.v3.compactedDesc; decide) _ hmem h
    iapply errMsgP_of_newVar _ _ _ hm1 $$ Hnv Hge
  · iunfold readErrIs at Hrd
    icases Hrd with (%Hn | #Hc | #Hs | #Hl | #Ht)
    · exact absurd Hn hne
    · iapply errMsgP_of_isCtxErr _ (by unfold rangeErrMsgOk; decide) $$ Hc
    · ihave #Hnv := EtcdGrove.errorsNewVars_mem
        (X := go_etcd_io.etcd.server.v3.etcdserver.errors.ErrStopped) (m := go!"etcdserver: server stopped")
        (by unfold go_etcd_io.etcd.server.v3.etcdserver.errors.errorsMsgs; mem_tac) $$ Hev
      iapply errMsgP_of_newVar _ _ _ (by unfold rangeErrMsgOk; decide) $$ Hnv Hs
    · ihave #Hnv := EtcdGrove.errorsNewVars_mem
        (X := go_etcd_io.etcd.server.v3.etcdserver.errors.ErrLeaderChanged) (m := go!"etcdserver: leader changed")
        (by unfold go_etcd_io.etcd.server.v3.etcdserver.errors.errorsMsgs; mem_tac) $$ Hev
      iapply errMsgP_of_newVar _ _ _ (by unfold rangeErrMsgOk; decide) $$ Hnv Hl
    · ihave #Hnv := EtcdGrove.errorsNewVars_mem
        (X := go_etcd_io.etcd.server.v3.etcdserver.errors.ErrTimeout) (m := go!"etcdserver: request timed out")
        (by unfold go_etcd_io.etcd.server.v3.etcdserver.errors.errorsMsgs; mem_tac) $$ Hev
      iapply errMsgP_of_newVar _ _ _ (by unfold rangeErrMsgOk; decide) $$ Hnv Ht
  · iunfold mvcc.rangeKeysErr at Hk
    icases Hk with ⟨-, -, %ii, %s, %He, #HE⟩
    iunfold errMsgP
    iexists ii
    isplitr
    · ipureintro; exact He
    iintro %Φ !> - HΦ
    iapply HE
    inext
    iapply HΦ
    ipureintro
    exact rangeErrMsgOk_of_prefix _ _
      (by unfold go_etcd_io.etcd.cache.v3.futureRevDesc; decide)
      (by unfold go_etcd_io.etcd.cache.v3.compactedDesc; decide)

open Iris.ProofMode in
/-- **An error `Range` returns other than mvcc's two** (`rangeErrOut`'s last three cases; k8s etcd3
7c-2 part 2, S5): neither of mvcc's read errors (the variables' message cells differ, or, for the
`rangeKeys` wrap, its description), and, passed through by `togRPCError` (`ctxPassed`), of a
description that is neither read error's gRPC one (a context error's, `ctxErrDescs`; the
`rangeKeys` wrap's prefix). -/
theorem rangeErrOther_facts (e kf kc : GoInterface) (hne : e ≠ GoInterface.nil) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ⊢
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth -∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.errors -∗
      go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ctxErrDescs -∗
      (globalAddr go_etcd_io.etcd.server.v3.storage.mvcc.ErrFutureRev ↦□ kf : IProp GF) -∗
      (globalAddr go_etcd_io.etcd.server.v3.storage.mvcc.ErrCompacted ↦□ kc : IProp GF) -∗
      (authErrVarIs e ∨ readErrIs e ∨ mvcc.rangeKeysErr e) -∗
      ⌜e ≠ kf ∧ e ≠ kc⌝ ∗ (ctxPassed e -∗ ∃ m : GoString, go_etcd_io.etcd.cache.v3.descIs e m ∗
        ⌜rangeErrMsgOk m⌝) := by
  iintro #Pm #Pa #Pe #Hcd #Hkf #Hkc #H
  ihave #Hm : (go_etcd_io.etcd.server.v3.storage.mvcc.mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Pm
  icases Hm with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, #CC, #CF, -⟩
  iunfold go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ctxErrDescs at Hcd
  icases Hcd with ⟨⟨%ecn, #Hcn, %mcn, #Dcn, %Hdcn⟩, ⟨%ede, #Hde, %mde, #Dde, %Hdde⟩⟩
  -- a context value passed through has a context error's description
  ihave #Hcx : iprop(□ ∀ x : GoInterface, ((globalAddr _root_.Perennial.context.Canceled ↦□ x : IProp GF) ∨
      (globalAddr _root_.Perennial.context.DeadlineExceeded ↦□ x : IProp GF)) -∗
      ∃ m : GoString, go_etcd_io.etcd.cache.v3.descIs x m ∗ ⌜rangeErrMsgOk m⌝) $$ []
  · iintro !> %x (#Hx | #Hx)
    · icombine Hx Hcn gives %h; subst h; iexists mcn; iframe Dcn; ipureintro; exact Hdcn
    · icombine Hx Hde gives %h; subst h; iexists mde; iframe Dde; ipureintro; exact Hdde
  icases H with (#Hau | #Hrd | #Hk)
  · -- an auth package variable
    iunfold authErrVarIs at Hau
    icases Hau with (%Hn | ⟨%g, %ea, %Hg, #Hge, %He⟩)
    · exact absurd Hn hne
    subst He
    ihave #Ha : (go_etcd_io.etcd.server.v3.auth.authInit : IProp GF) $$ []
    · iapply isPkgInit_access $$ Pa
    icases Ha with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #HAC⟩
    ihave #HapF := EtcdGrove.errVarApart_cells go_etcd_io.etcd.server.v3.storage.mvcc.ErrFutureRev
      go!"mvcc: required revision is a future revision" go_etcd_io.etcd.server.v3.auth.authErrMsgs
      (go_etcd_io.etcd.server.v3.auth.authErrMsgs_ne_of _ (by decide)) $$ CF HAC
    ihave #HapC := EtcdGrove.errVarApart_cells go_etcd_io.etcd.server.v3.storage.mvcc.ErrCompacted
      go!"mvcc: required revision has been compacted" go_etcd_io.etcd.server.v3.auth.authErrMsgs
      (go_etcd_io.etcd.server.v3.auth.authErrMsgs_ne_of _ (by decide)) $$ CC HAC
    ihave #AF := HapF $$ %g %Hg.1
    ihave #AC := HapC $$ %g %Hg.1
    iunfold EtcdGrove.errVarApart at AF AC
    icases AF with ⟨%f1, %f2, #F1, #F2, %Hf⟩
    icases AC with ⟨%c1, %c2, #C1, #C2, %Hc⟩
    icombine Hkf F1 gives %h1
    icombine Hge F2 gives %h2
    icombine Hkc C1 gives %h3
    icombine Hge C2 gives %h4
    isplitr
    · ipureintro
      constructor
      · intro h; apply Hf; rw [h] at h2; rw [h1] at h2; cases h2; rfl
      · intro h; apply Hc; rw [h] at h4; rw [h3] at h4; cases h4; rfl
    iintro #Hp
    iunfold ctxPassed at Hp
    ihave #Hx := Hp $$ %ea %(And.intro rfl ⟨Hg.2.2.1, Hg.2.2.2.1⟩)
    iapply Hcx $$ Hx
  · -- the read index's
    iunfold readErrIs at Hrd
    ihave #Hei : (go_etcd_io.etcd.server.v3.etcdserver.errors.errorsInit : IProp GF) $$ []
    · iapply isPkgInit_access $$ Pe
    icases Hei with ⟨-, #Hev, #Hcells⟩
    -- an `etcdserver` error variable: apart from mvcc's, an `errors.New` leaf
    ihave #Hvar : iprop(□ ∀ (X m : GoString), ⌜(X, m) ∈ go_etcd_io.etcd.server.v3.etcdserver.errors.errorsMsgs⌝ -∗
        (globalAddr X ↦□ e : IProp GF) -∗
        ⌜e ≠ kf ∧ e ≠ kc⌝ ∗ (ctxPassed e -∗ ∃ m : GoString, go_etcd_io.etcd.cache.v3.descIs e m ∗
          ⌜rangeErrMsgOk m⌝)) $$ []
    · iintro !> %X %m %hm #HX
      ihave #HapF := EtcdGrove.errVarApart_cells go_etcd_io.etcd.server.v3.storage.mvcc.ErrFutureRev
        go!"mvcc: required revision is a future revision" go_etcd_io.etcd.server.v3.etcdserver.errors.errorsMsgs
        (errorsMsgs_ne_of _ (by simp only [go_etcd_io.etcd.server.v3.etcdserver.errors.errorsMsgs,
          List.map_cons, List.map_nil]; decide)) $$ CF Hcells
      ihave #HapC := EtcdGrove.errVarApart_cells go_etcd_io.etcd.server.v3.storage.mvcc.ErrCompacted
        go!"mvcc: required revision has been compacted" go_etcd_io.etcd.server.v3.etcdserver.errors.errorsMsgs
        (errorsMsgs_ne_of _ (by simp only [go_etcd_io.etcd.server.v3.etcdserver.errors.errorsMsgs,
          List.map_cons, List.map_nil]; decide)) $$ CC Hcells
      ihave #AF := HapF $$ %X %(List.mem_map_of_mem (f := Prod.fst) hm)
      ihave #AC := HapC $$ %X %(List.mem_map_of_mem (f := Prod.fst) hm)
      iunfold EtcdGrove.errVarApart at AF AC
      icases AF with ⟨%f1, %f2, #F1, #F2, %Hf⟩
      icases AC with ⟨%c1, %c2, #C1, #C2, %Hc⟩
      icombine Hkf F1 gives %h1
      icombine HX F2 gives %h2
      icombine Hkc C1 gives %h3
      icombine HX C2 gives %h4
      ihave #Hnv := EtcdGrove.errorsNewVars_mem hm $$ Hev
      iunfold EtcdGrove.errorsNewVar at Hnv
      icases Hnv with ⟨%x, #Hx, -⟩
      icombine HX Hx gives %h5
      isplitr
      · ipureintro
        constructor
        · intro h; apply Hf; rw [h] at h2; rw [h1] at h2; cases h2; rfl
        · intro h; apply Hc; rw [h] at h4; rw [h3] at h4; cases h4; rfl
      iintro #Hp
      iunfold ctxPassed at Hp
      have hl := EtcdGrove.errorString_errLeaf x
      ihave #Hx' := Hp $$ %(⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩ : GoInterfaceOk)
        %(And.intro h5 ⟨hl.2.1, hl.2.2.1⟩)
      iapply Hcx $$ Hx'
    icases Hrd with (%Hn | #Hc | #Hs | #Hl | #Ht)
    · exact absurd Hn hne
    · -- a context's value: apart from mvcc's (`Canceled`: its message cell; `DeadlineExceeded`: its
      -- type)
      ihave #Hc' := Hc
      iunfold context.isCtxErr at Hc'
      icases Hc' with (⟨#HcV, %x, %hx, #Hs⟩ | ⟨#HdV, %hv⟩)
      · ihave #Ccn : (EtcdGrove.errVarCell _root_.Perennial.context.Canceled go!"context canceled" : IProp GF) $$ []
        · iunfold EtcdGrove.errVarCell
          iexists x
          rw [← hx]
          iframe HcV
          iunfold EtcdGrove.errStrCell
          iexact Hs
        ihave #AF := EtcdGrove.errVarApart_of _ _ _ _ (by decide) $$ Ccn CF
        ihave #AC := EtcdGrove.errVarApart_of _ _ _ _ (by decide) $$ Ccn CC
        iunfold EtcdGrove.errVarApart at AF AC
        icases AF with ⟨%f1, %f2, #F1, #F2, %Hf⟩
        icases AC with ⟨%c1, %c2, #C1, #C2, %Hc2⟩
        icombine HcV F1 gives %h1
        icombine Hkf F2 gives %h2
        icombine HcV C1 gives %h3
        icombine Hkc C2 gives %h4
        isplitr
        · ipureintro
          constructor
          · intro h; apply Hf; rw [← h] at h2; rw [h1] at h2; cases h2; rfl
          · intro h; apply Hc2; rw [← h] at h4; rw [h3] at h4; cases h4; rfl
        iintro -
        iapply Hcx $$ [HcV]
        ileft; iexact HcV
      · ihave #Hnf := errorsNewVar_of_errVarCell _ _ $$ CF
        ihave #Hnc := errorsNewVar_of_errVarCell _ _ $$ CC
        iunfold EtcdGrove.errorsNewVar at Hnf Hnc
        icases Hnf with ⟨%y, #Hy, -⟩
        icases Hnc with ⟨%z, #Hz, -⟩
        icombine Hkf Hy gives %h1
        icombine Hkc Hz gives %h2
        isplitr
        · ipureintro
          constructor
          · intro h; rw [h, h1] at hv
            injection hv with hv'; injection hv' with ht _
            exact _root_.Perennial.context.deadlineExceededError_ne_ptr _ ht.symm
          · intro h; rw [h, h2] at hv
            injection hv with hv'; injection hv' with ht _
            exact _root_.Perennial.context.deadlineExceededError_ne_ptr _ ht.symm
        iintro -
        iapply Hcx $$ [HdV]
        iright; iexact HdV
    · iapply Hvar $$ %go_etcd_io.etcd.server.v3.etcdserver.errors.ErrStopped %go!"etcdserver: server stopped"
        %(by unfold go_etcd_io.etcd.server.v3.etcdserver.errors.errorsMsgs; mem_tac) Hs
    · iapply Hvar $$ %go_etcd_io.etcd.server.v3.etcdserver.errors.ErrLeaderChanged %go!"etcdserver: leader changed"
        %(by unfold go_etcd_io.etcd.server.v3.etcdserver.errors.errorsMsgs; mem_tac) Hl
    · iapply Hvar $$ %go_etcd_io.etcd.server.v3.etcdserver.errors.ErrTimeout %go!"etcdserver: request timed out"
        %(by unfold go_etcd_io.etcd.server.v3.etcdserver.errors.errorsMsgs; mem_tac) Ht
  · -- the `rangeKeys` wrap: Go's `*fmt.wrapError` (its description's prefix) or Perennial's model's
    -- `*errors.errorString` (its message cell; H0, 2026-11-18)
    iunfold mvcc.rangeKeysErr at Hk
    icases Hk with ⟨-, ⟨%ii, %inner, %Hii, #Hw⟩, -⟩
    subst Hii
    iunfold EtcdGrove.fmt.errorfWrapIs at Hw
    icases Hw with (#HM | #HW)
    · -- the model's: apart from mvcc's variables (the cells' messages differ), a leaf
      iunfold EtcdGrove.fmt.modelErrIs at HM
      icases HM with ⟨%y, %Hy, %s, #Hc, -⟩
      subst Hy
      iunfold EtcdGrove.errVarCell at CF CC
      icases CF with ⟨%xf, #HF, #CFc⟩
      icases CC with ⟨%xc, #HC, #CCc⟩
      icombine Hkf HF gives %h1
      icombine Hkc HC gives %h2
      subst h1 h2
      ihave %Hyf := EtcdGrove.errStrCell_ne y xf _ _
        (fun h => absurd (congrArg List.head? h) (by simp)) $$ Hc CFc
      ihave %Hyc := EtcdGrove.errStrCell_ne y xc _ _
        (fun h => absurd (congrArg List.head? h) (by simp)) $$ Hc CCc
      isplitr
      · ipureintro
        constructor
        · intro h; apply Hyf; injection h with h; injection h with _ hv
          exact go.intoVal_inj (V := Loc) hv
        · intro h; apply Hyc; injection h with h; injection h with _ hv
          exact go.intoVal_inj (V := Loc) hv
      iintro #Hp
      iunfold ctxPassed at Hp
      have hl := EtcdGrove.errorString_errLeaf y
      ihave #Hx' := Hp $$ %(⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #y⟩ : GoInterfaceOk)
        %(And.intro rfl ⟨hl.2.1, hl.2.2.1⟩)
      iapply Hcx $$ Hx'
    -- Go's: its description starts with the format's prefix; an `Unwrap` method, which mvcc's
    -- `*errors.errorString` variables have not
    ihave ⟨%s, #Hds⟩ := go_etcd_io.etcd.cache.v3.wrapErrIs_descIs _ _ _ $$ HW
    iunfold EtcdGrove.fmt.wrapErrIs at HW
    icases HW with ⟨%Hm, -, -⟩
    iunfold EtcdGrove.errVarCell at CF CC
    icases CF with ⟨%xf, #HF, -⟩
    icases CC with ⟨%xc, #HC, -⟩
    icombine Hkf HF gives %h1
    icombine Hkc HC gives %h2
    subst h1 h2
    isplitr
    · ipureintro
      constructor
      · intro h; simp only [interface.mkOk] at h; injection h with h; subst h
        exact absurd Hm.2.1 (EtcdGrove.ErrorStringLeaf.leaf #xf).2.1
      · intro h; simp only [interface.mkOk] at h; injection h with h; subst h
        exact absurd Hm.2.1 (EtcdGrove.ErrorStringLeaf.leaf #xc).2.1
    iintro -
    iexists _
    iframe Hds
    ipureintro
    exact rangeErrMsgOk_of_prefix _ _
      (by unfold go_etcd_io.etcd.cache.v3.futureRevDesc; decide)
      (by unfold go_etcd_io.etcd.cache.v3.compactedDesc; decide)

open Iris.ProofMode in
/-- **S4: what `togRPCError` made of a `Range` error** (k8s etcd3 7c-2 part 2): the gRPC error has
the future revision's description only if `Range`'s was mvcc's `ErrFutureRev`, with the read's facts
(`rangeErrAt`), likewise the compacted one's (`rangeErrDesc`). By `togRPCError`'s branch
(`grpcErrOut`): passed through, an error of its own description (mvcc's own two: `grpcErrMapOk`'s
`mvcc: …` descriptions, G2-a; the others: `rangeErrOther_facts`); mapped, the map's value, of a read
error's description only at mvcc's matching error (`grpcErrMapOk`); the fallback, of a description
that is neither (`rangeErrMsgOk`, the `Error()` of `Range`'s errors, `errMsgP_of_rangeErrOut`). -/
theorem rangeErrDesc_of_grpcErrOut (on : Bool) (E : apply.AEnv GF) (γr : ReadNames) (c : w64)
    (F : mvcc.Log) (o : OpFull) (Q : List EntryModel → IProp GF) (e err : GoInterface)
    (hne : e ≠ GoInterface.nil) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ⊢
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc -∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth -∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.errors -∗
      rangeErrOut on E γr c F o Q e -∗ grpcErrOut rangeErrMsgOk e err -∗
      rangeErrDesc on E γr c F o Q err := by
  iintro #Pv #Pm #Pa #Pe #H #G
  ihave #Hv : (go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.v3rpcInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Pv
  icases Hv with ⟨-, -, -, -, -, -, -, -, #Hcd⟩
  iunfold grpcErrOut at G
  icases G with ⟨%mp, %M, %kf, %kc, -, -, #Hkf, #Hkc, #HM, #Hbr⟩
  ihave %HM0 : ⌜(M !! kf).isSome ∧ (M !! kc).isSome⌝ $$ []
  · iunfold go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.grpcErrMapOk at HM
    icases HM with ⟨%h, -⟩
    ipureintro; exact h.2
  -- mvcc's two errors differ (their message cells)
  ihave %hkfc : ⌜kf ≠ kc⌝ $$ []
  · ihave #Hm : (go_etcd_io.etcd.server.v3.storage.mvcc.mvccInit : IProp GF) $$ []
    · iapply isPkgInit_access $$ Pm
    icases Hm with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, #CC, #CF, -⟩
    iunfold EtcdGrove.errVarCell at CF CC
    icases CF with ⟨%xf, #HF, #CFc⟩
    icases CC with ⟨%xc, #HC, #CCc⟩
    icombine Hkf HF gives %h1
    icombine Hkc HC gives %h2
    subst h1 h2
    ihave %Hne := EtcdGrove.errStrCell_ne xf xc _ _ (by decide) $$ CFc CCc
    ipureintro
    intro h; apply Hne; simp only [interface.mkOk] at h; injection h with h; injection h with _ hv
    exact go.intoVal_inj (V := Loc) hv
  iunfold rangeErrDesc
  iunfold rangeErrOut at H
  icases H with (⟨%ef, #Hf, %He, #Hat⟩ | ⟨%ec, #Hc, %He, #Hat⟩ | #Hoth)
  · -- mvcc's `ErrFutureRev`
    icombine Hkf Hf gives %h
    subst He h
    icases Hbr with (⟨%Hee, -⟩ | %Hmap | ⟨-, %mfb, #Dfb, %Hfb⟩)
    · -- passed through: a key of the map, of a description neither read error's
      subst Hee
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 HM0.1
      ihave ⟨%mk, #Dk, %Hk⟩ := go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.grpcErrMapOk_key $$ HM %hv
      iexists mk
      iframe Dk
      isplitl []
      · iright; iexact Hat
      · ileft; ipureintro; exact Hk.2
    · ihave ⟨%mv, #Dv, %Hv⟩ := go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.grpcErrMapOk_val $$ HM %Hmap
      iexists mv
      iframe Dv
      isplitl []
      · iright; iexact Hat
      · ileft; ipureintro; intro hd; exact hkfc (Hv.2 hd)
    · iexists mfb
      iframe Dfb
      isplitl []
      · iright; iexact Hat
      · ileft; ipureintro; exact Hfb.2
  · -- mvcc's `ErrCompacted`
    icombine Hkc Hc gives %h
    subst He h
    icases Hbr with (⟨%Hee, -⟩ | %Hmap | ⟨-, %mfb, #Dfb, %Hfb⟩)
    · subst Hee
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 HM0.2
      ihave ⟨%mk, #Dk, %Hk⟩ := go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.grpcErrMapOk_key $$ HM %hv
      iexists mk
      iframe Dk
      isplitl []
      · ileft; ipureintro; exact Hk.1
      · iright; iexact Hat
    · ihave ⟨%mv, #Dv, %Hv⟩ := go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.grpcErrMapOk_val $$ HM %Hmap
      iexists mv
      iframe Dv
      isplitl []
      · ileft; ipureintro; intro hd; exact hkfc (Hv.1 hd).symm
      · iright; iexact Hat
    · iexists mfb
      iframe Dfb
      isplitl []
      · ileft; ipureintro; exact Hfb.1
      · iright; iexact Hat
  · -- the others
    ihave ⟨%Hap, #Hpt⟩ := rangeErrOther_facts e kf kc hne $$ Pm Pa Pe Hcd Hkf Hkc Hoth
    icases Hbr with (⟨%Hee, #Hcp⟩ | %Hmap | ⟨-, %mfb, #Dfb, %Hfb⟩)
    · ihave ⟨%md, #Dd, %Hd⟩ := Hpt $$ Hcp
      subst Hee
      iexists md
      iframe Dd
      isplitl []
      · ileft; ipureintro; exact Hd.1
      · ileft; ipureintro; exact Hd.2
    · ihave ⟨%mv, #Dv, %Hv⟩ := go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.grpcErrMapOk_val $$ HM %Hmap
      iexists mv
      iframe Dv
      isplitl []
      · ileft; ipureintro; intro hd; exact Hap.1 (Hv.1 hd)
      · ileft; ipureintro; intro hd; exact Hap.2 (Hv.2 hd)
    · iexists mfb
      iframe Dfb
      isplitl []
      · ileft; ipureintro; exact Hfb.1
      · ileft; ipureintro; exact Hfb.2

/-- **`raftKV`'s `Range` conjunct in the server's auth mode, from `EtcdServer.Range.spec`** (in a
mode other than `.any`, with the store's range check as the server keeps it, `srvAuthLb`). -/
theorem kvRangeOk_of_serverM (hRange : EtcdServer.Range.spec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64) (F : mvcc.Log)
    (d : KVDep GF) (n : Nat) (tok : Option GoString) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ ⌜E.authMode ≠ .any⌝ ∗
        isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr ∗ srvAuthLb s E ⊢
      kvRangeOk s (srvKVAnsM E.authOn s E ρ γr c F d n tok) := by
  iintro ⟨#Hpkg, %Hany, #Hsrv, #Hsrd, #Hlb⟩
  iunfold kvRangeOk
  iintro %ctx %r %o !> %Φ ⟨Hcall, #Hr, %Hok⟩ HΦ
  simp only [srvKVAnsM]
  icases Hcall with ⟨Hcall, Hrc, Hdep, #HF, #Hn, #HtokK⟩
  ihave #Hdep' := kvDep_of_depM E.authOn s E ρ γr tok d $$ Hdep
  iunfold srvCall at Hcall
  icases Hcall with ⟨%ci, %cd, %Hci, #Hctx, #Hlib, #Hspan, #Hstc, #Hct, Hcred, Hlt⟩
  subst Hci
  iapply wp_fupd
  wp_apply hRange s E ρ γr c ci cd tok r o none false (rangeDepQM E.authOn γr.kv d) F n Hany $$ [Hrc]
    as %resp %err ⟨Hrc, Hres⟩
  · iframe #; iframe Hrc
    isplitr
    · simp only [traceutil.ownTraceOpt]; itrivial
    ipureintro; exact validSortTarget_of_rangeCheck o Hok.1
  ihave #Hcore := srvKVCoreM_of_readM E.authOn s E γr $$ Hsrd
  icases Hres with (⟨%Herr, #Hcls, Hok'⟩ | ⟨%Hre, #HaE, #HrO, -⟩)
  · obtain ⟨rfl, Hrn⟩ := Herr
    iunfold rangeReadOkM at Hok'
    icases Hok' with ⟨%log, #Hcert, Hcok, #Hrcp, %Hlen, Hlin, HQl, #Hres, Hown⟩
    imod depQ_leases_none E.authOn o.base.serializable E γr log _ $$ Hcore HQl with HQl
    imodintro
    iapply HΦ
    iunfold kvAnswer
    ihave #Hres' := Hres
    icases Hres' with ⟨%crev, Hres'⟩
    iunfold txn.rangeResult at Hres'
    icases Hres' with (⟨-, %ef, -, %He⟩ | ⟨-, #He⟩ | ⟨-, %kvs, %more, #Hresp, -⟩ | ⟨-, %ec, -, %He⟩)
    · cases He
    · ihave %Hne := mvcc.rangeKeysErr_ne_nil _ $$ He
      exact absurd rfl Hne
    rotate_left
    · cases He
    iunfold txn.rangeResponseIs at Hresp
    icases Hresp with ⟨-, %h, %sl, %ps, #Hhf, %Hhn, #Hrev, -⟩
    ileft
    isplitr
    · ipureintro; exact ⟨rfl, Hrn⟩
    iexists h, W64 ((log.length : Int) - 1)
    ihave ⟨#Hhf2, Hw, Hri⟩ := hdr_of_own _ h _ (mvcc.api.mvccReaders E.γ 1)
      (w64_last_ne_zero log Hlen.2.1 Hlen.2.2.1) $$ [$Hown]
    · iframe #; ipureintro; exact Hhn
    iframe Hhf2 Hw Hri
    simp only
    iframe Hrc Hcred Hlt
    isplitl [Hcok Hlin HQl]
    · iunfold rangeAnsOkM
      iexists log
      iframe Hcert Hcok Hrcp Hres Hlin HQl
      ipureintro; exact ⟨Hlen.1, Hlen.2.1, Hlen.2.2.1, rfl, Hlen.2.2.2⟩
    iintro %hon
    iunfold rangeAuthed
    icases Hcls with ⟨%info, %m, %Hm, #Hc, #Hib, #Hpb, #Hf⟩
    iexists info, m
    iframe Hc Hpb Hf
    isplitr
    · ipureintro; exact Hm
    rw [hon]
    iapply infoBoundM_tok $$ Hib
  · obtain ⟨rfl, Hne⟩ := Hre
    imodintro
    iapply HΦ
    iunfold kvAnswer
    iright
    isplitr
    · iapply srvErrIs_of_applyErrIs _ Hne $$ HaE
    isplitr
    · -- (k8s etcd3 7c-2 part 2, S5) the error's `Error()` has neither read error's description
      ihave #Pm : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
      · iPkgInit
      ihave #Pa : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth $$ []
      · iPkgInit
      ihave #Pe : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.errors $$ []
      · iPkgInit
      iapply errMsgP_of_rangeErrOut _ _ _ _ _ _ _ _ Hne $$ Pm Pa Pe HrO
    simp only
    iframe Hrc Hcred Hlt HrO

/-- **`raftKV`'s `Txn` conjunct in the server's auth mode, from `EtcdServer.Txn.spec`** (as the
other conjuncts; a writing transaction, with auth on, of the permission cache's shape). -/
theorem kvTxnOk_of_serverM (hTxn : EtcdServer.Txn.spec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64) (F : mvcc.Log)
    (d : KVDep GF) (n : Nat) (tok : Option GoString) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ ⌜E.authMode ≠ .any⌝ ∗
        isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr ∗ srvAuthLb s E ⊢
      kvTxnOk s (srvKVAnsM E.authOn s E ρ γr c F d n tok) := by
  iintro ⟨#Hpkg, %Hany, #Hsrv, #Hsrd, #Hlb⟩
  iunfold kvTxnOk
  iintro %ctx %r %cs %ts %es %n' !> %Φ ⟨Hcall, #Hr, %Hok⟩ HΦ
  obtain ⟨Hck, Hdp, HivT, HivE, Hin, Hro, Hsh⟩ := Hok
  obtain ⟨ts', es', hts, hes, hm⟩ := txnModelOf_of_check Hck
  simp only [srvKVAnsM] at Hin ⊢
  simp only [kvDepPreL] at Hro
  icases Hcall with ⟨Hcall, Hrc, Hdep, #HF, #Hn, #HtokK⟩
  iunfold srvCall at Hcall
  icases Hcall with ⟨%ci, %cd, %Hci, #Hctx, #Hlib, #Hspan, #Hstc, #Hct, Hcred, Hlt⟩
  subst Hci
  ihave #Hrt := txnReqIs_txnRequestIs r cs ts es ts' es' hts hes $$ Hr
  generalize ht : ({ cmps := cs, thenOps := ts', elseOps := es' } : TxnModel) = t at hm ⊢
  have hg := txnGetsOk_of_check _ _ _ _ _ Hck hm Hin
  have hT := hTxn s E ρ γr c ci cd tok r t (opDepQ d) (rangeDepQM E.authOn γr.kv d) none false F n
  cases hro : txn.txnReadonly t
  · -- a writing transaction: through raft, as `Put`
    have hdp' : (∃ Q, d = .op1 (.txn t) Q) ∧
        (txn.txnPlain t ∨ ((E.authOn = true ∧ ρ.kv.lm = .revocable) ∧ txnPlainL t)) ∧ txnNoZeroEnd t ∧
        ReqOp.siblingSafeL ts ∧ ReqOp.siblingSafeL es ∧ txn.OpsNoCut t.thenOps ∧
        txn.OpsNoCut t.elseOps := by
      rcases Hro t hm with ⟨h, -⟩ | h
      · rw [hro] at h; cases h
      · exact h
    obtain ⟨hq, hpl, hz, hsT, hsE, hnT, hnE⟩ := hdp'
    have hsh : txn.txnShape t := by
      subst ht
      exact txnShape_of_check n' cs ts es ts' es' hts hes Hck HivT HivE ⟨hz.2.1, hz.2.2⟩
        ⟨hsT, hsE⟩ (hpl.elim (txn.txnLeased_of_plain _) (fun h => h.2)) ⟨hnT, hnE⟩
    have hkn : txn.txnKeysNodup t := by
      subst ht
      exact txnKeysNodup_of_check n' cs ts es ts' es' hts hes Hck HivT HivE ⟨hz.2.1, hz.2.2⟩ ⟨hsT, hsE⟩
    ihave Hdep := txnPermitM_of_dep E.authOn s E ρ γr tok d t
      (hdrBoundM E.authOn s E tok)
      (fun h hm => by rw [h]; exact hdrBoundM_tok s E _ hm)
      ⟨hq, hpl.imp id (fun h => ⟨h.1.1, h.1.2, h.2⟩), hz⟩ ⟨hsh, hkn⟩
      (fun h => Hsh h t hm hro) $$ Hdep
    simp only [hro, Bool.false_eq_true, ↓reduceIte] at hT
    wp_apply hT $$ [Hlt Hcred Hrc Hdep] as %resp %err ⟨Hlt, Hrc, Hres⟩
    · iframe #; iframe Hlt Hcred Hrc Hdep
      isplitr
      · simp only [traceutil.ownTraceOpt]; itrivial
      ipureintro; exact ⟨fun h => h.elim, fun _ => Hdp t hm⟩
    iapply HΦ
    iunfold kvAnswer
    icases Hres with (⟨%Herr, Hok', #Hgate⟩ | ⟨%Hre, #HaE, Hfail⟩)
    · obtain ⟨rfl, Hrn⟩ := Herr
      iunfold txnAppliedOk at Hok'
      simp only [apply.txnOutcomeIs, apply.noSpaceErrIs, Bool.false_eq_true, ↓reduceIte]
      icases Hok' with ⟨%tw, %hm', %rq', %t', %x, %x', %l, %skip, %Hst, ⟨#Hout, %Hnil⟩, Hhdr, #Hcert, HMint, #Hwit,
        Hcok, Hrcpt, %Hwf, ⟨%ltq, %Hltq, HQv⟩⟩
      -- (auth-lease S3b D7) the transaction's lease liveness: the handler's answer does not carry it
      ihave HQv : iprop(∃ lt, ⌜E.authOn = false ∨ ρ.kv.lm = .none → lt = []⌝ ∗ opDepQ d (kvStateOf x.log lt)) $$ [HQv]
      · iexists ltq; iframe HQv; ipureintro; exact Hltq.1
      ihave #Hresp := Hout
      iunfold txn.txnResponseIs at Hresp
      icases Hresp with ⟨-, #Hf⟩
      iunfold txn.txnRespFieldsIs at Hf
      icases Hf with ⟨%h, #Hhf, %Hhn, #Hrev, -⟩
      iunfold apply.appliedHdr at Hhdr
      icases Hhdr with ⟨Hown, %Hlen⟩
      ileft
      isplitr
      · ipureintro; exact ⟨by first | rfl | trivial, Hrn⟩
      iexists h, W64 (mvcc.writeRev x.log
        (txn.srvRunTxn (W64 (x.log.length : Int)) (mvcc.stateAfter x.log) t').2.1 : Int)
      ihave ⟨#Hhf2, Hw, Hri⟩ := hdr_of_own _ h _ (mvcc.api.mvccReaders E.γ 1)
        (writeRev_ne_zero _ _ Hlen.1 (by have := Hlen.2; omega)) $$ [$Hown]
      · iframe #; ipureintro; exact Hhn
      iframe Hhf2 Hw Hri
      iframe Hrc Hlt
      iexists t
      isplitr
      · ipureintro; exact hm
      simp only [hro, Bool.false_eq_true, ↓reduceIte]
      isplitl; rotate_left
      · iintro %hon
        ihave ⟨%tw2, %hm2, %L2, %Hg2, #Hhb2, #HpAf2⟩ := Hgate $$ %hon
        rw [hon]
        iexists tw2
        isplitr
        · ipureintro; exact Hg2.1
        iunfold writeGrantOn
        iexists hm2, L2
        iframe HpAf2
        isplitr
        · ipureintro; exact Hg2.2
        iapply hdrBoundM_tok $$ Hhb2
      iunfold txnAppliedAns
      iexists tw, hm', rq', t', x, x', l, skip
      isplitr
      · ipureintro
        exact ⟨Hst.1, Hst.2.1, Hst.2.2.1, Hst.2.2.2.1, Hst.2.2.2.2.1, rfl, Hst.2.2.2.2.2.1, Hlen.1, Hlen.2,
          Hst.2.2.2.2.2.2⟩
      simp only [apply.txnOutcomeIs, apply.noSpaceErrIs, Bool.false_eq_true, ↓reduceIte]
      iframe Hout Hcert HMint Hwit Hcok Hrcpt HQv
      try (ipureintro; exact Hwf)
      try (ipureintro; trivial)
    · obtain ⟨-, Hne⟩ := Hre
      iright
      isplitr
      · iapply srvErrIs_of_applyErrIs _ Hne $$ HaE
      isplitr
      · iapply errMsgP_of_srvErrIs_of _ _ (fun _ => trivial)
        iapply srvErrIs_of_applyErrIs _ Hne $$ HaE
      simp only
      iframe Hrc Hlt
      iexists t
      isplitr
      · ipureintro; exact hm
      simp only [hro, Bool.false_eq_true, ↓reduceIte]
      iapply txnErrOkM_elim $$ Hfail
  · -- a read-only transaction: read locally
    ihave #Hdep' := kvDep_of_depM E.authOn s E ρ γr tok d $$ Hdep
    simp only [hro, ↓reduceIte] at hT
    iapply wp_fupd
    wp_apply hT $$ [Hlt Hcred Hrc] as %resp %err ⟨Hlt, Hrc, Hcred, Hres⟩
    · iframe #; iframe Hlt Hcred Hrc
      isplitr
      · simp only [traceutil.ownTraceOpt]; itrivial
      ipureintro
      first
        | exact fun _ => ⟨hg hro, Hany⟩
        | exact ⟨fun _ => ⟨hg hro, Hany⟩, fun h => by cases h⟩
    ihave #Hcore := srvKVCoreM_of_readM E.authOn s E γr $$ Hsrd
    icases Hres with (⟨%Herr, #Hcls, Hok'⟩ | ⟨%Hne, #HaE, -⟩)
    · obtain ⟨rfl, Hrn⟩ := Herr
      iunfold txnReadOkM at Hok'
      icases Hok' with ⟨%log, #Hcert, Hcok, #Hrcp, %Hlen, Hlin, HQl, #Hresp, Hown⟩
      imod depQ_leases_none E.authOn (txn.txnSerializable t) E γr log _ $$ Hcore HQl with HQl
      imodintro
      iapply HΦ
      iunfold kvAnswer
      ihave #Hresp' := Hresp
      iunfold txn.txnResponseIs at Hresp'
      icases Hresp' with ⟨-, #Hf⟩
      iunfold txn.txnRespFieldsIs at Hf
      icases Hf with ⟨%h, #Hhf, %Hhn, #Hrev, -⟩
      ileft
      isplitr
      · ipureintro; exact ⟨rfl, Hrn⟩
      iexists h, W64 ((log.length : Int) - 1)
      ihave ⟨#Hhf2, Hw, Hri⟩ := hdr_of_own _ h _ (mvcc.api.mvccReaders E.γ 1)
        (w64_last_ne_zero log Hlen.2.1 Hlen.2.2.1) $$ [$Hown]
      · iframe #; ipureintro; exact Hhn
      iframe Hhf2 Hw Hri
      simp only
      iframe Hrc Hlt
      iexists t
      isplitr
      · ipureintro; exact hm
      simp only [hro, ↓reduceIte]
      iframe Hcred
      isplitl [Hcok Hlin HQl]
      · iunfold txnReadAnsM
        iexists log
        iframe Hcert Hcok Hrcp Hresp Hlin HQl
        ipureintro; exact ⟨Hlen.1, Hlen.2.1, Hlen.2.2.1, rfl, Hlen.2.2.2⟩
      iintro %hon
      iunfold txnAuthed
      icases Hcls with ⟨%info, %m, %Hm, #Hc, #Hib, #Hf⟩
      iexists info, m
      iframe Hc Hf
      isplitr
      · ipureintro; exact Hm
      rw [hon]
      iapply infoBoundM_tok $$ Hib
    · imodintro
      iapply HΦ
      iunfold kvAnswer
      iright
      isplitr
      · iapply srvErrIs_of_applyErrIs _ Hne $$ HaE
      isplitr
      · iapply errMsgP_of_srvErrIs_of _ _ (fun _ => trivial)
        iapply srvErrIs_of_applyErrIs _ Hne $$ HaE
      simp only
      iframe Hrc Hlt
      iexists t
      isplitr
      · ipureintro; exact hm
      simp only [hro, ↓reduceIte]
      iexact Hcred

/-- **`raftKV`'s getters, from the server's** (`KV().Rev()`: strict M1, `KV.Rev.contract` at the
store handle's dynamic type (`shapes.law`), with the thread's token (`revR`) and a reader's update
from the store invariant (`au_read`, at the read side's floor); `Cluster().ID()`, `MemberID`,
`Term`, `Leader`). -/
theorem kvGetOk_of_serverM (hKV : EtcdServer.KV.spec (GF := GF) (hG := hG))
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hP : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hR : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (hCl : EtcdServer.Cluster.spec (GF := GF) (hG := hG))
    (hID : membership.RaftCluster.ID.spec (GF := GF) (hG := hG))
    (hMID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (hTerm : EtcdServer.Term.spec (GF := GF) (hG := hG))
    (hLead : EtcdServer.Leader.spec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64) (F : mvcc.Log)
    (d : KVDep GF) (n : Nat) (tok : Option GoString) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr ⊢
      kvGetOk s (srvKVAnsM E.authOn s E ρ γr c F d n tok) := by
  iintro ⟨#Hpkg, #Hsrv, #Hsrd⟩
  ihave #Hmv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  ihave #Hmb : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership $$ []
  · iPkgInit
  ihave ⟨⟨%v, #Hv⟩, #HsrvB⟩ := (isServerReqM_split _ _ _ _).1 $$ Hsrv
  iunfold srvReqFieldsAtM at Hv
  icases Hv with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hmid, #Hlead, #Hcl, #Htr, #Hpeers, -⟩
  iunfold srvPeersOk at Hpeers
  icases Hpeers with ⟨#Hcid, -, -⟩
  iunfold isServerReadM at Hsrd
  icases Hsrd with ⟨%w, #Hw⟩
  iunfold srvReadFieldsAtM at Hw
  icases Hw with ⟨-, -, #Hkvf, #Hkv, %Hkvw, -, -, -, -, -, -, -, #Hterm, ⟨%log₀, #Hl0, -⟩, -, #Hkvi, -⟩
  icases txn.isMvcc_shape hsh w.kv E.γ $$ Hkv with ⟨%Hsh, -⟩
  obtain ⟨kty, kvv, Hkveq, -, -, hRevC, -⟩ := Hsh
  ihave Hkv' : □ mvcc.api.isMvcc (interface.mkOk kty kvv) E.γ $$ []
  · rw [← Hkveq]; imodintro; iexact Hkv
  icases Hkv' with #Hkv'
  -- the store invariant and `E.Nx`/`E.Cp`'s instances, in either mode (`srvKVInvsM_kvStoreInv`)
  ihave ⟨#Hks, %Hks2⟩ := srvKVInvsM_kvStoreInv E.authOn s E γr $$ Hkvi
  obtain ⟨hNxP, hNxT, hCpP, hCpT⟩ := Hks2
  iunfold kvGetOk
  simp only [srvKVAnsM]
  isplitr
  · iintro !> %Φ - HΦ
    wp_apply hKV s w.kv $$ []
    · iframe #
    iapply HΦ
    iexists ⟨kty, kvv⟩
    isplitr
    · ipureintro; exact Hkveq
    iintro !> %Φ' Hrdr HΦ'
    ihave Hau := srvApi.au_read E.Nx E.Cp hP hR E.kv E.γ E.γs log₀ $$ Hks Hl0
    iunfold srvApi.auRead at Hau
    wp_apply (hRevC E.γ _) $$ [$Hkv' $Hrdr $Hau] as %rv ⟨Hrdr, -⟩
    iapply HΦ'
    iexact Hrdr
  isplitr
  · iintro !> %Φ - HΦ
    wp_apply hCl s v.cluster $$ []
    · iframe #
    iapply HΦ
    iexists ⟨go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty, #v.cluster⟩
    isplitr
    · ipureintro; rfl
    iintro !> %Φ' - HΦ'
    wp_apply hID v.cluster v.cid $$ []
    · iframe #
    iapply HΦ'
    itrivial
  isplitr
  · iintro !> %Φ - HΦ
    wp_apply hMID s v.memberID $$ []
    · iframe #
    iapply HΦ
    itrivial
  iunfold raftStatusOk
  isplitr
  · iintro !> %Φ - HΦ
    wp_apply hTerm s $$ []
    · iframe #
    iexact HΦ
  · iintro !> %Φ - HΦ
    wp_apply hLead s $$ []
    · iframe #
      iunfold srvLeadInv
      iunfold srvAtomicU64 at Hlead
      iexact Hlead
    iexact HΦ


/-- **The server's contract in its auth mode, from the server's linked specs** (the auth component's
stage 4; no premise but the server's facts in its mode, the store's range check, `srvAuthLb`, and a
mode other than `.any`), at the parameters `srvKVAnsM E.authOn s E ρ γr c F d n tok`. -/
theorem raftKV_of_serverM (hPut : EtcdServer.Put.spec (GF := GF) (hG := hG))
    (hDel : EtcdServer.DeleteRange.spec (GF := GF) (hG := hG))
    (hRange : EtcdServer.Range.spec (GF := GF) (hG := hG))
    (hTxn : EtcdServer.Txn.spec (GF := GF) (hG := hG))
    (hKV : EtcdServer.KV.spec (GF := GF) (hG := hG))
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hP : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hR : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (hCl : EtcdServer.Cluster.spec (GF := GF) (hG := hG))
    (hID : membership.RaftCluster.ID.spec (GF := GF) (hG := hG))
    (hMID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (hTerm : EtcdServer.Term.spec (GF := GF) (hG := hG))
    (hLead : EtcdServer.Leader.spec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64) (F : mvcc.Log)
    (d : KVDep GF) (n : Nat) (tok : Option GoString) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ ⌜E.authMode ≠ .any⌝ ∗
        isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr ∗ srvAuthLb s E ⊢
      raftKV s (srvKVAnsM E.authOn s E ρ γr c F d n tok) := by
  iintro ⟨#Hpkg, %Hany, #Hsrv, #Hsrd, #Hlb⟩
  iunfold raftKV
  isplitr
  · iapply kvRangeOk_of_serverM hRange s E ρ γr c F d n tok; iframe #; ipureintro; exact Hany
  isplitr
  · iapply kvPutOk_of_serverM hPut s E ρ γr c F d n tok; iframe #
  isplitr
  · iapply kvDeleteOk_of_serverM hDel s E ρ γr c F d n tok; iframe #
  isplitr
  · iapply kvTxnOk_of_serverM hTxn s E ρ γr c F d n tok; iframe #; ipureintro; exact Hany
  iapply kvGetOk_of_serverM hKV hsh hP hR hCl hID hMID hTerm hLead s E ρ γr c F d n tok; iframe #

/-- A handler's answer under parameters `A'` is one under `A` when `A'`'s answers give `A`'s. -/
theorem kvAnswer_mono (A A' : KVAns GF) (hR : A.revR = A'.revR)
    (hok : ∀ q resp h r, A'.ok q resp h r ⊢ A.ok q resp h r)
    (herr : ∀ q e, A'.err q e ⊢ A.err q e) (hP : ∀ q m, A'.errP q m → A.errP q m)
    (q : KVReq) (hf resp : Loc) (err : GoInterface) :
    kvAnswer A' q hf resp err ⊢ kvAnswer A q hf resp err := by
  unfold kvAnswer
  rw [hR]
  iintro (⟨%Hok, %h, %r, Hh, Hw, Hrv, Ha⟩ | ⟨He, #Hm, Ha⟩)
  · ileft
    isplitr
    · ipureintro; exact Hok
    iexists h, r
    iframe Hh Hw Hrv
    iapply hok $$ Ha
  · iright
    iframe He
    isplitr
    · iapply errMsgP_mono err _ _ (hP q) $$ Hm
    iapply herr $$ Ha

/-- **The server's contract is monotone in its parameters** (the auth component's stage 4): `raftKV`
under `A'` is `raftKV` under `A` when `A`'s calls update to `A'`'s, its requests are `A'`'s, `A'`'s
answers give `A`'s, and the revision readers agree. -/
theorem raftKV_mono (s : Loc) (A A' : KVAns GF) (hR : A.revR = A'.revR)
    (hcall : ∀ ctx, A.call ctx ⊢ |==> A'.call ctx) (hpre : ∀ q, A.pre q → A'.pre q)
    (hok : ∀ q resp h r, A'.ok q resp h r ⊢ A.ok q resp h r)
    (herr : ∀ q e, A'.err q e ⊢ A.err q e) (hP : ∀ q m, A'.errP q m → A.errP q m) :
    raftKV s A' ⊢ raftKV s A := by
  unfold raftKV
  iintro #⟨Hrg, Hput, Hdel, Htxn, Hget⟩
  isplitr
  · iunfold kvRangeOk
    iunfold kvRangeOk at Hrg
    iintro %ctx %r %o !> %Φ ⟨Hcall, #Hr, %Hok⟩ HΦ
    imod hcall ctx $$ Hcall with Hcall
    iapply Hrg $$ [Hcall]
    · iframe Hcall Hr; ipureintro; exact ⟨Hok.1, hpre _ Hok.2⟩
    inext
    iintro %resp %err Hans
    iapply HΦ
    iapply kvAnswer_mono A A' hR hok herr hP $$ Hans
  isplitr
  · iunfold kvPutOk
    iunfold kvPutOk at Hput
    iintro %ctx %r %o !> %Φ ⟨Hcall, #Hr, %Hok⟩ HΦ
    imod hcall ctx $$ Hcall with Hcall
    iapply Hput $$ [Hcall]
    · iframe Hcall Hr; ipureintro; exact ⟨Hok.1, hpre _ Hok.2⟩
    inext
    iintro %resp %err Hans
    iapply HΦ
    iapply kvAnswer_mono A A' hR hok herr hP $$ Hans
  isplitr
  · iunfold kvDeleteOk
    iunfold kvDeleteOk at Hdel
    iintro %ctx %r %o !> %Φ ⟨Hcall, #Hr, %Hok⟩ HΦ
    imod hcall ctx $$ Hcall with Hcall
    iapply Hdel $$ [Hcall]
    · iframe Hcall Hr; ipureintro; exact ⟨Hok.1, hpre _ Hok.2⟩
    inext
    iintro %resp %err Hans
    iapply HΦ
    iapply kvAnswer_mono A A' hR hok herr hP $$ Hans
  isplitr
  · iunfold kvTxnOk
    iunfold kvTxnOk at Htxn
    iintro %ctx %r %cs %ts %es %n !> %Φ ⟨Hcall, #Hr, %Hok⟩ HΦ
    imod hcall ctx $$ Hcall with Hcall
    iapply Htxn $$ [Hcall]
    · iframe Hcall Hr; ipureintro
      exact ⟨Hok.1, Hok.2.1, Hok.2.2.1, Hok.2.2.2.1, hpre _ Hok.2.2.2.2⟩
    inext
    iintro %resp %err Hans
    iapply HΦ
    iapply kvAnswer_mono A A' hR hok herr hP $$ Hans
  iunfold kvGetOk
  iunfold kvGetOk at Hget
  rw [hR]
  iexact Hget


/-- **The off answers from the mode's at auth off** (a bridge; the auth component's stage 5): the
server's contract at `srvKVAnsM false` with no auth bound gives it at the off answers `srvKVAns`
(through `raftKV_mono`: the gated rows dropped, the auth bound `0` free, `authPubLbM_zero`). -/
theorem raftKV_srvKVAnsM_false (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (c : w64) (F : mvcc.Log) (d : KVDep GF) :
    raftKV s (srvKVAnsM false s E ρ γr c F d 0 none) ⊢ raftKV s (srvKVAns s E ρ γr c F d) :=
  raftKV_mono s _ _ rfl
    (fun ctx => by
      simp only [srvKVAns, srvKVAnsM]
      iintro ⟨Hc, Hrc, Hdep, #HF⟩
      imod kvDepOwnM_of_dep _ s E ρ γr none d $$ Hdep with Hdep
      imod (authPubLbM_zero (GF := GF) E.authMode) with #Hn
      imodintro
      iframe Hc Hrc Hdep HF Hn
      iintro !> %h; cases h)
    (fun q h => ⟨h.1, kvDepPreL_of_pre _ d q h.2, fun h' => by cases h'⟩)
    (fun q resp h r => by
      cases q with
      | put o => simp only [srvKVAns, srvKVAnsM]; iintro ⟨Hrc, Ha, -⟩; iframe
      | deleteRange o => simp only [srvKVAns, srvKVAnsM]; iintro ⟨Hrc, Ha, -⟩; iframe
      | range o =>
        simp only [srvKVAns, srvKVAnsM]; iintro ⟨Hrc, Hc, Hl, Ha, -⟩; iframe
      | txn cs ts es =>
        simp only [srvKVAns, srvKVAnsM]
        iintro ⟨Hrc, Hl, %t, %ht, H⟩
        iframe Hrc Hl
        iexists t
        isplitr
        · ipureintro; exact ht
        cases hr : txn.txnReadonly t <;> simp only [Bool.false_eq_true, ↓reduceIte]
        · icases H with ⟨H, -⟩; iexact H
        · icases H with ⟨Hc, Ha, -⟩; iframe)
    (fun q e => by
      cases q <;> simp only [srvKVAns, srvKVAnsM] <;>
        first | exact .rfl | (iintro ⟨Hrc, Hc, Hl, -⟩; iframe))
    (fun _ _ _ => trivial)

/-- **The on answers from the mode's at auth on** (a bridge; the auth component's stage 5): the
server's contract at `srvKVAnsM true` gives it at `srvKVAnsOn` (through `raftKV_mono`: the gates
opened at `rfl`). -/
theorem raftKV_srvKVAnsM_true (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (c : w64) (F : mvcc.Log) (d : KVDep GF) (na : Nat) (tok : Option GoString) :
    raftKV s (srvKVAnsM true s E ρ γr c F d na tok) ⊢ raftKV s (srvKVAnsOn s E ρ γr c F d na tok) :=
  raftKV_mono s _ _ rfl
    (fun ctx => by
      simp only [srvKVAnsOn, srvKVAnsM]
      iintro ⟨Hc, Hrc, Hdep, #HF, #Hn, #Ht⟩
      imodintro
      iframe Hc Hrc HF Hn
      isplitl [Hdep]
      · iapply (kvDepOwnM_true s E ρ γr tok d).2 $$ Hdep
      iintro !> -; iexact Ht)
    (fun q h => ⟨h.1, kvDepPreML_of_on _ d q h.2⟩)
    (fun q resp h r => by
      cases q with
      | put o =>
        simp only [srvKVAnsOn, srvKVAnsM]
        iintro ⟨Hrc, Ha, Hg⟩; iframe Hrc Ha; iapply Hg; ipureintro; first | rfl | trivial
      | deleteRange o =>
        simp only [srvKVAnsOn, srvKVAnsM]
        iintro ⟨Hrc, Ha, Hg⟩; iframe Hrc Ha; iapply Hg; ipureintro; first | rfl | trivial
      | range o =>
        simp only [srvKVAnsOn, srvKVAnsM]
        iintro ⟨Hrc, Hc, Hl, Ha, Hg⟩; iframe Hrc Hc Hl Ha; iapply Hg; ipureintro; first | rfl | trivial
      | txn cs ts es =>
        simp only [srvKVAnsOn, srvKVAnsM]
        iintro ⟨Hrc, Hl, %t, %ht, H⟩
        iframe Hrc Hl
        iexists t
        isplitr
        · ipureintro; exact ht
        cases hr : txn.txnReadonly t <;> simp only [Bool.false_eq_true, ↓reduceIte]
        · icases H with ⟨Ha, Hg⟩; iframe Ha; iapply Hg; ipureintro; first | rfl | trivial
        · icases H with ⟨Hc, Ha, Hg⟩; iframe Hc Ha; iapply Hg; ipureintro; first | rfl | trivial)
    (fun q e => by
      cases q <;> simp only [srvKVAnsOn, srvKVAnsM] <;>
        first | exact .rfl | (iintro ⟨Hrc, Hc, Hl, -⟩; iframe))
    (fun _ _ _ => trivial)

section monoT
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-! ### O2: monotonicity in the TLS fact (2026-11-23)

The replies' facts are monotone in `T` (`□ (T1 -∗ T2)` turns one at `T1` into one at `T2`), the
callers' updates antitone (an update told the grant at `T2` is one told it at `T1`). -/

open Iris.ProofMode in
theorem hdrBoundT_mono (T1 T2 : IProp GF) (M : auth.AuthMode) (tok : Option GoString)
    (hm : apply.HeaderModel) :
    iprop(□ (T1 -∗ T2)) ∗ hdrBoundT T1 M tok hm ⊢ hdrBoundT T2 M tok hm := by
  unfold hdrBoundT
  iintro ⟨#HT, H⟩
  icases H with (H | (H | H))
  · ileft; iexact H
  · iright; ileft; iexact H
  · iright; iright; iapply HT $$ H

open Iris.ProofMode in
theorem rangeAuthed_mono (T1 T2 : IProp GF) (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (n : Nat)
    (tok : Option GoString) (o : OpFull) :
    iprop(□ (T1 -∗ T2)) ∗ rangeAuthed T1 E γr c n tok o ⊢ rangeAuthed T2 E γr c n tok o := by
  unfold rangeAuthed
  iintro ⟨#HT, %info, %m, %hn, Hc, Hi, Hp, Hf⟩
  iexists info, m
  isplitr
  · ipureintro; exact hn
  iframe Hc Hp Hf
  iapply infoBoundT_mono T1 T2
  iframe HT Hi

open Iris.ProofMode in
theorem txnAuthed_mono (T1 T2 : IProp GF) (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (n : Nat)
    (tok : Option GoString) (t : TxnModel) :
    iprop(□ (T1 -∗ T2)) ∗ txnAuthed T1 E γr c n tok t ⊢ txnAuthed T2 E γr c n tok t := by
  unfold txnAuthed
  iintro ⟨#HT, %info, %m, %hn, Hc, Hi, Hf⟩
  iexists info, m
  isplitr
  · ipureintro; exact hn
  iframe Hc Hf
  iapply infoBoundT_mono T1 T2
  iframe HT Hi

open Iris.ProofMode in
theorem writeGrantOn_mono (T1 T2 : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (rq0 : apply.IRRModel) :
    iprop(□ (T1 -∗ T2)) ∗ writeGrantOn T1 E ρ tok rq0 ⊢ writeGrantOn T2 E ρ tok rq0 := by
  unfold writeGrantOn
  iintro ⟨#HT, %hm, %L, %hg, Hb, Hp⟩
  iexists hm, L
  isplitr
  · ipureintro; exact hg
  iframe Hp
  iapply hdrBoundT_mono T1 T2
  iframe HT Hb

open Iris.ProofMode in
theorem opGrantT_mono (T1 T2 : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (op : KVOp) (L₀ : List EntryModel) (σ : KVState) :
    iprop(□ (T1 -∗ T2)) ∗ opGrantT T1 E ρ tok op L₀ σ ⊢ opGrantT T2 E ρ tok op L₀ σ := by
  have hb : ∀ hm, iprop(□ (T1 -∗ T2)) ∗ hdrBoundT T1 E.authMode tok hm ⊢ hdrBoundT T2 E.authMode tok hm :=
    fun hm => hdrBoundT_mono T1 T2 E.authMode tok hm
  cases op with
  | put o => exact writeGrantG_mono_with _ _ _ _ _ _ σ _ hb
  | deleteRange o => exact writeGrantG_mono_with _ _ _ _ _ _ σ _ hb
  | leaseGrant id ttl => exact writeGrantG_mono_with _ _ _ _ _ _ σ _ hb
  | leaseRevoke id => exact writeGrantG_mono_with _ _ _ _ _ _ σ _ hb
  | txn t =>
    simp only [opGrantT]
    iintro ⟨#HT, %tw, %h, H⟩
    iexists tw
    isplitr
    · ipureintro; exact h
    iapply writeGrantG_mono_with _ _ _ _ _ _ σ _ hb
    iframe HT H
  | _ => simp only [opGrantT]; iintro -; itrivial

open Iris.ProofMode in
/-- A caller's update told the grant at `T2` is one told it at `T1`. -/
theorem kvOpAuOn_mono (T1 T2 : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (op : KVOp) (Q : KVState → IProp GF) :
    iprop(□ (T1 -∗ T2)) ∗ kvOpAuOn T2 E ρ tok op Q ⊢ kvOpAuOn T1 E ρ tok op Q := by
  unfold kvOpAuOn
  iintro ⟨#HT, %L₀, #HL, H⟩
  iexists L₀
  iframe HL
  iapply kvAu1G_mono_with _ _ _ _ _ iprop(□ (T1 -∗ T2)) (fun σ => opGrantT_mono T1 T2 E ρ tok op L₀ σ)
  iframe HT H

open Iris.ProofMode in
/-- `kvOpAuOn_mono` in the auth mode `on`. -/
theorem kvOpAuM_mono (on : Bool) (T1 T2 : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames)
    (tok : Option GoString) (op : KVOp) (Q : KVState → IProp GF) :
    iprop(□ (T1 -∗ T2)) ∗ kvOpAuM on T2 E ρ tok op Q ⊢ kvOpAuM on T1 E ρ tok op Q := by
  unfold kvOpAuM
  iintro ⟨#HT, %L₀, #HL, H⟩
  iexists L₀
  iframe HL
  iapply kvAu1G_mono_with _ _ _ _ _ iprop(□ (T1 -∗ T2))
  rotate_left
  · iframe HT H
  intro σ
  iintro ⟨#HT', H'⟩ %h
  iapply opGrantT_mono T1 T2 E ρ tok op L₀ σ
  iframe HT'
  iapply H' $$ %h

end monoT

end proofs

end v3rpc
end EtcdGrove
end Perennial
