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
- a call is at a context carrying the token `tok` (`auth.ctxTokenOf`; the parameter is the
  caller's, as the deposit `d` is);
- a successful write's answer is `srvKVAns`'s and the grant (`writeGrantOn`, 2026-10-28): the
  request with the header the server stamped (`hm`) was granted at the committed log `L` before
  its entry (`grantedAt`), the header's user is the empty one or the one `tok` was issued to
  (`hdrBoundT`), and `L` followed by the write's own entry is committed (`pubAfterM`, with the auth
  state after it published). An error answer says nothing more: a refused request's caller needs
  nothing from it (`examples/etcd/auth`'s `Work` panics only when a refused request succeeds).

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

/-- **What a request must be with auth on** (`kvDepPre`'s, and of the shape the permission cache
decides, `kvReqShape`; a put's non-empty key is the gRPC check's). -/
def kvDepPreOn (d : KVDep GF) (q : KVReq) : Prop :=
  kvDepPre d q ∧ kvReqShape q

/-- **What a request must be, in the auth mode `on`**: `kvDepPre`, and with auth on the shape. -/
def kvDepPreM (on : Bool) (d : KVDep GF) (q : KVReq) : Prop :=
  kvDepPre d q ∧ (on = true → kvReqShape q)

theorem kvDepPreM_of_on (on : Bool) (d : KVDep GF) (q : KVReq) (h : kvDepPreOn d q) :
    kvDepPreM on d q :=
  ⟨h.1, fun _ => h.2⟩

/-- **A successful `Range` of `o` with auth on** (`rangeAnsOkM` with auth on). -/
abbrev rangeAnsOkOn (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (F : mvcc.Log) (o : OpFull)
    (resp : Loc) (r : w64) (Q : List EntryModel → IProp GF) : IProp GF :=
  rangeAnsOkM true E γr c F o resp r Q

/-- **A successful read-only `Txn` of `t` with auth on** (`txnReadAnsM` with auth on). -/
abbrev txnReadAnsOn (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (F : mvcc.Log) (t : TxnModel)
    (Q : List EntryModel → IProp GF) (resp : Loc) (r : w64) : IProp GF :=
  txnReadAnsM true E γr c F t Q resp r

/-- An auth info bound to the context `ctx` is bound to its token. -/
theorem infoBoundM_tok (s : Loc) (E : apply.AEnv GF) (ctx : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) :
    infoBoundM (GF := GF) true s E ctx info ⊢ infoBoundT s E.authMode (auth.ctxTokenOf ctx) info := by
  unfold infoBoundM infoBoundT principalBound
  iintro H; iexact H

/-- **A read's check, as the answer reports it** (persistent): the permissions the check of `o`
saw granted at states recorded at an index `m` at least the caller's bound `n`, and for a
linearizable read no older than the auth state the committed log through the read index `c` left;
the auth info checked the caller's (`infoBoundT`, E3zb, 2026-10-28). -/
def rangeAuthed (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (n : Nat)
    (tok : Option GoString) (o : OpFull) : IProp GF :=
  iprop(∃ (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (m : Nat), ⌜n ≤ m⌝ ∗
    apply.rangeClassFrom E.authMode m info o ∗ infoBoundT s E.authMode tok info ∗
    (if o.base.serializable then iprop(True) else authFloorAt E.authMode γr c m))

instance rangeAuthed_persistent (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (n : Nat)
    (tok : Option GoString) (o : OpFull) : Persistent (rangeAuthed (GF := GF) s E γr c n tok o) := by
  unfold rangeAuthed; split <;> infer_instance

/-- **A read-only transaction's checks, as the answer reports them** (`rangeAuthed`'s). -/
def txnAuthed (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (n : Nat)
    (tok : Option GoString) (t : TxnModel) : IProp GF :=
  iprop(∃ (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (m : Nat), ⌜n ≤ m⌝ ∗
    txnClassFrom E.authMode m info t ∗ infoBoundT s E.authMode tok info ∗
    (if txn.txnSerializable t then iprop(True) else authFloorAt E.authMode γr c m))

instance txnAuthed_persistent (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (n : Nat)
    (tok : Option GoString) (t : TxnModel) : Persistent (txnAuthed (GF := GF) s E γr c n tok t) := by
  unfold txnAuthed; split <;> infer_instance

/-- **A header's user is the caller's** (persistent): the empty user, or the one the caller's
token `tok` was issued to (`auth.tokOk`), or the server's TLS fallback is on (`principalBound`'s,
over the token instead of the context: `hdrBoundM_tok`). -/
def hdrBoundT (s : Loc) (M : auth.AuthMode) (tok : Option GoString) (hm : apply.HeaderModel) :
    IProp GF :=
  iprop(⌜hm.username = (zeroValDef : GoString)⌝ ∨
    ((∃ token : GoString, ⌜tok = some token⌝ ∗ auth.tokOk M token hm.username) ∨ srvTLSId s))

instance hdrBoundT_persistent (s : Loc) (M : auth.AuthMode) (tok : Option GoString)
    (hm : apply.HeaderModel) : Persistent (hdrBoundT (GF := GF) s M tok hm) := by
  unfold hdrBoundT; infer_instance

/-- **A successful write's grant** (persistent; see the file header): for the request `rq0` with
the header the server stamped, granted at the committed log `L` before its entry, the header's user
the caller's, and `L` with the entry committed. -/
def writeGrantOn (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (rq0 : apply.IRRModel) : IProp GF :=
  iprop(∃ (hm : apply.HeaderModel) (L : List EntryModel),
    ⌜grantedAt ρ.kv srvAuthSt0 (apply.withHeader rq0 hm) L⌝ ∗ hdrBoundT s E.authMode tok hm ∗
    pubAfterM true E ρ (apply.withHeader rq0 hm) L)

instance writeGrantOn_persistent (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (tok : Option GoString) (rq0 : apply.IRRModel) :
    Persistent (writeGrantOn (GF := GF) s E ρ tok rq0) := by
  unfold writeGrantOn; infer_instance

/-- A header bound to the context `ctx` is bound to its token (`hdrBoundT`). -/
theorem hdrBoundM_tok (s : Loc) (E : apply.AEnv GF) (ctx : GoInterface) (hm : apply.HeaderModel) :
    hdrBoundM (GF := GF) true s E ctx hm ⊢ hdrBoundT s E.authMode (auth.ctxTokenOf ctx) hm := by
  unfold hdrBoundM hdrBoundT principalBound
  iintro H; iexact H

/-- **A write's grant, as the server tells the client's update** (the auth-mode merge's step 5,
2026-10-29): `writeGrantG` of the write's request (for a transaction, of some wire transaction of
it), the header bound to the caller's token (`hdrBoundT`), past the client's lower bound `L₀` of
the requested log. -/
def opGrantT (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString) :
    KVOp → List EntryModel → KVState → IProp GF
  | .put o, L₀ => writeGrantG ρ.kv srvAuthSt0 (hdrBoundT s E.authMode tok) (irrPut o) L₀
  | .deleteRange o, L₀ =>
    writeGrantG ρ.kv srvAuthSt0 (hdrBoundT s E.authMode tok) (irrDeleteRange o) L₀
  | .txn t, L₀ => fun σ => iprop(∃ tw : txn.TxnModelW, ⌜tw.toModel = t⌝ ∗
      writeGrantG ρ.kv srvAuthSt0 (hdrBoundT s E.authMode tok) (irrTxn tw) L₀ σ)
  | _, _ => fun _ => iprop(True)

/-- **A write's update with auth on, at the token `tok`** (the auth-mode merge's 5a, 2026-10-29):
fired at most once, at a lower bound `L₀` of the requested log the caller holds (`srvReqLogLb`),
told the write's grant (`opGrantT`) when it fires. -/
def kvOpAuOn (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString) (op : KVOp)
    (Q : KVState → IProp GF) : IProp GF :=
  iprop(∃ L₀ : List EntryModel, srvReqLogLb ρ.raft L₀ ∗
    kvAu1G ρ.kv (kvOpStep op) (opGrantT s E ρ tok op L₀) Q)

/-- **The deposit with auth on** (step 5): `kvDepOwn`'s, a write's update told its grant when it
fires (`opGrantT`), at a lower bound `L₀` of the requested log the caller holds
(`srvReqLogLb`). One that ignores the grant is one (`kvDepOwnOn_of_dep`). -/
def kvDepOwnOn (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (tok : Option GoString) : KVDep GF → IProp GF
  | .op1 o Q => kvOpAuOn s E ρ tok o Q
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
    mvcc.idxCert E.γ.idx F ∗ auth.authPubLbM E.authMode n ∗ ⌜auth.ctxTokenOf ctx = tok⌝)
  pre q := (match q with
    | .txn cs ts es => txnInModel cs ts es
    | _ => True) ∧ kvDepPreOn d q
  ok q resp _h r := iprop(srvRdCall s E γr c ∗ match q with
    | .put o => iprop(putAppliedOk s E ρ.rd F o (opDepQ d) resp r ∗
        writeGrantOn s E ρ tok (irrPut o))
    | .deleteRange o => iprop(deleteAppliedOk s E ρ.rd F o (opDepQ d) resp r ∗
        writeGrantOn s E ρ tok (irrDeleteRange o))
    | .range o => iprop(idCred ρ.ids 1 ∗ srvLeadTimeReader s ∗
        rangeAnsOkOn E γr c F o resp r (rangeDepQOn γr.kv d) ∗ rangeAuthed s E γr c n tok o)
    | .txn cs ts es => iprop(srvLeadTimeReader s ∗ ∃ t, ⌜txnModelOf cs ts es = some t⌝ ∗
        if txn.txnReadonly t then iprop(idCred ρ.ids 1 ∗
          txnReadAnsOn E γr c F t (rangeDepQOn γr.kv d) resp r ∗ txnAuthed s E γr c n tok t)
        else iprop(txnAppliedAns E ρ.rd F t (opDepQ d) resp r ∗
          ∃ tw : txn.TxnModelW, ⌜tw.toModel = t⌝ ∗ writeGrantOn s E ρ tok (irrTxn tw))))
  err q e := iprop(srvRdCall s E γr c ∗ match q with
    | .put o => putErrOk s E ρ F o e
    | .deleteRange o => deleteErrOk s E ρ F o e
    | .range _ => iprop(idCred ρ.ids 1 ∗ srvLeadTimeReader s)
    | .txn cs ts es => iprop(srvLeadTimeReader s ∗ ∃ t, ⌜txnModelOf cs ts es = some t⌝ ∗
        if txn.txnReadonly t then idCred ρ.ids 1 else txnErrOk E ρ F t e))
  revR := mvcc.storeReader E.s E.γ

/-- **A write's update in the auth mode `on`** (`kvOpAuOn`'s, the auth component's stage 4): fired at
most once, at a lower bound `L₀` of the requested log the caller holds, told the write's grant
(`opGrantT`) when it fires with auth on (`⌜on = true⌝ → …`). -/
def kvOpAuM (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (op : KVOp) (Q : KVState → IProp GF) : IProp GF :=
  iprop(∃ L₀ : List EntryModel, srvReqLogLb ρ.raft L₀ ∗
    kvAu1G ρ.kv (kvOpStep op) (fun σ => iprop(⌜on = true⌝ → opGrantT s E ρ tok op L₀ σ)) Q)

/-- **A request's deposit in the auth mode `on`**: a write's update by `kvOpAuM`; the rest as
`kvDepOwn`. Off, it is `kvDepOwn` (`kvDepOwnM_of_dep`, `kvDepOwnM_false`); on, `kvDepOwnOn`
(`kvDepOwnM_true`). -/
def kvDepOwnM (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (tok : Option GoString) : KVDep GF → IProp GF
  | .op1 o Q => kvOpAuM on s E ρ tok o Q
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
        (fun σ => iprop(⌜false = true⌝ → opGrantT s E ρ tok o L₀ σ)) Q ⊢
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
    mvcc.idxCert E.γ.idx F ∗ auth.authPubLbM E.authMode n ∗ ⌜on = true → auth.ctxTokenOf ctx = tok⌝)
  pre q := (match q with
    | .txn cs ts es => txnInModel cs ts es
    | _ => True) ∧ kvDepPreM on d q
  ok q resp _h r := iprop(srvRdCall s E γr c ∗ match q with
    | .put o => iprop(putAppliedOk s E ρ.rd F o (opDepQ d) resp r ∗
        (⌜on = true⌝ → writeGrantOn s E ρ tok (irrPut o)))
    | .deleteRange o => iprop(deleteAppliedOk s E ρ.rd F o (opDepQ d) resp r ∗
        (⌜on = true⌝ → writeGrantOn s E ρ tok (irrDeleteRange o)))
    | .range o => iprop(idCred ρ.ids 1 ∗ srvLeadTimeReader s ∗
        rangeAnsOkM on E γr c F o resp r (rangeDepQM on γr.kv d) ∗
        (⌜on = true⌝ → rangeAuthed s E γr c n tok o))
    | .txn cs ts es => iprop(srvLeadTimeReader s ∗ ∃ t, ⌜txnModelOf cs ts es = some t⌝ ∗
        if txn.txnReadonly t then iprop(idCred ρ.ids 1 ∗
          txnReadAnsM on E γr c F t (rangeDepQM on γr.kv d) resp r ∗
          (⌜on = true⌝ → txnAuthed s E γr c n tok t))
        else iprop(txnAppliedAns E ρ.rd F t (opDepQ d) resp r ∗
          (⌜on = true⌝ → ∃ tw : txn.TxnModelW, ⌜tw.toModel = t⌝ ∗ writeGrantOn s E ρ tok (irrTxn tw)))))
  err q e := iprop(srvRdCall s E γr c ∗ match q with
    | .put o => putErrOk s E ρ F o e
    | .deleteRange o => deleteErrOk s E ρ F o e
    | .range _ => iprop(idCred ρ.ids 1 ∗ srvLeadTimeReader s)
    | .txn cs ts es => iprop(srvLeadTimeReader s ∗ ∃ t, ⌜txnModelOf cs ts es = some t⌝ ∗
        if txn.txnReadonly t then idCred ρ.ids 1 else txnErrOk E ρ F t e))
  revR := mvcc.storeReader E.s E.γ

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
    (hGb : on = true → ∀ hm, Gb hm ⊢ hdrBoundT s E.authMode tok hm)
    (hc : putReqOk o) (hd : kvDepPreM on d (.put o)) :
    kvDepOwnM on s E ρ γr tok d ⊢ putPermitM on ρ.raft ρ.kv Gb o (opDepQ d) := by
  have hd1 := hd.1
  simp only [kvDepPre] at hd1
  obtain ⟨⟨Q, rfl⟩, hl⟩ := hd1
  cases on with
  | false =>
    iintro H
    simp only [putPermitM]
    iapply putPermit_of_dep ρ γr _ o hd.1
    iapply kvDepOwnM_false $$ H
  | true =>
    iintro H
    ihave H := (kvDepOwnM_true s E ρ γr tok _).1 $$ H
    simp only [putPermitM]
    iapply putPermitOn_mono ρ.raft ρ.kv (hdrBoundT s E.authMode tok) Gb o _ (hGb rfl)
    simp only [kvDepOwnOn, kvOpAuOn, opDepQ, opGrantT]
    iunfold putPermitOn
    isplitr
    · ipureintro
      refine ⟨hl, fun hk => ?_⟩
      simp [putReqOk, putCheck, hk] at hc
    iexact H

/-- A delete's permit in the mode `on` (`deletePermitM`) from its deposit (and with auth on its
shape), at a binding `Gb` as `putPermitM_of_dep`'s. -/
theorem deletePermitM_of_dep (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (γr : ReadNames) (tok : Option GoString) (d : KVDep GF) (o : OpFull)
    (Gb : apply.HeaderModel → IProp GF)
    (hGb : on = true → ∀ hm, Gb hm ⊢ hdrBoundT s E.authMode tok hm)
    (hd : kvDepPreM on d (.deleteRange o)) :
    kvDepOwnM on s E ρ γr tok d ⊢ deletePermitM on ρ.raft ρ.kv Gb o (opDepQ d) := by
  have hd1 := hd.1
  simp only [kvDepPre] at hd1
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
    iapply deletePermitOn_mono ρ.raft ρ.kv (hdrBoundT s E.authMode tok) Gb o _ (hGb rfl)
    simp only [kvDepOwnOn, kvOpAuOn, opDepQ, opGrantT]
    iunfold deletePermitOn
    isplitr
    · ipureintro; exact ⟨hz, hd.2 rfl⟩
    iexact H

/-- A writing transaction's permit in the mode `on` (`txnPermitM`) from its deposit, its shape and
(with auth on) the permission cache's shape, at a binding `Gb` as `putPermitM_of_dep`'s. -/
theorem txnPermitM_of_dep (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (tok : Option GoString) (d : KVDep GF) (t : TxnModel) (Gb : apply.HeaderModel → IProp GF)
    (hGb : on = true → ∀ hm, Gb hm ⊢ hdrBoundT s E.authMode tok hm)
    (hd : (∃ Q, d = .op1 (.txn t) Q) ∧ txn.txnPlain t ∧ txnNoZeroEnd t) (hs : txn.txnShape t)
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
    iapply writeGrantG_mono ρ.kv srvAuthSt0 (hdrBoundT s E.authMode tok) Gb _ L₀ σ (hGb h) $$ Hg))
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
  have hd : kvDepPreM E.authOn d (.put o) := Hok.2.2
  simp only [srvKVAnsM]
  icases Hcall with ⟨Hcall, Hrc, Hdep, #HF, -, %Htok⟩
  iunfold srvCall at Hcall
  icases Hcall with ⟨%ci, %cd, %Hci, #Hctx, -, Hcred, Hrd⟩
  subst Hci
  ihave ⟨Hard, Hrc⟩ := srvRdCall_rd s E γr c $$ Hrc
  wp_apply hPut s E ρ ci cd r o (opDepQ d) F $$ [Hrd Hard Hcred Hdep] as %resp %err ⟨Hrd, Hard, Hres⟩
  · iframe #; iframe Hrd Hard Hcred
    -- the gate is `Put.spec`'s, found by unification (off, the permit ignores it)
    iapply putPermitM_of_dep E.authOn s E ρ γr tok d o _ ?hGb Hok.1 hd $$ Hdep
    case hGb => intro h hm; rw [← Htok h]; exact hdrBoundM_tok s E _ hm
  ihave Hrc := Hrc $$ Hard
  iapply HΦ
  iunfold kvAnswer
  icases Hres with (⟨%Herr, %hm, %x, %x', %oc, %skip, %Hst, Hpo, Hhdr, #Hcert, HMint, #Hwit, #Hcok,
    HQv, #Hhb, #Hgate⟩ | ⟨%Hre, #HaE, Hfail⟩)
  · obtain ⟨Hstep, ⟨l, rfl⟩, HFx⟩ := Hst
    subst Herr
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
    ihave ⟨#Hhf2, Hw, Hri⟩ := hdr_of_own _ h (W64 (x.log.length : Int)) (mvcc.storeReader E.s E.γ)
      (w64_rev_ne_zero _ (by omega) Hlen.2) $$ [$Hown]
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
      rw [← Htok hon]
      iapply hdrBoundM_tok $$ Hhb
    iunfold putAppliedOk
    iframe Hrd
    iunfold putApplied
    iexists hm, x, x', l, skip
    iframe Hcert HMint Hwit Hcok HQv
    isplitr
    · ipureintro; exact ⟨Hstep, rfl, HFx, Hlen.1, Hlen.2⟩
    simp only [apply.putOutcomeIs, apply.noSpaceErrIs, Bool.false_eq_true, ↓reduceIte]
    iframe Hresp
  · obtain ⟨rfl, Hne⟩ := Hre
    iright
    isplitr
    · iapply srvErrIs_of_applyErrIs _ Hne $$ HaE
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
  have hd : kvDepPreM E.authOn d (.deleteRange o) := Hok.2.2
  have Hnz0 : o.base.rangeEnd ≠ [W8 0] := by
    have h1 := hd.1; simp only [kvDepPre] at h1; exact h1.2
  simp only [srvKVAnsM]
  icases Hcall with ⟨Hcall, Hrc, Hdep, #HF, -, %Htok⟩
  have HnzW : irrNoZeroEnd (irrDeleteRange o) := by
    refine ⟨?_, ?_, ?_⟩
    · intro _ h; simp [irrDeleteRange, apply.irrEmpty] at h
    · intro o' h; simp only [irrDeleteRange, Option.some.injEq] at h; subst h; exact Hnz0
    · intro _ h; simp [irrDeleteRange, apply.irrEmpty] at h
  iunfold srvCall at Hcall
  icases Hcall with ⟨%ci, %cd, %Hci, #Hctx, -, Hcred, Hrd⟩
  subst Hci
  ihave ⟨Hard, Hrc⟩ := srvRdCall_rd s E γr c $$ Hrc
  wp_apply hDel s E ρ ci cd r o (opDepQ d) F $$ [Hrd Hard Hcred Hdep] as %resp %err ⟨Hrd, Hard, Hres⟩
  · iframe #; iframe Hrd Hard Hcred
    -- the gate is `DeleteRange.spec`'s, as in the put
    iapply deletePermitM_of_dep E.authOn s E ρ γr tok d o _ ?hGb hd $$ Hdep
    case hGb => intro h hm; rw [← Htok h]; exact hdrBoundM_tok s E _ hm
  ihave Hrc := Hrc $$ Hard
  iapply HΦ
  iunfold kvAnswer
  icases Hres with (⟨%Herr, %hm, %rq', %op', %x, %x', %oc, %skip, %Hst, Hpo, Hhdr, #Hcert, HMint, #Hwit,
    #Hcok, HQv, #Hhb, #Hgate⟩ | ⟨%Hre, #HaE, Hfail⟩)
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
    ihave ⟨#Hhf2, Hw, Hri⟩ := hdr_of_own _ h _ (mvcc.storeReader E.s E.γ)
      (writeRev_ne_zero _ _ Hlen.1 Hlen.2) $$ [$Hown]
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
      rw [← Htok hon]
      iapply hdrBoundM_tok $$ Hhb
    iunfold deleteAppliedOk
    iframe Hrd
    iunfold deleteApplied
    iexists hm, rq', op', x, x', l, skip
    iframe Hcert HMint Hwit Hcok HQv
    isplitr
    · ipureintro; exact ⟨Hwire, Hop', Hnz, Hstep, rfl, HFx, Hlen.1, Hlen.2⟩
    simp only [apply.deleteOutcomeIs, apply.noSpaceErrIs, Bool.false_eq_true, ↓reduceIte]
    iframe Hresp
  · obtain ⟨rfl, Hne⟩ := Hre
    iright
    isplitr
    · iapply srvErrIs_of_applyErrIs _ Hne $$ HaE
    simp only
    iframe Hrc
    iunfold deleteErrOk
    iframe Hrd
    iunfold deleteErr
    icases Hfail with (⟨%hm, %rq', %Hw, Herr, -⟩ | Hdep)
    · ileft; iexists hm, rq'; iframe Herr; ipureintro; exact Hw
    · iright; iexact Hdep

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
  icases Hcall with ⟨Hcall, Hrc, Hdep, #HF, #Hn, %Htok⟩
  ihave #Hdep' := kvDep_of_depM E.authOn s E ρ γr tok d $$ Hdep
  iunfold srvCall at Hcall
  icases Hcall with ⟨%ci, %cd, %Hci, #Hctx, #Hct, Hcred, Hlt⟩
  subst Hci
  wp_apply hRange s E ρ γr c ci cd r o none false (rangeDepQM E.authOn γr.kv d) F n Hany $$ [Hrc]
    as %resp %err ⟨Hrc, Hres⟩
  · iframe #; iframe Hrc
    isplitr
    · simp only [traceutil.ownTraceOpt]; itrivial
    ipureintro; exact validSortTarget_of_rangeCheck o Hok.1
  iapply HΦ
  iunfold kvAnswer
  icases Hres with (⟨%Herr, #Hcls, Hok'⟩ | ⟨%Hre, #HaE, -⟩)
  · obtain ⟨rfl, Hrn⟩ := Herr
    iunfold rangeReadOkM at Hok'
    icases Hok' with ⟨%log, #Hcert, #Hcok, %Hlen, Hlin, HQl, #Hres, Hown⟩
    ihave #Hres' := Hres
    icases Hres' with ⟨%crev, Hres'⟩
    iunfold txn.rangeResult at Hres'
    icases Hres' with (⟨-, %ef, -, %He⟩ | ⟨-, #He⟩ | ⟨-, %kvs, %more, #Hresp, -⟩ | ⟨-, %ec, -, %He⟩)
    · cases He
    · ihave %Hne := mvcc.ctxErrorf_ne_nil _ $$ He
      exact absurd rfl Hne
    rotate_left
    · cases He
    iunfold txn.rangeResponseIs at Hresp
    icases Hresp with ⟨-, %h, %sl, %ps, #Hhf, %Hhn, #Hrev, -⟩
    ileft
    isplitr
    · ipureintro; exact ⟨rfl, Hrn⟩
    iexists h, W64 ((log.length : Int) - 1)
    ihave ⟨#Hhf2, Hw, Hri⟩ := hdr_of_own _ h _ (mvcc.storeReader E.s E.γ)
      (w64_last_ne_zero log Hlen.1 Hlen.2.1) $$ [$Hown]
    · iframe #; ipureintro; exact Hhn
    iframe Hhf2 Hw Hri
    simp only
    iframe Hrc Hcred Hlt
    isplitl [Hlin HQl]
    · iunfold rangeAnsOkM
      iexists log
      iframe Hcert Hcok Hres Hlin HQl
      ipureintro; exact ⟨Hlen.1, Hlen.2.1, rfl, Hlen.2.2⟩
    iintro %hon
    iunfold rangeAuthed
    icases Hcls with ⟨%info, %m, %Hm, #Hc, #Hib, #Hf⟩
    iexists info, m
    iframe Hc Hf
    isplitr
    · ipureintro; exact Hm
    rw [hon]
    rw [← Htok hon]; iapply infoBoundM_tok $$ Hib
  · obtain ⟨rfl, Hne⟩ := Hre
    iright
    isplitr
    · iapply srvErrIs_of_applyErrIs _ Hne $$ HaE
    simp only
    iframe Hrc Hcred Hlt

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
  simp only [kvDepPre] at Hro
  icases Hcall with ⟨Hcall, Hrc, Hdep, #HF, #Hn, %Htok⟩
  iunfold srvCall at Hcall
  icases Hcall with ⟨%ci, %cd, %Hci, #Hctx, #Hct, Hcred, Hlt⟩
  subst Hci
  ihave #Hrt := txnReqIs_txnRequestIs r cs ts es ts' es' hts hes $$ Hr
  generalize ht : ({ cmps := cs, thenOps := ts', elseOps := es' } : TxnModel) = t at hm ⊢
  have hg := txnGetsOk_of_check _ _ _ _ _ Hck hm Hin
  have hT := hTxn s E ρ γr c ci cd r t (opDepQ d) (rangeDepQM E.authOn γr.kv d) none false F n
  cases hro : txn.txnReadonly t
  · -- a writing transaction: through raft, as `Put`
    have hdp' : (∃ Q, d = .op1 (.txn t) Q) ∧ txn.txnPlain t ∧ txnNoZeroEnd t ∧
        ReqOp.siblingSafeL ts ∧ ReqOp.siblingSafeL es ∧ txn.OpsNoCut t.thenOps ∧
        txn.OpsNoCut t.elseOps := by
      rcases Hro t hm with ⟨h, -⟩ | h
      · rw [hro] at h; cases h
      · exact h
    obtain ⟨hq, hpl, hz, hsT, hsE, hnT, hnE⟩ := hdp'
    have hsh : txn.txnShape t := by
      subst ht
      exact txnShape_of_check n' cs ts es ts' es' hts hes Hck HivT HivE ⟨hz.2.1, hz.2.2⟩
        ⟨hsT, hsE⟩ hpl ⟨hnT, hnE⟩
    ihave Hdep := txnPermitM_of_dep E.authOn s E ρ γr tok d t
      (hdrBoundM E.authOn s E (GoInterface.ok ci))
      (fun h hm => by rw [h, ← Htok h]; exact hdrBoundM_tok s E _ hm) ⟨hq, hpl, hz⟩ hsh
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
        #Hcok, HQv⟩
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
      ihave ⟨#Hhf2, Hw, Hri⟩ := hdr_of_own _ h _ (mvcc.storeReader E.s E.γ)
        (writeRev_ne_zero _ _ Hlen.1 Hlen.2) $$ [$Hown]
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
        rw [hon, ← Htok hon]
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
      iframe Hout Hcert HMint Hwit Hcok HQv
      try (ipureintro; trivial)
    · obtain ⟨-, Hne⟩ := Hre
      iright
      isplitr
      · iapply srvErrIs_of_applyErrIs _ Hne $$ HaE
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
    wp_apply hT $$ [Hlt Hcred Hrc] as %resp %err ⟨Hlt, Hrc, Hcred, Hres⟩
    · iframe #; iframe Hlt Hcred Hrc
      isplitr
      · simp only [traceutil.ownTraceOpt]; itrivial
      ipureintro
      first
        | exact fun _ => ⟨hg hro, Hany⟩
        | exact ⟨fun _ => ⟨hg hro, Hany⟩, fun h => by cases h⟩
    iapply HΦ
    iunfold kvAnswer
    icases Hres with (⟨%Herr, #Hcls, Hok'⟩ | ⟨%Hne, #HaE⟩)
    · obtain ⟨rfl, Hrn⟩ := Herr
      iunfold txnReadOkM at Hok'
      icases Hok' with ⟨%log, #Hcert, #Hcok, %Hlen, Hlin, HQl, #Hresp, Hown⟩
      ihave #Hresp' := Hresp
      iunfold txn.txnResponseIs at Hresp'
      icases Hresp' with ⟨-, #Hf⟩
      iunfold txn.txnRespFieldsIs at Hf
      icases Hf with ⟨%h, #Hhf, %Hhn, #Hrev, -⟩
      ileft
      isplitr
      · ipureintro; exact ⟨rfl, Hrn⟩
      iexists h, W64 ((log.length : Int) - 1)
      ihave ⟨#Hhf2, Hw, Hri⟩ := hdr_of_own _ h _ (mvcc.storeReader E.s E.γ)
        (w64_last_ne_zero log Hlen.1 Hlen.2.1) $$ [$Hown]
      · iframe #; ipureintro; exact Hhn
      iframe Hhf2 Hw Hri
      simp only
      iframe Hrc Hlt
      iexists t
      isplitr
      · ipureintro; exact hm
      simp only [hro, ↓reduceIte]
      iframe Hcred
      isplitl [Hlin HQl]
      · iunfold txnReadAnsM
        iexists log
        iframe Hcert Hcok Hresp Hlin HQl
        ipureintro; exact ⟨Hlen.1, Hlen.2.1, rfl, Hlen.2.2⟩
      iintro %hon
      iunfold txnAuthed
      icases Hcls with ⟨%info, %m, %Hm, #Hc, #Hib, #Hf⟩
      iexists info, m
      iframe Hc Hf
      isplitr
      · ipureintro; exact Hm
      rw [hon, ← Htok hon]
      iapply infoBoundM_tok $$ Hib
    · iright
      isplitr
      · iapply srvErrIs_of_applyErrIs _ Hne $$ HaE
      simp only
      iframe Hrc Hlt
      iexists t
      isplitr
      · ipureintro; exact hm
      simp only [hro, ↓reduceIte]
      iexact Hcred

/-- **`raftKV`'s getters, from the server's** (`KV().Rev()`: `store.Rev` on the bare store with the
store's reader slots, `revR`; `Cluster().ID()`, `MemberID`, `Term`, `Leader`). -/
theorem kvGetOk_of_serverM (hKV : EtcdServer.KV.spec (GF := GF) (hG := hG))
    (hRev : mvcc.store.Rev.spec (GF := GF) (hG := hG))
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
  have hRev := mvcc.store.Rev.spec_R hRev
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
  icases Hw with ⟨-, -, #Hkvf, #Hkv, #Hrvf, #Hrv, -, -, -, -, -, -, -, #Hterm, -⟩
  ihave %Hkvok := txn.isKV_ok _ E.s E.γ $$ Hkv
  obtain ⟨kty, kvv, Hkveq⟩ := Hkvok
  ihave ⟨#Hko0, #Hst⟩ := txn.isKV_kvOver _ E.s E.γ $$ Hkv
  ihave #Hko : mvcc.kvOver (interface.mkOk kty kvv) E.s $$ []
  · rw [← Hkveq]; iexact Hko0
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
    iintro !> %Φ' Hrd HΦ'
    imod ownToks_0 (GF := GF) E.γ.revs with Hnone
    imod mvcc.idxCert_nil (GF := GF) E.γ.idx with #Hc0
    iapply mvcc.kvOver_rev_wp kty kvv E.s
    iframe Hko
    wp_apply hRev E.s w.rv E.γ 0 [] $$ [Hrd Hnone] as %rv ⟨Hrd, -, -⟩
    · iframe #; iframe Hrd Hnone
    iapply HΦ'
    iexact Hrd
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
    (hRev : mvcc.store.Rev.spec (GF := GF) (hG := hG))
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
  iapply kvGetOk_of_serverM hKV hRev hCl hID hMID hTerm hLead s E ρ γr c F d n tok; iframe #

/-- A handler's answer under parameters `A'` is one under `A` when `A'`'s answers give `A`'s. -/
theorem kvAnswer_mono (A A' : KVAns GF) (hR : A.revR = A'.revR)
    (hok : ∀ q resp h r, A'.ok q resp h r ⊢ A.ok q resp h r)
    (herr : ∀ q e, A'.err q e ⊢ A.err q e) (q : KVReq) (hf resp : Loc) (err : GoInterface) :
    kvAnswer A' q hf resp err ⊢ kvAnswer A q hf resp err := by
  unfold kvAnswer
  rw [hR]
  iintro (⟨%Hok, %h, %r, Hh, Hw, Hrv, Ha⟩ | ⟨He, Ha⟩)
  · ileft
    isplitr
    · ipureintro; exact Hok
    iexists h, r
    iframe Hh Hw Hrv
    iapply hok $$ Ha
  · iright
    iframe He
    iapply herr $$ Ha

/-- **The server's contract is monotone in its parameters** (the auth component's stage 4): `raftKV`
under `A'` is `raftKV` under `A` when `A`'s calls update to `A'`'s, its requests are `A'`'s, `A'`'s
answers give `A`'s, and the revision readers agree. -/
theorem raftKV_mono (s : Loc) (A A' : KVAns GF) (hR : A.revR = A'.revR)
    (hcall : ∀ ctx, A.call ctx ⊢ |==> A'.call ctx) (hpre : ∀ q, A.pre q → A'.pre q)
    (hok : ∀ q resp h r, A'.ok q resp h r ⊢ A.ok q resp h r)
    (herr : ∀ q e, A'.err q e ⊢ A.err q e) :
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
    iapply kvAnswer_mono A A' hR hok herr $$ Hans
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
    iapply kvAnswer_mono A A' hR hok herr $$ Hans
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
    iapply kvAnswer_mono A A' hR hok herr $$ Hans
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
    iapply kvAnswer_mono A A' hR hok herr $$ Hans
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
      ipureintro; exact fun h => by cases h)
    (fun q h => ⟨h.1, h.2, fun h' => by cases h'⟩)
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
    (fun q e => by simp only [srvKVAns, srvKVAnsM]; exact .rfl)

/-- **The on answers from the mode's at auth on** (a bridge; the auth component's stage 5): the
server's contract at `srvKVAnsM true` gives it at `srvKVAnsOn` (through `raftKV_mono`: the gates
opened at `rfl`). -/
theorem raftKV_srvKVAnsM_true (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (c : w64) (F : mvcc.Log) (d : KVDep GF) (na : Nat) (tok : Option GoString) :
    raftKV s (srvKVAnsM true s E ρ γr c F d na tok) ⊢ raftKV s (srvKVAnsOn s E ρ γr c F d na tok) :=
  raftKV_mono s _ _ rfl
    (fun ctx => by
      simp only [srvKVAnsOn, srvKVAnsM]
      iintro ⟨Hc, Hrc, Hdep, #HF, #Hn, %Ht⟩
      imodintro
      iframe Hc Hrc HF Hn
      isplitl [Hdep]
      · iapply (kvDepOwnM_true s E ρ γr tok d).2 $$ Hdep
      ipureintro; exact fun _ => Ht)
    (fun q h => ⟨h.1, kvDepPreM_of_on _ d q h.2⟩)
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
    (fun q e => by simp only [srvKVAnsOn, srvKVAnsM]; exact .rfl)

end proofs

end v3rpc
end EtcdGrove
end Perennial
