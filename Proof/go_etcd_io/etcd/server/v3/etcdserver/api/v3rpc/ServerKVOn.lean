/-
**The server's contract with auth on** (the auth plan's E3zb, 2026-10-28; `ServerKV.lean`'s, in
the auth mode `on`): the parameters `A : KVAns GF` of `raftKV s A` for the server `s` started with
auth on (`srvKVAnsOn s E ρ γr c F d n tok`), and every conjunct of `raftKV` proved from the server's
linked specs with auth on (`EtcdServer.{Put,DeleteRange,Txn}.specOn`, `Range.specOn`,
`Txn.specOnR`): `kvPutOk_of_serverOn`, ..., `raftKV_of_serverOn`.

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
  nothing from it (`examples/authkv`'s `Work` panics only when a refused request succeeds).

Lean-first (no Rocq counterpart).
-/
module

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

/-- A range's result over committed logs under the deposit, at the mode-`on` model's state
(`rangeDepQ`'s; `kvDep`'s form at `kvStM true`). -/
def rangeDepQOn (γk : KVNames) : KVDep GF → List EntryModel → IProp GF
  | .read Q => fun L => iprop(□ Q (kvStM true γk L))
  | _ => fun _ => iprop(True)

/-- **What a request must be with auth on** (`kvDepPre`'s, and of the shape the permission cache
decides: a delete's key and range end, `auth.reqShape`; a writing transaction's every permission,
`kvShapeAll`). -/
def kvDepPreOn (d : KVDep GF) (q : KVReq) : Prop :=
  kvDepPre d q ∧ match q with
  | .deleteRange o => auth.reqShape o.key o.base.rangeEnd
  | .txn cs ts es => ∀ t, txnModelOf cs ts es = some t → txn.txnReadonly t = false →
      ∀ tw : txn.TxnModelW, tw.toModel = t → kvShapeAll (irrTxn tw)
  | _ => True

/-- **A successful `Range` of `o` with auth on** (`rangeAnsOk` at the mode-`on` model). -/
def rangeAnsOkOn (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (F : mvcc.Log) (o : OpFull)
    (resp : Loc) (r : w64) (Q : List EntryModel → IProp GF) : IProp GF :=
  iprop(∃ log : mvcc.Log, mvcc.idxCert E.γ.idx log ∗ mvcc.certOk E.γ log ∗
    ⌜2 ≤ log.length ∧ log.length + 3 ≤ 2 ^ 63 ∧ r = W64 ((log.length : Int) - 1) ∧ F <+: log⌝ ∗
    (if o.base.serializable then iprop(True) else readLogOk γr c log) ∗
    (if o.base.serializable then iprop(True) else
      ∃ L : List EntryModel, srvRLogLb γr.raft L ∗ ⌜kvModelM true γr.kv L = log⌝ ∗ □ Q L) ∗
    txn.rangeResult resp GoInterface.nil log (W64 ((log.length : Int) - 1)) o true)

/-- **A successful read-only `Txn` of `t` with auth on** (`txnReadAns` at the mode-`on` model). -/
def txnReadAnsOn (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (F : mvcc.Log) (t : TxnModel)
    (Q : List EntryModel → IProp GF) (resp : Loc) (r : w64) : IProp GF :=
  iprop(∃ log : mvcc.Log, mvcc.idxCert E.γ.idx log ∗ mvcc.certOk E.γ log ∗
    ⌜2 ≤ log.length ∧ log.length + 3 ≤ 2 ^ 63 ∧ r = W64 ((log.length : Int) - 1) ∧ F <+: log⌝ ∗
    (if txn.txnSerializable t then iprop(True) else readLogOk γr c log) ∗
    (if txn.txnSerializable t then iprop(True) else
      ∃ L : List EntryModel, srvRLogLb γr.raft L ∗ ⌜kvModelM true γr.kv L = log⌝ ∗ □ Q L) ∗
    txn.txnResponseIs false resp (W64 ((log.length : Int) - 1)) t
      (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).1
      (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.2)

/-- **A read's check, as the answer reports it** (persistent): the permissions the check of `o`
saw granted at states recorded at an index `m` at least the caller's bound `n`, and for a
linearizable read no older than the auth state the committed log through the read index `c` left. -/
def rangeAuthed (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (n : Nat) (o : OpFull) : IProp GF :=
  iprop(∃ (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (m : Nat), ⌜n ≤ m⌝ ∗
    apply.rangeClassFrom E.authMode m info o ∗
    (if o.base.serializable then iprop(True) else authFloorAt E.authMode γr c m))

instance rangeAuthed_persistent (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (n : Nat)
    (o : OpFull) : Persistent (rangeAuthed (GF := GF) E γr c n o) := by
  unfold rangeAuthed; split <;> infer_instance

/-- **A read-only transaction's checks, as the answer reports them** (`rangeAuthed`'s). -/
def txnAuthed (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (n : Nat) (t : TxnModel) : IProp GF :=
  iprop(∃ (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (m : Nat), ⌜n ≤ m⌝ ∗
    txnClassFrom E.authMode m info t ∗
    (if txn.txnSerializable t then iprop(True) else authFloorAt E.authMode γr c m))

instance txnAuthed_persistent (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (n : Nat)
    (t : TxnModel) : Persistent (txnAuthed (GF := GF) E γr c n t) := by
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

/-- **The server's parameters of `raftKV` with auth on** (see the file header): `srvKVAns`'s, with
the caller's lower bound `n` of the published auth index. -/
def srvKVAnsOn (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64)
    (F : mvcc.Log) (d : KVDep GF) (n : Nat) (tok : Option GoString) : KVAns GF where
  call ctx := iprop(srvCall s ρ ctx ∗ srvRdCall s E γr c ∗ kvDepOwn ρ γr d ∗
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
        rangeAnsOkOn E γr c F o resp r (rangeDepQOn γr.kv d) ∗ rangeAuthed E γr c n o)
    | .txn cs ts es => iprop(srvLeadTimeReader s ∗ ∃ t, ⌜txnModelOf cs ts es = some t⌝ ∗
        if txn.txnReadonly t then iprop(idCred ρ.ids 1 ∗
          txnReadAnsOn E γr c F t (rangeDepQOn γr.kv d) resp r ∗ txnAuthed E γr c n t)
        else iprop(txnAppliedAns E ρ.rd F t (opDepQ d) resp r ∗
          ∃ tw : txn.TxnModelW, ⌜tw.toModel = t⌝ ∗ writeGrantOn s E ρ tok (irrTxn tw))))
  err q e := iprop(srvRdCall s E γr c ∗ match q with
    | .put o => putErrOk s E ρ F o e
    | .deleteRange o => deleteErrOk s E ρ F o e
    | .range _ => iprop(idCred ρ.ids 1 ∗ srvLeadTimeReader s)
    | .txn cs ts es => iprop(srvLeadTimeReader s ∗ ∃ t, ⌜txnModelOf cs ts es = some t⌝ ∗
        if txn.txnReadonly t then idCred ρ.ids 1 else txnErrOk E ρ F t e))
  revR := mvcc.storeReader E.s E.γ

/-- A deposit is a read deposit at the mode-`on` model's state (`kvDep_of_dep`'s). -/
theorem kvDep_of_depOn (ρ : ReqNames) (γr : ReadNames) (d : KVDep GF) :
    kvDepOwn ρ γr d ⊢ kvDep γr.kv (rangeDepQOn γr.kv d) (kvStM true γr.kv) := by
  iintro H
  iunfold kvDep
  cases d with
  | none => iright; ipureintro; rfl
  | op o Q => iright; ipureintro; rfl
  | op1 o Q => iright; ipureintro; rfl
  | read Q =>
    ileft
    iexists Q
    iunfold kvDepOwn at H
    iframe H
    ipureintro; rfl

/-- A put's permit with auth on (`putPermitOn`) from its deposit and the gRPC check. -/
theorem putPermitOn_of_dep (ρ : ReqNames) (γr : ReadNames) (d : KVDep GF) (o : OpFull)
    (hc : putReqOk o) (hd : kvDepPre d (.put o)) :
    kvDepOwn ρ γr d ⊢ putPermitOn ρ.kv o (opDepQ d) := by
  iintro H
  iunfold putPermitOn
  isplitl [H]
  · iapply putPermit_of_dep ρ γr d o hd $$ H
  ipureintro
  intro hk
  simp [putReqOk, putCheck, hk] at hc

/-- A delete's permit with auth on (`deletePermitOn`) from its deposit and its shape. -/
theorem deletePermitOn_of_dep (ρ : ReqNames) (γr : ReadNames) (d : KVDep GF) (o : OpFull)
    (hd : kvDepPreOn d (.deleteRange o)) :
    kvDepOwn ρ γr d ⊢ deletePermitOn ρ.kv o (opDepQ d) := by
  iintro H
  iunfold deletePermitOn
  isplitl [H]
  · iapply deletePermit_of_dep ρ γr d o hd.1 $$ H
  ipureintro; exact hd.2

/-- A writing transaction's permit with auth on (`txnPermitOn`) from its deposit and its shape. -/
theorem txnPermitOn_of_dep (ρ : ReqNames) (γr : ReadNames) (d : KVDep GF) (t : TxnModel)
    (hd : (∃ Q, d = .op1 (.txn t) Q) ∧ txn.txnPlain t ∧ txnNoZeroEnd t) (hs : txn.txnShape t)
    (hsh : ∀ tw : txn.TxnModelW, tw.toModel = t → kvShapeAll (irrTxn tw)) :
    kvDepOwn ρ γr d ⊢ txnPermitOn ρ.kv t (opDepQ d) := by
  iintro H
  iunfold txnPermitOn
  isplitl [H]
  · iapply txnPermit_of_dep ρ γr d t hd hs $$ H
  ipureintro; exact hsh

end defs

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`raftKV`'s `Put` conjunct with auth on, from `EtcdServer.Put.specOn`**. -/
theorem kvPutOk_of_serverOn (hPut : EtcdServer.Put.specOn (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64) (F : mvcc.Log)
    (d : KVDep GF) (n : Nat) (tok : Option GoString) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReqM true s E ρ ⊢
      kvPutOk s (srvKVAnsOn s E ρ γr c F d n tok) := by
  iintro ⟨#Hpkg, #Hsrv⟩
  iunfold kvPutOk
  iintro %ctx %r %o !> %Φ ⟨Hcall, #Hr, %Hok⟩ HΦ
  have hd : kvDepPre d (.put o) := Hok.2.2.1
  simp only [srvKVAnsOn]
  icases Hcall with ⟨Hcall, Hrc, Hdep, #HF, -, %Htok⟩
  ihave Hpp := putPermitOn_of_dep ρ γr d o Hok.1 hd $$ Hdep
  iunfold srvCall at Hcall
  icases Hcall with ⟨%ci, %cd, %Hci, #Hctx, -, Hcred, Hrd⟩
  subst Hci
  ihave ⟨Hard, Hrc⟩ := srvRdCall_rd s E γr c $$ Hrc
  wp_apply hPut s E ρ ci cd r o (opDepQ d) F $$ [Hrd Hard Hcred Hpp] as %resp %err ⟨Hrd, Hard, Hres⟩
  · iframe #; iframe Hrd Hard Hcred Hpp
  ihave Hrc := Hrc $$ Hard
  iapply HΦ
  iunfold kvAnswer
  icases Hres with (⟨%Herr, %hm, %x, %x', %oc, %skip, %Hst, Hpo, Hhdr, #Hcert, HMint, #Hwit, #Hcok,
    HQv, #Hhb, %L, %Hga, #HpAf⟩ | ⟨%Hre, #HaE, Hfail⟩)
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
    · iunfold writeGrantOn
      iexists hm, L
      iframe HpAf
      isplitr
      · ipureintro; exact Hga
      rw [← Htok]; iapply hdrBoundM_tok $$ Hhb
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

/-- **`raftKV`'s `DeleteRange` conjunct with auth on, from `EtcdServer.DeleteRange.specOn`**. -/
theorem kvDeleteOk_of_serverOn (hDel : EtcdServer.DeleteRange.specOn (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64) (F : mvcc.Log)
    (d : KVDep GF) (n : Nat) (tok : Option GoString) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReqM true s E ρ ⊢
      kvDeleteOk s (srvKVAnsOn s E ρ γr c F d n tok) := by
  iintro ⟨#Hpkg, #Hsrv⟩
  iunfold kvDeleteOk
  iintro %ctx %r %o !> %Φ ⟨Hcall, #Hr, %Hok⟩ HΦ
  have hd : kvDepPreOn d (.deleteRange o) := Hok.2.2
  simp only [srvKVAnsOn]
  icases Hcall with ⟨Hcall, Hrc, Hdep, #HF, -, %Htok⟩
  ihave Hdep := deletePermitOn_of_dep ρ γr d o hd $$ Hdep
  ihave ⟨%Hnz0, Hdep⟩ := deletePermitOn_nz ρ.kv o (opDepQ d) $$ Hdep
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
  · iframe #; iframe Hrd Hard Hcred Hdep
  ihave Hrc := Hrc $$ Hard
  iapply HΦ
  iunfold kvAnswer
  icases Hres with (⟨%Herr, %hm, %rq', %op', %x, %x', %oc, %skip, %Hst, Hpo, Hhdr, #Hcert, HMint, #Hwit,
    #Hcok, HQv, #Hhb, %L, %Hga, #HpAf⟩ | ⟨%Hre, #HaE, Hfail⟩)
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
    · iunfold writeGrantOn
      iexists hm, L
      rw [← Hrq]
      iframe HpAf
      isplitr
      · ipureintro; exact Hga
      rw [← Htok]; iapply hdrBoundM_tok $$ Hhb
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

/-- **`raftKV`'s `Range` conjunct with auth on, from `EtcdServer.Range.specOn`** (in the mode
`on γa`, with the store's range check as the server keeps it, `srvAuthLb`). -/
theorem kvRangeOk_of_serverOn (hRange : EtcdServer.Range.specOn (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64) (F : mvcc.Log)
    (d : KVDep GF) (n : Nat) (tok : Option GoString) (γa : auth.AuthNames) (hγa : E.authMode = .on γa) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReqM true s E ρ ∗ isServerReadM true s E γr ∗ srvAuthLb s E ⊢
      kvRangeOk s (srvKVAnsOn s E ρ γr c F d n tok) := by
  iintro ⟨#Hpkg, #Hsrv, #Hsrd, #Hlb⟩
  iunfold kvRangeOk
  iintro %ctx %r %o !> %Φ ⟨Hcall, #Hr, %Hok⟩ HΦ
  simp only [srvKVAnsOn]
  icases Hcall with ⟨Hcall, Hrc, Hdep, #HF, #Hn, -⟩
  ihave #Hdep' := kvDep_of_depOn ρ γr d $$ Hdep
  iunfold srvCall at Hcall
  icases Hcall with ⟨%ci, %cd, %Hci, #Hctx, #Hct, Hcred, Hlt⟩
  subst Hci
  wp_apply hRange s E ρ γr c ci cd r o none false (rangeDepQOn γr.kv d) F n γa hγa $$ [Hrc]
    as %resp %err ⟨Hrc, Hres⟩
  · iframe #; iframe Hrc
    isplitr
    · simp only [traceutil.ownTraceOpt]; itrivial
    ipureintro; exact validSortTarget_of_rangeCheck o Hok.1
  iapply HΦ
  iunfold kvAnswer
  icases Hres with (⟨%Herr, #Hcls, Hok'⟩ | ⟨%Hre, #HaE⟩)
  · obtain ⟨rfl, Hrn⟩ := Herr
    iunfold rangeReadOkM at Hok'
    icases Hok' with ⟨%log, #Hcert, #Hcok, %Hlen, Hlin, HQl, #Hres, Hown⟩
    ihave #Hres' := Hres
    iunfold txn.rangeResult at Hres'
    icases Hres' with (⟨-, %ef, -, %He⟩ | ⟨-, #He⟩ | ⟨-, %kvs, %more, #Hresp, -⟩)
    · cases He
    · ihave %Hne := mvcc.errorfIs_ne_nil _ $$ He
      exact absurd rfl Hne
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
    · iunfold rangeAnsOkOn
      iexists log
      iframe Hcert Hcok Hres Hlin HQl
      ipureintro; exact ⟨Hlen.1, Hlen.2.1, rfl, Hlen.2.2⟩
    iunfold rangeAuthed
    iexact Hcls
  · obtain ⟨rfl, Hne⟩ := Hre
    iright
    isplitr
    · iapply srvErrIs_of_applyErrIs _ Hne $$ HaE
    simp only
    iframe Hrc Hcred Hlt

/-- **`raftKV`'s `Txn` conjunct with auth on, from `EtcdServer.Txn.specOn`/`specOnR`** (as
`kvTxnOk_of_server`; a writing transaction of the permission cache's shape, `kvDepPreOn`). -/
theorem kvTxnOk_of_serverOn (hTxn : EtcdServer.Txn.specOn (GF := GF) (hG := hG))
    (hTxnR : EtcdServer.Txn.specOnR (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64) (F : mvcc.Log)
    (d : KVDep GF) (n : Nat) (tok : Option GoString) (γa : auth.AuthNames) (hγa : E.authMode = .on γa) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReqM true s E ρ ∗ isServerReadM true s E γr ∗ srvAuthLb s E ⊢
      kvTxnOk s (srvKVAnsOn s E ρ γr c F d n tok) := by
  iintro ⟨#Hpkg, #Hsrv, #Hsrd, #Hlb⟩
  iunfold kvTxnOk
  iintro %ctx %r %cs %ts %es %n' !> %Φ ⟨Hcall, #Hr, %Hok⟩ HΦ
  obtain ⟨Hck, HivT, HivE, Hin, Hro, Hsh⟩ := Hok
  obtain ⟨ts', es', hts, hes, hm⟩ := txnModelOf_of_check Hck
  simp only [srvKVAnsOn] at Hin ⊢
  simp only [kvDepPre] at Hro
  icases Hcall with ⟨Hcall, Hrc, Hdep, #HF, #Hn, %Htok⟩
  iunfold srvCall at Hcall
  icases Hcall with ⟨%ci, %cd, %Hci, #Hctx, #Hct, Hcred, Hlt⟩
  subst Hci
  ihave #Hrt := txnReqIs_txnRequestIs r cs ts es ts' es' hts hes $$ Hr
  generalize ht : ({ cmps := cs, thenOps := ts', elseOps := es' } : TxnModel) = t at hm ⊢
  have hg := txnGetsOk_of_check _ _ _ _ _ Hck hm Hin
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
    ihave Hdep := txnPermitOn_of_dep ρ γr d t ⟨hq, hpl, hz⟩ hsh (Hsh t hm hro) $$ Hdep
    iunfold isServerReadM at Hsrd
    icases Hsrd with ⟨%w, #Hw⟩
    iunfold srvReadFieldsAtM at Hw
    icases Hw with ⟨-, -, -, -, -, -, -, -, -, -, #Hlga, %Hlgn, -⟩
    iunfold srvRdCall at Hrc
    icases Hrc with ⟨Hsr, Hlgr, Hca, Hrr, Hard⟩
    wp_apply hTxn s E ρ ci cd r t (opDepQ d) none false F w.lg $$ [Hlt Hard Hcred Hlgr Hdep]
      as %resp %err ⟨Hlt, Hard, Hlgr, Hres⟩
    · iframe #; iframe Hlt Hard Hcred Hlgr Hdep
      isplitr
      · ipureintro; exact Hlgn
      isplitr
      · simp only [traceutil.ownTraceOpt]; itrivial
      ipureintro; exact hro
    ihave Hrc : srvRdCall s E γr c $$ [Hsr Hlgr Hca Hrr Hard]
    · iunfold srvRdCall; iframe
    iapply HΦ
    iunfold kvAnswer
    icases Hres with (⟨%Herr, Hok', %tw2, %hm2, %L2, %Hg2, #Hhb2, #HpAf2⟩ | ⟨%Hre, #HaE, Hfail⟩)
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
      · iexists tw2
        isplitr
        · ipureintro; exact Hg2.1
        iunfold writeGrantOn
        iexists hm2, L2
        iframe HpAf2
        isplitr
        · ipureintro; exact Hg2.2
        rw [← Htok]; iapply hdrBoundM_tok $$ Hhb2
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
      iapply txnErrOk_of_on $$ Hfail
  · -- a read-only transaction: read locally
    ihave #Hdep' := kvDep_of_depOn ρ γr d $$ Hdep
    wp_apply hTxnR s E ρ γr c ci cd r t (rangeDepQOn γr.kv d) none false F n γa hγa
      $$ [Hlt Hcred Hrc] as %resp %err ⟨Hlt, Hrc, Hcred, Hres⟩
    · iframe #; iframe Hlt Hcred Hrc
      isplitr
      · simp only [traceutil.ownTraceOpt]; itrivial
      ipureintro; exact ⟨hro, hg hro⟩
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
      · iunfold txnReadAnsOn
        iexists log
        iframe Hcert Hcok Hresp Hlin HQl
        ipureintro; exact ⟨Hlen.1, Hlen.2.1, rfl, Hlen.2.2⟩
      iunfold txnAuthed
      iexact Hcls
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

/-- **`raftKV`'s getters with auth on, from the server's** (as `kvGetOk_of_server`) (`KV().Rev()`: `store.Rev` on the bare store with
the store's reader slots, `revR`; `Cluster().ID()`, `MemberID`, `Term`, `Leader`). -/
theorem kvGetOk_of_serverOn (hKV : EtcdServer.KV.spec (GF := GF) (hG := hG))
    (hRev : mvcc.store.Rev.spec (GF := GF) (hG := hG))
    (hCl : EtcdServer.Cluster.spec (GF := GF) (hG := hG))
    (hID : membership.RaftCluster.ID.spec (GF := GF) (hG := hG))
    (hMID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (hTerm : EtcdServer.Term.spec (GF := GF) (hG := hG))
    (hLead : EtcdServer.Leader.spec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64) (F : mvcc.Log)
    (d : KVDep GF) (n : Nat) (tok : Option GoString) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReqM true s E ρ ∗ isServerReadM true s E γr ⊢
      kvGetOk s (srvKVAnsOn s E ρ γr c F d n tok) := by
  have hRev := mvcc.store.Rev.spec_frozen hRev
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
  simp only [srvKVAnsOn]
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

/-- **The server's contract `raftKV` with auth on, from the server's linked specs** (no premise
but the server's facts with auth on, `isServerReqM true`, `isServerReadM true`, `srvAuthLb`, in
the mode `on γa`), at the parameters `srvKVAnsOn s E ρ γr c F d n tok`. -/
theorem raftKV_of_serverOn (hPut : EtcdServer.Put.specOn (GF := GF) (hG := hG))
    (hDel : EtcdServer.DeleteRange.specOn (GF := GF) (hG := hG))
    (hRange : EtcdServer.Range.specOn (GF := GF) (hG := hG))
    (hTxn : EtcdServer.Txn.specOn (GF := GF) (hG := hG))
    (hTxnR : EtcdServer.Txn.specOnR (GF := GF) (hG := hG))
    (hKV : EtcdServer.KV.spec (GF := GF) (hG := hG))
    (hRev : mvcc.store.Rev.spec (GF := GF) (hG := hG))
    (hCl : EtcdServer.Cluster.spec (GF := GF) (hG := hG))
    (hID : membership.RaftCluster.ID.spec (GF := GF) (hG := hG))
    (hMID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (hTerm : EtcdServer.Term.spec (GF := GF) (hG := hG))
    (hLead : EtcdServer.Leader.spec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64) (F : mvcc.Log)
    (d : KVDep GF) (n : Nat) (tok : Option GoString) (γa : auth.AuthNames) (hγa : E.authMode = .on γa) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReqM true s E ρ ∗ isServerReadM true s E γr ∗ srvAuthLb s E ⊢
      raftKV s (srvKVAnsOn s E ρ γr c F d n tok) := by
  iintro ⟨#Hpkg, #Hsrv, #Hsrd, #Hlb⟩
  iunfold raftKV
  isplitr
  · iapply kvRangeOk_of_serverOn hRange s E ρ γr c F d n tok γa hγa; iframe #
  isplitr
  · iapply kvPutOk_of_serverOn hPut s E ρ γr c F d n tok; iframe #
  isplitr
  · iapply kvDeleteOk_of_serverOn hDel s E ρ γr c F d n tok; iframe #
  isplitr
  · iapply kvTxnOk_of_serverOn hTxn hTxnR s E ρ γr c F d n tok γa hγa; iframe #
  iapply kvGetOk_of_serverOn hKV hRev hCl hID hMID hTerm hLead s E ρ γr c F d n tok; iframe #

end proofs

end v3rpc
end EtcdGrove
end Perennial
