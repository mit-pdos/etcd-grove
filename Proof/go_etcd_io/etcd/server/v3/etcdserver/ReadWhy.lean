/-
**Why a read on the serializable path was refused** (auth-guard-completeness G4, 2026-11-14;
`notes/auth-guard-scope.md`, §2.5). Lean-first (no Rocq counterpart).

`Range` and a read-only `Txn` check the request through `doSerialize` (`v3_server.go:1035-1057`): the
request side (`AuthInfoFromCtx`), the permission check `chk` of the auth info it gave (`AuthInfo{}`
when none), the read, then the revision re-check. `doSerialize`'s spec names why it refused
(`serialWhy`); here is what `Range`'s and `Txn`'s specs state of it, in their own terms:

* `rangeWhy`: the request side's reasons, or one permission check of the range `[key, e)` (`e` the
  range end the check saw, `apply.authEndOf`) refused (`permWhy`), or the revision re-check
  (`oldRevWhy`);
* `txnWhy`: likewise, the refused check being one a read-only transaction makes (`apply.txnMay`: a
  comparison's read or a get's).

A failed read's error is such a refusal or an error of the read itself: the read index's
(`readErrIs`) or the txn package's read (mvcc's `ErrFutureRev` and `ErrCompacted`, a done context's
`rangeKeys` error; a transaction's `checkTxn` errors). The specs state it as that disjunction
(`rangeWhyOut`, `txnWhyOut`), not as "an auth error variable has a reason": telling the read's own
errors apart from the auth package's variables needs their message cells, and a wrapped context
error's (`mvcc.ctxErrorf`, `fmt.Errorf` with `%w`) is opaque in Perennial's model (`Spec/fmt/ErrorfWrap.lean`:
no fact from the model). In the modes `off` and `any` the reasons are `True` (as `permWhy`'s).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthWhy
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReadOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthCheckTxnLb

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **Why a range read `o` was refused** on the server `s` (persistent): with auth on, the request
side's reasons, or the read check of `[o.key, e)` (`e` the range end the check saw) refusing the auth
info the request side gave (`permWhy`), or `doSerialize`'s revision re-check (`oldRevWhy`); `True` in
the modes `off` and `any`. -/
def rangeWhy (s : Loc) (M : auth.AuthMode) (n : Nat) (ctx : GoInterface) (o : OpFull)
    (err : GoInterface) : IProp GF :=
  match M with
  | .on γa => iprop(reqSideWhy M n ctx err ∨
      (∃ (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (e : GoString),
        ⌜apply.authEndOf o.base.rangeEnd e⌝ ∗ permWhy s M n ctx err info o.key e .read) ∨
      oldRevWhy s γa n ctx err)
  | _ => iprop(True)

instance rangeWhy_persistent (s : Loc) (M : auth.AuthMode) (n : Nat) (ctx : GoInterface)
    (o : OpFull) (err : GoInterface) : Persistent (rangeWhy (GF := GF) s M n ctx o err) := by
  unfold rangeWhy; cases M <;> infer_instance

/-- **A failed `Range`'s error, with why if refused** (persistent): a refusal with its reason
(`rangeWhy`), the read index's error (`readErrIs`), or the read's own (mvcc's `ErrFutureRev` or
`ErrCompacted`, or `rangeKeys`' error for a done context). -/
def rangeWhyOut (s : Loc) (M : auth.AuthMode) (n : Nat) (ctx : GoInterface) (o : OpFull)
    (err : GoInterface) : IProp GF :=
  iprop(rangeWhy s M n ctx o err ∨ readErrIs err ∨
    (∃ ef : GoInterfaceOk,
      (globalAddr go_etcd_io.etcd.server.v3.storage.mvcc.ErrFutureRev ↦□ GoInterface.ok ef : IProp GF) ∗
      ⌜err = GoInterface.ok ef⌝) ∨
    (∃ ec : GoInterfaceOk,
      (globalAddr go_etcd_io.etcd.server.v3.storage.mvcc.ErrCompacted ↦□ GoInterface.ok ec : IProp GF) ∗
      ⌜err = GoInterface.ok ec⌝) ∨
    mvcc.rangeKeysErr err)

instance rangeWhyOut_persistent (s : Loc) (M : auth.AuthMode) (n : Nat) (ctx : GoInterface)
    (o : OpFull) (err : GoInterface) : Persistent (rangeWhyOut (GF := GF) s M n ctx o err) := by
  unfold rangeWhyOut; infer_instance

/-- **Why a read-only transaction `t` was refused** on the server `s` (persistent): with auth on, the
request side's reasons, or one of its reads' checks (`apply.txnMay`, of a wire transaction `tw`
describing `t`: `IsRangePermitted` of a comparison's or a get's range) refusing the auth info the
request side gave (`permWhy`), or `doSerialize`'s revision
re-check (`oldRevWhy`); `True` in the modes `off` and `any`. -/
def txnWhy (s : Loc) (M : auth.AuthMode) (n : Nat) (ctx : GoInterface) (t : TxnModel)
    (err : GoInterface) : IProp GF :=
  match M with
  | .on γa => iprop(reqSideWhy M n ctx err ∨
      (∃ (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (tw : txn.TxnModelW) (x : apply.Perm3),
        ⌜tw.toModel = t ∧ apply.txnMay tw x⌝ ∗ permWhy s M n ctx err info x.1 x.2.1 .read) ∨
      oldRevWhy s γa n ctx err)
  | _ => iprop(True)

instance txnWhy_persistent (s : Loc) (M : auth.AuthMode) (n : Nat) (ctx : GoInterface)
    (t : TxnModel) (err : GoInterface) : Persistent (txnWhy (GF := GF) s M n ctx t err) := by
  unfold txnWhy; cases M <;> infer_instance

/-- **A failed read-only `Txn`'s error, with why if refused** (persistent): a refusal with its reason
(`txnWhy`), the read index's error (`readErrIs`), or the read's own (`checkTxn`'s, `txn.checkErrIs`, or
a done context's, `mvcc.ctxErrorf`). -/
def txnWhyOut (s : Loc) (M : auth.AuthMode) (n : Nat) (ctx : GoInterface) (t : TxnModel)
    (err : GoInterface) : IProp GF :=
  iprop(txnWhy s M n ctx t err ∨ readErrIs err ∨ txn.checkErrIs err ∨ mvcc.ctxErrorf err)

instance txnWhyOut_persistent (s : Loc) (M : auth.AuthMode) (n : Nat) (ctx : GoInterface)
    (t : TxnModel) (err : GoInterface) : Persistent (txnWhyOut (GF := GF) s M n ctx t err) := by
  unfold txnWhyOut; infer_instance

/-! ### From `doSerialize`'s reason -/

/-- `doSerialize`'s reason, its check the store's range check of `[o.key, e)` at a bound `n' ≥ n`
(`permRefusalM`), is `rangeWhy` at `n`. -/
theorem rangeWhy_of_serialWhy (s : Loc) (M : auth.AuthMode) (n n' : Nat) (h : n ≤ n')
    (ctx : GoInterface) (o : OpFull) (e : GoString) (he : apply.authEndOf o.base.rangeEnd e)
    (err : GoInterface) (herr : err ≠ GoInterface.nil) :
    serialWhy (GF := GF) s M n ctx err
        (fun info err => auth.permRefusalM M n' info o.key e .read err) ⊢
      rangeWhy s M n ctx o err := by
  cases M with
  | on γa =>
    unfold serialWhy rangeWhy
    iintro (#Hr | ⟨%info, #Hi, #HR⟩ | #Ho)
    · ileft; iexact Hr
    · iright; ileft
      iexists info, e
      isplitr
      · ipureintro; exact he
      · iapply (permWhy_of_infoWhy s γa n n' h ctx err info o.key e .read herr) $$ Hi HR
    · iright; iright; iexact Ho
  | _ => unfold rangeWhy; iintro -; itrivial

/-- `doSerialize`'s reason, its check `CheckTxnAuth` of the wire transaction `tw` (one of its range
checks refused at a bound `n' ≥ n`, `permRefusalM`), is `txnWhy` at `n`. -/
theorem txnWhy_of_serialWhy (s : Loc) (M : auth.AuthMode) (γa : auth.AuthNames) (hM : M = .on γa)
    (n n' : Nat) (h : n ≤ n') (ctx : GoInterface) (t : TxnModel) (tw : txn.TxnModelW)
    (htw : tw.toModel = t) (err : GoInterface) (herr : err ≠ GoInterface.nil) :
    serialWhy (GF := GF) s M n ctx err (fun info err => iprop(∃ x : apply.Perm3,
        ⌜apply.txnMay tw x⌝ ∗ auth.permRefusalM (.on γa) n' info x.1 x.2.1 .read err)) ⊢
      txnWhy s M n ctx t err := by
  subst hM
  unfold serialWhy txnWhy
  iintro (#Hr | ⟨%info, #Hi, %x, %hx, #HR⟩ | #Ho)
  · ileft; iexact Hr
  · iright; ileft
    iexists info, tw, x
    isplitr
    · ipureintro; exact ⟨htw, hx⟩
    · iapply (permWhy_of_infoWhy s γa n n' h ctx err info x.1 x.2.1 .read herr) $$ Hi HR
  · iright; iright; iexact Ho

/-- The reasons are about the context's token only: a context with the same incoming metadata
(`EnsureTrace`'s and the tracer's derived contexts) has the same ones. -/
theorem rangeWhy_ctx (s : Loc) (M : auth.AuthMode) (n : Nat) (c c' : GoInterface) (o : OpFull)
    (err : GoInterface) (h : metadata.incomingOf c = metadata.incomingOf c') :
    rangeWhy (GF := GF) s M n c o err ⊢ rangeWhy s M n c' o err := by
  have ht : auth.ctxTokenOf c = auth.ctxTokenOf c' := by unfold auth.ctxTokenOf; rw [h]
  cases M with
  | on γa =>
    unfold rangeWhy permWhy oldRevWhy reqSideWhy principalBound auth.noPrincipalFrom
      auth.tokRefusedFrom
    rw [ht]
  | _ => unfold rangeWhy; iintro -; itrivial

theorem txnWhy_ctx (s : Loc) (M : auth.AuthMode) (n : Nat) (c c' : GoInterface) (t : TxnModel)
    (err : GoInterface) (h : metadata.incomingOf c = metadata.incomingOf c') :
    txnWhy (GF := GF) s M n c t err ⊢ txnWhy s M n c' t err := by
  have ht : auth.ctxTokenOf c = auth.ctxTokenOf c' := by unfold auth.ctxTokenOf; rw [h]
  cases M with
  | on γa =>
    unfold txnWhy permWhy oldRevWhy reqSideWhy principalBound auth.noPrincipalFrom
      auth.tokRefusedFrom
    rw [ht]
  | _ => unfold txnWhy; iintro -; itrivial

theorem rangeWhyOut_off (s : Loc) (M : auth.AuthMode) (n : Nat) (ctx : GoInterface) (o : OpFull)
    (err : GoInterface) (h : M.isOn = false) : ⊢ rangeWhyOut (GF := GF) s M n ctx o err := by
  unfold rangeWhyOut
  ileft
  cases M with
  | on γa => cases h
  | _ => unfold rangeWhy; itrivial

theorem txnWhyOut_off (s : Loc) (M : auth.AuthMode) (n : Nat) (ctx : GoInterface) (t : TxnModel)
    (err : GoInterface) (h : M.isOn = false) : ⊢ txnWhyOut (GF := GF) s M n ctx t err := by
  unfold txnWhyOut
  ileft
  cases M with
  | on γa => cases h
  | _ => unfold txnWhy; itrivial

theorem rangeWhyOut_read (s : Loc) (M : auth.AuthMode) (n : Nat) (ctx : GoInterface) (o : OpFull)
    (err : GoInterface) : readErrIs (GF := GF) err ⊢ rangeWhyOut s M n ctx o err := by
  unfold rangeWhyOut; iintro #H; iright; ileft; iexact H

theorem txnWhyOut_read (s : Loc) (M : auth.AuthMode) (n : Nat) (ctx : GoInterface) (t : TxnModel)
    (err : GoInterface) : readErrIs (GF := GF) err ⊢ txnWhyOut s M n ctx t err := by
  unfold txnWhyOut; iintro #H; iright; ileft; iexact H

/-- The txn package's range read failed: mvcc's errors or `rangeKeys`' (`txn.rangeResult`). -/
theorem rangeWhyOut_of_result (s : Loc) (M : auth.AuthMode) (n : Nat) (ctx : GoInterface)
    (o : OpFull) (resp : Loc) (ei : GoInterfaceOk) (log : mvcc.Log) (rev : w64) (crev : Int) :
    txn.rangeResult (GF := GF) resp (GoInterface.ok ei) log rev crev o true ⊢
      rangeWhyOut s M n ctx o (GoInterface.ok ei) := by
  iunfold txn.rangeResult
  iintro (⟨%H, %ef, #Hef, %He⟩ | ⟨%H, #He⟩ | ⟨%H, -⟩ | ⟨%H, %ec, #Hec, %He⟩)
  · unfold rangeWhyOut; iright; iright; ileft; iexists ef; iframe Hef; ipureintro; exact He
  · unfold rangeWhyOut; iright; iright; iright; iright; iexact He
  · cases H.2.1
  · unfold rangeWhyOut; iright; iright; iright; ileft; iexists ec; iframe Hec; ipureintro; exact He

end defs

end EtcdGrove
end Perennial
