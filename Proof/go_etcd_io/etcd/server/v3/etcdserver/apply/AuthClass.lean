/-
**The keys a request's authorization must cover, and the class statement** (`notes/auth-plan.md`,
A1; `notes/auth-matrix.md`; 2026-10-23). Lean-first (no Rocq counterpart).

A permission check's verdict (`auth.permVerdict`, A0) says of one call: if it passed, some recorded
state of the auth store permitted the key or range. This file states what a *request* requires
(`notes/auth-matrix.md`'s "keys" column) and what the checks of the apply layer and the API layer
establish when they pass, in every mode (`auth.AuthMode`): nothing in `off` and `any`, the class
in `on γa`.

- `classRes M info perms`: in the mode `on γa`, each `(key, rangeEnd, op)` of `perms` is permitted to
  the principal `info` at some recorded state (`classOk`); otherwise `True`.
- The range end **as the check sees it** (`authEndOf`): the checks take the request's `RangeEnd`
  bytes, the model (`rangeEndOf`, `txn/Requests.lean`) reads a non-`nil` empty `RangeEnd` as
  open-ended (as mvcc does), while `isOpPermitted` reads any empty one as a point. The two agree
  except for a non-`nil` empty `RangeEnd`, which no wire request produces (protobuf-go decodes a
  present empty `bytes` field as `nil`; checked with a probe, 2026-10-23) but an in-process caller
  could build; so a range's class is stated for some end `e` with `authEndOf o.base.rangeEnd e`:
  the model's end, or empty when the model's is open-ended.
- A put: the write of its key (a point: `IsPutPermitted(key)`), and with `PrevKv` the read of
  the key (`IsRangePermitted(key, nil)`: a point). **Not stated**: the keys of the put's lease
  (`checkLeasePuts`: admin, or `IsPutPermitted` of each key `Keys()` returns), because the
  lessor's contract (`isApplyLessor`, names-only) does not relate `Keys()` to any model, so a
  statement over them would be vacuous; the leases unit (T3) is where they get a model.
- A delete range: the write of the range, and with `PrevKv` its read. A range: its read. A
  transaction (`txnClass`): the read of each comparison's range, then both branches' operations,
  nested transactions recursively (`opClass`/`opsClass`, as `checkTxnReqsPermission` walks them).
  A nested put's `PrevKv` read and lease keys are checked by the code (`checkPutAuth`) but not
  stated: `TxnOp` carries neither (`putTxnOp`).

The method-level statement (the auth applier's `Put` etc. for the principal `Apply` set from the
request's header) needs the principal threaded through `chainRes`'s auth case; it is not here
(A1 covers the checks, which take the principal as a parameter), see `notes/decisions.md`, "A1".
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Contracts
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Requests

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apply

open Iris Iris.BI Iris.ProofMode

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- A required permission: a key, a range end (`[]`: the key alone) and the operation's type. -/
abbrev Perm3 := GoString × GoString × auth.PermType

/-- **Every permission of `perms` is granted to `info`** at some recorded state of the history
`γa` (persistent). -/
def classOk (γa : auth.AuthNames) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (perms : List Perm3) : IProp GF :=
  iprop([∗list] x ∈ perms, ∃ (i : Nat) (st : auth.AuthState), auth.authStateAt γa i st ∗
    ⌜auth.permitted st (auth.authInfoM info) x.1 x.2.1 x.2.2⌝)

instance classOk_persistent (γa : auth.AuthNames) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (perms : List Perm3) : Persistent (classOk (GF := GF) γa info perms) := by
  unfold classOk; infer_instance

/-- **The class result in the mode `M`**: `classOk` in `on γa`, nothing otherwise. -/
def classRes (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (perms : List Perm3) : IProp GF :=
  match M with
  | .on γa => classOk γa info perms
  | _ => iprop(True)

instance classRes_persistent (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (perms : List Perm3) : Persistent (classRes (GF := GF) M info perms) := by
  unfold classRes; cases M <;> infer_instance

theorem classRes_nil (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) :
    ⊢ classRes (GF := GF) M info [] := by
  cases M
  · unfold classRes; itrivial
  · unfold classRes; itrivial
  · unfold classRes classOk
    iapply BigSepL.bigSepL_nil.2
    iempintro

theorem classRes_app (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (l1 l2 : List Perm3) :
    classRes (GF := GF) M info l1 ∗ classRes M info l2 ⊢ classRes M info (l1 ++ l2) := by
  cases M
  · unfold classRes; iintro -; itrivial
  · unfold classRes; iintro -; itrivial
  · unfold classRes classOk
    iintro ⟨H1, H2⟩
    iapply BigSepL.bigSepL_append.2
    iframe H1 H2

theorem classRes_cons (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (x : Perm3) (l : List Perm3) :
    classRes (GF := GF) M info [x] ∗ classRes M info l ⊢ classRes M info (x :: l) := by
  exact classRes_app M info [x] l

theorem classRes_cons_left (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (x : Perm3) (l : List Perm3) :
    classRes (GF := GF) M info (x :: l) ⊢ classRes M info [x] := by
  cases M
  · unfold classRes; iintro -; itrivial
  · unfold classRes; iintro -; itrivial
  · unfold classRes classOk
    iintro H
    ihave ⟨H1, -⟩ := BigSepL.bigSepL_cons.1 $$ H
    iapply BigSepL.bigSepL_singleton.2
    iexact H1

/-- A passed check's verdict gives the class of its one permission. -/
theorem classRes_of_permVerdict (M : auth.AuthMode)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (k e : GoString) (op : auth.PermType) :
    auth.permVerdict (GF := GF) M info k e op GoInterface.nil ⊢ classRes M info [(k, e, op)] := by
  cases M
  · unfold classRes; iintro -; itrivial
  · unfold classRes; iintro -; itrivial
  · unfold auth.permVerdict classRes classOk
    iintro ⟨⟨%i, %st, #Hst, %Hp⟩, -⟩
    iapply BigSepL.bigSepL_singleton.2
    iexists i, st
    iframe #
    ipureintro
    exact Hp rfl

/-- The range end a check saw, given the model's (see the file header): the model's end, or empty
when the model's is open-ended (a non-`nil` empty `RangeEnd`). -/
def authEndOf (modelEnd e : GoString) : Prop :=
  e = modelEnd ∨ (e = [] ∧ modelEnd = [W8 0])

/-- The check sees the request's `RangeEnd` contents `e`, the model `rangeEndOf esl e`; a `nil`
slice has no contents. -/
theorem authEndOf_rangeEndOf (esl : GoSlice) (e : GoString) (hl : e.length = sint.nat esl.len) :
    authEndOf (txn.rangeEndOf esl e) e := by
  unfold authEndOf txn.rangeEndOf
  by_cases h1 : esl = slice.nil
  · subst h1
    simp only [↓reduceIte]
    left
    have : e.length = 0 := by rw [hl]; rfl
    exact List.length_eq_zero_iff.1 this
  · simp only [h1, ↓reduceIte]
    by_cases h2 : e = []
    · subst h2; simp
    · simp [h2]

/-- The read of a range or get `o` (`IsRangePermitted(key, rangeEnd)`). -/
def rangeClass (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (o : OpFull) : IProp GF :=
  iprop(∃ e : GoString, ⌜authEndOf o.base.rangeEnd e⌝ ∗ classRes M info [(o.key, e, .read)])

/-- The write of a delete `o`'s range, and with `PrevKv` its read. -/
def deleteClass (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (o : OpFull) : IProp GF :=
  iprop(∃ e : GoString, ⌜authEndOf o.base.rangeEnd e⌝ ∗
    classRes M info ((o.key, e, .write) :: if o.base.prevKV then [(o.key, e, .read)] else []))

/-- The permissions a put `o` needs: the write of its key, and with `PrevKv` its read. -/
def putPerms (o : OpFull) : List Perm3 :=
  (o.key, [], .write) :: if o.base.prevKV then [(o.key, [], .read)] else []

/-- The class of a put `o` (`checkPutAuth`; the lease's keys are not stated, see the header). -/
def putClass (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (o : OpFull) :
    IProp GF :=
  classRes M info (putPerms o)

/-- The reads of a transaction's comparisons. -/
def cmpsClass (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (cs : List CmpModel) : IProp GF :=
  iprop([∗list] cm ∈ cs, ∃ e : GoString, ⌜authEndOf cm.rangeEnd e⌝ ∗
    classRes M info [(cm.key, e, .read)])

mutual
/-- **The class of a transaction's operation** (`checkTxnReqsPermission`'s walk): a get's read, a
put's write of its key (its `PrevKv` read and lease keys are not in `TxnOp`), a delete's write and
`PrevKv` read, a nested transaction's comparisons and both branches. -/
def opClass (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) :
    TxnOp → IProp GF
  | .get o => rangeClass M info o
  | .put k _ _ => classRes M info [(k, [], .write)]
  | .putKeep k _ => classRes M info [(k, [], .write)]
  | .putIgnVal k _ => classRes M info [(k, [], .write)]
  | .delete o => deleteClass M info o
  | .txn cs ts es => iprop(□ (cmpsClass M info cs ∗ opsClass M info ts ∗ opsClass M info es))

/-- The class of a list of operations, in order. -/
def opsClass (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) :
    List TxnOp → IProp GF
  | [] => iprop(True)
  | op :: ops => iprop(opClass M info op ∗ opsClass M info ops)
end

/-- **The class of a transaction** `t` (`checkTxnPermission`). -/
def txnClass (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (t : TxnModel) :
    IProp GF :=
  iprop(cmpsClass M info t.cmps ∗ opsClass M info t.thenOps ∗ opsClass M info t.elseOps)

instance rangeClass_persistent (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (o : OpFull) : Persistent (rangeClass (GF := GF) M info o) := by
  unfold rangeClass; infer_instance

instance deleteClass_persistent (M : auth.AuthMode)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (o : OpFull) :
    Persistent (deleteClass (GF := GF) M info o) := by
  unfold deleteClass; infer_instance

instance putClass_persistent (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (o : OpFull) : Persistent (putClass (GF := GF) M info o) := by
  unfold putClass; infer_instance

instance cmpsClass_persistent (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (cs : List CmpModel) : Persistent (cmpsClass (GF := GF) M info cs) := by
  unfold cmpsClass; infer_instance

instance opClass_persistent (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (op : TxnOp) : Persistent (opClass (GF := GF) M info op) := by
  cases op <;> unfold opClass <;> infer_instance

instance opsClass_persistent (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (ops : List TxnOp) : Persistent (opsClass (GF := GF) M info ops) := by
  induction ops with
  | nil => unfold opsClass; infer_instance
  | cons op ops ih => unfold opsClass; infer_instance

instance txnClass_persistent (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (t : TxnModel) : Persistent (txnClass (GF := GF) M info t) := by
  unfold txnClass; infer_instance

theorem opClass_get (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (o : OpFull) : rangeClass (GF := GF) M info o ⊢ opClass M info (.get o) := by
  unfold opClass; iintro H; iexact H

theorem opClass_delete (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (o : OpFull) : deleteClass (GF := GF) M info o ⊢ opClass M info (.delete o) := by
  unfold opClass; iintro H; iexact H

theorem opClass_txn (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (cs : List CmpModel) (ts es : List TxnOp) :
    txnClass (GF := GF) M info ⟨cs, ts, es⟩ ⊢ opClass M info (.txn cs ts es) := by
  unfold txnClass opClass
  iintro #H
  imodintro
  iexact H

/-- A put's class gives its operation's (`putTxnOp`: the key's write, whichever variant). -/
theorem opClass_put_of_putClass (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (o : OpFull) : putClass (GF := GF) M info o ⊢ opClass M info (txn.putTxnOp o) := by
  unfold putClass putPerms txn.putTxnOp
  by_cases h1 : o.ignoreValue = true <;> by_cases h2 : o.ignoreLease = true <;>
    simp only [h1, h2, Bool.false_eq_true, ↓reduceIte] <;> unfold opClass <;>
    exact classRes_cons_left M info _ _

theorem opsClass_nil_eq (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) :
    opsClass (GF := GF) M info [] = iprop(True) := by
  unfold opsClass; rfl

theorem opsClass_cons (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (op : TxnOp) (ops : List TxnOp) :
    opsClass (GF := GF) M info (op :: ops) = iprop(opClass M info op ∗ opsClass M info ops) := by
  conv => lhs; unfold opsClass

theorem opsClass_nil (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) :
    ⊢ opsClass (GF := GF) M info [] := by
  rw [opsClass_nil_eq]; itrivial

theorem opsClass_app (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (l1 l2 : List TxnOp) :
    opsClass (GF := GF) M info l1 ∗ opsClass M info l2 ⊢ opsClass M info (l1 ++ l2) := by
  induction l1 with
  | nil => simp only [List.nil_append]; rw [opsClass_nil_eq]; iintro ⟨-, H⟩; iexact H
  | cons op ops ih =>
    simp only [List.cons_append]
    rw [opsClass_cons, opsClass_cons]
    iintro ⟨⟨H1, H2⟩, H3⟩
    iframe H1
    iapply ih
    iframe H2 H3

/-- `opsClass` over a prefix extended by one element (the loops' invariant). -/
theorem opsClass_snoc (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (l : List TxnOp) (op : TxnOp) :
    opsClass (GF := GF) M info l ∗ opClass M info op ⊢ opsClass M info (l ++ [op]) := by
  iintro ⟨H1, H2⟩
  iapply opsClass_app
  iframe H1
  rw [opsClass_cons, opsClass_nil_eq]
  iframe H2

theorem cmpsClass_nil (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) :
    ⊢ cmpsClass (GF := GF) M info [] := by
  unfold cmpsClass
  iapply BigSepL.bigSepL_nil.2
  iempintro

theorem cmpsClass_snoc (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (l : List CmpModel) (cm : CmpModel) (e : GoString) (he : authEndOf cm.rangeEnd e) :
    cmpsClass (GF := GF) M info l ∗ classRes M info [(cm.key, e, .read)] ⊢
      cmpsClass M info (l ++ [cm]) := by
  unfold cmpsClass
  iintro ⟨H1, H2⟩
  iapply BigSepL.bigSepL_snoc.2
  iframe H1
  iexists e
  iframe H2
  ipureintro; exact he

end defs

end apply
end EtcdGrove
end Perennial
