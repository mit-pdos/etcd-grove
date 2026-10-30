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
variable [GooseExts] [GooseSemantics] [GooseInterp]
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

/-! ## The class of a request, and its principal (A3, 2026-10-23) -/

/-- **The principal of the request `rq`** as the auth layer's `Apply` records it in its
`authInfo` (`auth.go`): the header's `Username` and `AuthRevision`; with no header, the zero
`AuthInfo` the field holds between `Apply`s (set at construction, reset after every `Apply`). -/
def principalOf (rq : IRRModel) : go_etcd_io.etcd.server.v3.auth.AuthInfo :=
  match rq.header with
  | some hm => ⟨hm.username, hm.authRevision⟩
  | none => zeroValDef

/-- **The class of the request `rq`** for the principal `info` in the mode `M`: the permissions
its KV request needs (`putClass`, `deleteClass`, `rangeClass`, `txnClass`); nothing for the other
requests (a lease revocation's keys are not stated: `checkLeasePuts`, see the header). -/
def reqClass (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (rq : IRRModel) : IProp GF :=
  match dispatchKind rq with
  | .put => iprop(∃ o : OpFull, ⌜rq.put = some o⌝ ∗ putClass M info o)
  | .deleteRange => iprop(∃ o : OpFull, ⌜rq.deleteRange = some o⌝ ∗ deleteClass M info o)
  | .range => iprop(∃ o : OpFull, ⌜rq.range = some o⌝ ∗ rangeClass M info o)
  | .txn => iprop(∃ t : TxnModel, ⌜rq.txn = some t⌝ ∗ txnClass M info t)
  | _ => iprop(True)

instance reqClass_persistent (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (rq : IRRModel) : Persistent (reqClass (GF := GF) M info rq) := by
  unfold reqClass; split <;> infer_instance

/-- A request the auth layer's KV methods do not check has the trivial class. -/
theorem reqClass_nonKV (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (rq : IRRModel) (h : isKVKind (dispatchKind rq) = false) : ⊢ reqClass (GF := GF) M info rq := by
  unfold reqClass
  split
  all_goals first | (iintro; itrivial) | (exfalso; simp_all [isKVKind])

theorem reqClass_put (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (rq : IRRModel) (o : OpFull) (h : rq.put = some o) (hk : dispatchKind rq = .put) :
    putClass (GF := GF) M info o ⊢ reqClass M info rq := by
  unfold reqClass; rw [hk]; iintro H; iexists o; iframe H; ipureintro; exact h

theorem reqClass_deleteRange (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (rq : IRRModel) (o : OpFull) (h : rq.deleteRange = some o) (hk : dispatchKind rq = .deleteRange) :
    deleteClass (GF := GF) M info o ⊢ reqClass M info rq := by
  unfold reqClass; rw [hk]; iintro H; iexists o; iframe H; ipureintro; exact h

theorem reqClass_range (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (rq : IRRModel) (o : OpFull) (h : rq.range = some o) (hk : dispatchKind rq = .range) :
    rangeClass (GF := GF) M info o ⊢ reqClass M info rq := by
  unfold reqClass; rw [hk]; iintro H; iexists o; iframe H; ipureintro; exact h

theorem reqClass_txn (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (rq : IRRModel) (t : TxnModel) (h : rq.txn = some t) (hk : dispatchKind rq = .txn) :
    txnClass (GF := GF) M info t ⊢ reqClass M info rq := by
  unfold reqClass; rw [hk]; iintro H; iexists t; iframe H; ipureintro; exact h

/-- The read of a range `o` from its check's verdict (`IsRangePermitted(key, rangeEnd)` on the
request's slices, the model's end `rangeEndOf esl e`). -/
theorem rangeClass_of_verdict (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (o : OpFull) (esl : GoSlice) (e : GoString) (hl : e.length = sint.nat esl.len)
    (hre : o.base.rangeEnd = txn.rangeEndOf esl e) :
    auth.permVerdict (GF := GF) M info o.key e .read GoInterface.nil ⊢ rangeClass M info o := by
  unfold rangeClass
  iintro H
  iexists e
  isplitl []
  · ipureintro; rw [hre]; exact authEndOf_rangeEndOf esl e hl
  · iapply (classRes_of_permVerdict M info o.key e .read) $$ H

/-- The class of a delete `o` from its checks' verdicts (`IsDeleteRangePermitted`, and with
`PrevKv` `IsRangePermitted`, on the request's slices). -/
theorem deleteClass_of_verdicts (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (o : OpFull) (esl : GoSlice) (e : GoString) (hl : e.length = sint.nat esl.len)
    (hre : o.base.rangeEnd = txn.rangeEndOf esl e) :
    auth.permVerdict (GF := GF) M info o.key e .write GoInterface.nil ∗
      (∀ _ : o.base.prevKV = true, auth.permVerdict M info o.key e .read GoInterface.nil) ⊢
      deleteClass M info o := by
  unfold deleteClass
  iintro ⟨Hw, Hr⟩
  iexists e
  isplitl []
  · ipureintro; rw [hre]; exact authEndOf_rangeEndOf esl e hl
  iapply classRes_cons
  isplitl [Hw]
  · iapply (classRes_of_permVerdict M info o.key e .write) $$ Hw
  cases hp : o.base.prevKV
  · simp only [Bool.false_eq_true, ↓reduceIte]; iapply classRes_nil
  · simp only [↓reduceIte]
    ihave Hr := Hr $$ %rfl
    iapply (classRes_of_permVerdict M info o.key e .read) $$ Hr

/-- **The class of a `UserGet` of the user `n`** by the principal `info` (`authApplierV3.UserGet`,
`auth.go`): an admin (`IsAdminPermitted`'s verdict at `nil`), or the user itself. -/
def userGetClass (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (n : GoString) : IProp GF :=
  iprop(auth.adminVerdict M (some info) GoInterface.nil ∨ ⌜n = info.Username'⌝)

instance userGetClass_persistent (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (n : GoString) : Persistent (userGetClass (GF := GF) M info n) := by
  unfold userGetClass; infer_instance

/-! ## The watch service's class (the auth plan's A4, 2026-10-24) -/

/-- **The key a watch create request's check sees** (`watch.go`'s `recvLoop`): an empty key is
`"\x00"`, the smallest key. -/
def watchKey (key : GoString) : GoString := if key = [] then [W8 0] else key

/-- **The read a watch create request asks** (`serverWatchStream.isWatchPermitted`,
`IsRangePermitted(authInfo, creq.Key, creq.RangeEnd)` with the key normalized and the range end as
the request gave it: a point when empty, from the key on when `"\x00"` (`WithFromKey`), else the
range `[Key, RangeEnd)`); the check runs before `recvLoop` rewrites the range end for mvcc. -/
def watchPerms (key rangeEnd : GoString) : List Perm3 := [(watchKey key, rangeEnd, .read)]

/-- **The class of a watch create request** for the principal `info` in the mode `M`
(`notes/auth-matrix.md`'s `Watch` row: RBAC read `[Key, RangeEnd)`). -/
def watchClass (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (key rangeEnd : GoString) : IProp GF :=
  classRes M info (watchPerms key rangeEnd)

instance watchClass_persistent (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (key rangeEnd : GoString) : Persistent (watchClass (GF := GF) M info key rangeEnd) := by
  unfold watchClass; infer_instance

theorem watchKey_ne_nil (key : GoString) : watchKey key ≠ [] := by
  unfold watchKey; split <;> simp_all

/-- In the mode `on γa`, the watch class names a recorded state that permitted the read. -/
theorem watchClass_on (γa : auth.AuthNames) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (key rangeEnd : GoString) :
    watchClass (GF := GF) (.on γa) info key rangeEnd ⊢
      ∃ (i : Nat) (st : auth.AuthState), auth.authStateAt γa i st ∗
        ⌜auth.permitted st (auth.authInfoM info) (watchKey key) rangeEnd .read⌝ := by
  unfold watchClass classRes classOk watchPerms
  iintro H
  ihave ⟨H1, -⟩ := BigSepL.bigSepL_cons.1 $$ H
  icases H1 with ⟨%i, %st, #Hst, %Hp⟩
  iexists i, st
  iframe #
  ipureintro; exact Hp

/-- **The class result no older than the index `n`** (G2, 2026-10-30; `classRes` at a reader's
lower bound): in the mode `on γa`, each permission of `perms` granted by a state recorded at an index
at least `n`; nothing otherwise. -/
def classResFrom (M : auth.AuthMode) (n : Nat) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (perms : List Perm3) : IProp GF :=
  match M with
  | .on γa => iprop([∗list] x ∈ perms, ∃ (i : Nat) (st : auth.AuthState),
      auth.authStateAt γa i st ∗ ⌜n ≤ i ∧ auth.permitted st (auth.authInfoM info) x.1 x.2.1 x.2.2⌝)
  | _ => iprop(True)

instance classResFrom_persistent (M : auth.AuthMode) (n : Nat)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (perms : List Perm3) :
    Persistent (classResFrom (GF := GF) M n info perms) := by
  unfold classResFrom; cases M <;> infer_instance

/-- At the bound `0` the class result no older than it is the class result. -/
theorem classResFrom_zero (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (perms : List Perm3) :
    classRes (GF := GF) M info perms ⊢ classResFrom M 0 info perms := by
  cases M with
  | on γa =>
    unfold classRes classOk classResFrom
    iapply BigSepL.bigSepL_mono_of_forall
    intro _ x
    iintro ⟨%i, %st, #Hst, %Hp⟩
    iexists i, st
    iframe Hst
    ipureintro; exact ⟨Nat.zero_le _, Hp⟩
  | off => iintro -; unfold classResFrom; itrivial
  | any => iintro -; unfold classResFrom; itrivial

/-- **The class of a watch create request no older than the index `n`** (G2; `watchClass` at the
client's bound, as `rangeClassFrom` is `rangeClass`'s). -/
def watchClassFrom (M : auth.AuthMode) (n : Nat) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (key rangeEnd : GoString) : IProp GF :=
  classResFrom M n info (watchPerms key rangeEnd)

instance watchClassFrom_persistent (M : auth.AuthMode) (n : Nat)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (key rangeEnd : GoString) :
    Persistent (watchClassFrom (GF := GF) M n info key rangeEnd) := by
  unfold watchClassFrom; infer_instance

/-- At the bound `0` the class no older than it is the class. -/
theorem watchClassFrom_zero (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (key rangeEnd : GoString) :
    watchClass (GF := GF) M info key rangeEnd ⊢ watchClassFrom M 0 info key rangeEnd := by
  unfold watchClass watchClassFrom
  exact classResFrom_zero M info _

/-- **In the mode `on γa`, the class no older than `n` names a state recorded at an index at least
`n` that permitted the read.** -/
theorem watchClassFrom_on (γa : auth.AuthNames) (n : Nat)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (key rangeEnd : GoString) :
    watchClassFrom (GF := GF) (.on γa) n info key rangeEnd ⊢
      ∃ (i : Nat) (st : auth.AuthState), auth.authStateAt γa i st ∗
        ⌜n ≤ i ∧ auth.permitted st (auth.authInfoM info) (watchKey key) rangeEnd .read⌝ := by
  unfold watchClassFrom classResFrom watchPerms
  iintro H
  ihave ⟨H1, -⟩ := BigSepL.bigSepL_cons.1 $$ H
  iexact H1

/-- Outside the mode `on`, the class no older than any `n` holds (G2's freeze, 2026-10-30). -/
theorem classResFrom_not_on (M : auth.AuthMode) (n : Nat)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (perms : List Perm3)
    (h : ∀ γa, M ≠ .on γa) : ⊢ classResFrom (GF := GF) M n info perms := by
  cases M with
  | off => unfold classResFrom; itrivial
  | any => unfold classResFrom; itrivial
  | on γa => exact absurd rfl (h γa)

/-- In the mode `on γa`, a state recorded at an index at least `n` permitting one permission gives
its class no older than `n` (G2's freeze, 2026-10-30). -/
theorem classResFrom_on_singleton (γa : auth.AuthNames) (n : Nat)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (k e : GoString) (op : auth.PermType) :
    (∃ (i : Nat) (st : auth.AuthState), auth.authStateAt (GF := GF) γa i st ∗
        ⌜n ≤ i ∧ auth.permitted st (auth.authInfoM info) k e op⌝) ⊢
      classResFrom (.on γa) n info [(k, e, op)] := by
  unfold classResFrom
  iintro H
  iapply BigSepL.bigSepL_singleton.2
  iexact H

/-- The watch's normalized key (G2's freeze, 2026-10-30). -/
theorem watchKey_eq (key : GoString) : watchKey key = if key = [] then [W8 0] else key := rfl

/-- The class of the watch's normalized read is the watch's class (G2's freeze, 2026-10-30). -/
theorem watchClassFrom_of_classResFrom (M : auth.AuthMode) (n : Nat)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (key rangeEnd : GoString) :
    classResFrom (GF := GF) M n info
        [((if key = [] then [W8 0] else key), rangeEnd, auth.PermType.read)] ⊢
      watchClassFrom M n info key rangeEnd := by
  unfold watchClassFrom watchPerms watchKey
  iintro H; iexact H

/-- A registered watch's request has the shape the permission cache decides (`auth.reqShape`):
mvcc's `Watch` registers `[k, e')` (`e'` the rewritten range end: empty for `"\x00"`) only for
`e' = []` or `k < e'`. -/
theorem reqShape_of_watch (key e : GoString)
    (h : (if e = [W8 0] then [] else e) = [] ∨
      go.GoStringLt (watchKey key) (if e = [W8 0] then [] else e)) :
    auth.reqShape (watchKey key) e := by
  refine ⟨watchKey_ne_nil key, ?_⟩
  by_cases he : e = [W8 0]
  · right; left; rw [he]; rfl
  · simp only [he, ↓reduceIte] at h
    rcases h with h | h
    · left; exact h
    · right; right; exact h

end defs

end apply
end EtcdGrove
end Perennial
