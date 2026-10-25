/-
Invariants, pure models, and representation predicates for `go.etcd.io/etcd/client/v3/ordering`
(etcd-io/etcd#22122).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.ordering.Base
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingTxnLemmas
public import Perennial.Proof.sync.RWMutexGuard

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ordering

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.ordering go_etcd_io.etcd.api.v3

/-! ## Pure model of `isReadOnly(op clientv3.Op) bool` -/

mutual
/-- `ordering.isReadOnly(op)` on an operation tree `OpT`: `true` for a `Get` leaf (`o.t = 1`),
`false` for any other leaf (`o.t ≠ 1`), and for a transaction (`OpT.txn`) recursively `true` iff
every operation in both `thenOps` and `elseOps` satisfies `isReadOnlyM`. -/
def isReadOnlyM : OpT → Bool
  | .leaf o => decide (o.t = W64 1)
  | .txn _ _ ts es => isReadOnlyListM ts && isReadOnlyListM es

/-- `isReadOnlyM` across a list of operation trees. -/
def isReadOnlyListM : List OpT → Bool
  | [] => true
  | t :: ts => isReadOnlyM t && isReadOnlyListM ts
end

theorem isReadOnlyListM_eq_all : ∀ ts : List OpT, isReadOnlyListM ts = ts.all isReadOnlyM
  | [] => rfl
  | t :: ts => by simp [isReadOnlyListM, isReadOnlyListM_eq_all ts]

theorem isReadOnlyListM_append (a b : List OpT) :
    isReadOnlyListM (a ++ b) = (isReadOnlyListM a && isReadOnlyListM b) := by
  rw [isReadOnlyListM_eq_all, isReadOnlyListM_eq_all, isReadOnlyListM_eq_all, List.all_append]

theorem isReadOnlyListM_take_succ (ts : List OpT) (i : Nat) (t : OpT) (h : ts[i]? = some t) :
    isReadOnlyListM (ts.take (i + 1)) = (isReadOnlyListM (ts.take i) && isReadOnlyM t) := by
  rw [List.take_add_one, h]
  simp [isReadOnlyListM_append, isReadOnlyListM]

theorem isReadOnlyListM_false_of_getElem? (ts : List OpT) (i : Nat) (t : OpT)
    (hi : ts[i]? = some t) (ht : isReadOnlyM t = false) :
    isReadOnlyListM ts = false := by
  rw [isReadOnlyListM_eq_all, List.all_eq_false]
  exact ⟨t, List.mem_of_getElem? hi, by simp [ht]⟩

mutual
/-- `isReadOnlyM t = true` iff every leaf operation in `t.leaves` is a `Get` (`o.t = W64 1`). -/
theorem isReadOnlyM_iff_leaves : ∀ t : OpT,
    isReadOnlyM t = true ↔ ∀ o ∈ t.leaves, o.t = W64 1
  | .leaf o => by
    simp [isReadOnlyM, OpT.leaves]
  | .txn _ _ ts es => by
    simp only [isReadOnlyM, OpT.leaves, Bool.and_eq_true, List.mem_append]
    rw [isReadOnlyListM_iff_leavesL ts, isReadOnlyListM_iff_leavesL es]
    constructor
    · rintro ⟨h1, h2⟩ o (ho | ho)
      · exact h1 o ho
      · exact h2 o ho
    · intro h
      exact ⟨fun o ho => h o (Or.inl ho), fun o ho => h o (Or.inr ho)⟩

/-- `isReadOnlyListM ts = true` iff every leaf operation in `OpT.leavesL ts` is a `Get` (`o.t = W64 1`). -/
theorem isReadOnlyListM_iff_leavesL : ∀ ts : List OpT,
    isReadOnlyListM ts = true ↔ ∀ o ∈ OpT.leavesL ts, o.t = W64 1
  | [] => by simp [isReadOnlyListM, OpT.leavesL]
  | t :: ts => by
    simp only [isReadOnlyListM, OpT.leavesL, Bool.and_eq_true, List.mem_append]
    rw [isReadOnlyM_iff_leaves t, isReadOnlyListM_iff_leavesL ts]
    constructor
    · rintro ⟨h1, h2⟩ o (ho | ho)
      · exact h1 o ho
      · exact h2 o ho
    · intro h
      exact ⟨fun o ho => h o (Or.inl ho), fun o ho => h o (Or.inr ho)⟩
end

/-- `isReadOnlyM t = false` iff `t` contains at least one non-`Get` leaf (`o.t ≠ W64 1`) in some
branch. -/
theorem isReadOnlyM_false_iff_exists_non_get (t : OpT) :
    isReadOnlyM t = false ↔ ∃ o ∈ t.leaves, o.t ≠ W64 1 := by
  rw [← Bool.not_eq_true, isReadOnlyM_iff_leaves]
  simp

/-! ## Representation predicates for `kvOrdering` and `txnOrdering` -/

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- The address of `kv.revMu`. -/
abbrev revMuAddr (kvp : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.client.v3.ordering.kvOrdering go!"revMu" kvp

/-- The address of `kv.prevRev`. -/
abbrev prevRevAddr (kvp : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.client.v3.ordering.kvOrdering go!"prevRev" kvp

/-- The resolved method expression for an interface value `i` and method name `m`
(after `method_interface_ok` steps `MethodResolve t m #i`). -/
abbrev ifaceMethod (i : GoInterface) (m : GoString) : Expr :=
  match i with
  | GoInterface.nil => Panic "nil interface"
  | GoInterface.ok ii => Val #(methods ii.ty m ii.v)

/-- `sync.Mutex{}` evaluates to the unlocked `sync.Mutex` zero value (`#false`).
In Go, `sync.Mutex` is a struct, so `sync.Mutex{}` (`CompositeLiteral sync.Mutex.ty (LiteralValueV [])`)
evaluates to its zero value; in Perennial's `TrustedCode/sync.lean`, `sync.Mutex.underlying` is
modeled as `go.bool` (`false`), which does not have a `StructType` composite-literal rule. -/
class MutexCompositeLiteral [FfiSyntax] [GoGlobalContext] [GoLocalContext]
    [GoSemanticsFunctions] : Prop where
  step : ⟦CompositeLiteral sync.Mutex.ty, LiteralValueV []⟧ ⤳ #false

attribute [instance] MutexCompositeLiteral.step

end addrs

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.ordering.Assumptions]

/-- The fractional lock invariant of `kv.revMu`: holds `kv.prevRev` with fraction `q` and a
persistent revision predicate `□ R prev`. -/
def kvOrderingLockInv (kvp : Loc) (R : w64 → IProp GF) (q : Qp) : IProp GF :=
  iprop(∃ prev : w64,
    prevRevAddr kvp ↦{DFrac.own q} prev ∗
    □ R prev)

instance kvOrderingLockInv_fractional (kvp : Loc) (R : w64 → IProp GF) :
    Fractional (kvOrderingLockInv (GF := GF) kvp R) where
  fractional q1 q2 := by
    have hsplit : ∀ prev : w64,
        (prevRevAddr kvp ↦{DFrac.own (q1 + q2)} prev : IProp GF) ⊣⊢
        prevRevAddr kvp ↦{DFrac.own q1} prev ∗
        prevRevAddr kvp ↦{DFrac.own q2} prev :=
      fun prev => (typedPointsto_dfractional (GF := GF) _ prev).dfractional (DFrac.own q1) (DFrac.own q2)
    constructor
    · iintro H
      unfold kvOrderingLockInv
      icases H with ⟨%prev, Hprev, #HR⟩
      icases (hsplit prev).1 $$ Hprev with ⟨H1, H2⟩
      isplitl [H1]
      · iexists prev; iframe; iexact HR
      · iexists prev; iframe; iexact HR
    · iintro ⟨H1, H2⟩
      unfold kvOrderingLockInv
      icases H1 with ⟨%p1, H1, #HR1⟩
      icases H2 with ⟨%p2, H2, -⟩
      icombine H1 H2 gives %Heq
      subst Heq
      iexists p1
      iframe HR1
      iapply (hsplit p1).2
      iframe

/-- A reader/writer token for `kv.revMu` (`sync.ownRWMutex`). -/
def kvOrderingHandle (kvp : Loc) (R : w64 → IProp GF) : IProp GF :=
  sync.ownRWMutex (revMuAddr kvp) (kvOrderingLockInv (hG := hG) kvp R)

/-- Fixed fields of `*kvOrdering` (`KV` and `orderViolationFunc`, read-only). -/
def isKvOrdering (kvp : Loc) (kv : go_etcd_io.etcd.client.v3.KV) (vf : OrderViolationFunc) :
    IProp GF :=
  iprop(⌜kvp ≠ null⌝ ∗
    structFieldRef go_etcd_io.etcd.client.v3.ordering.kvOrdering go!"KV" kvp ↦□ kv ∗
    structFieldRef go_etcd_io.etcd.client.v3.ordering.kvOrdering go!"orderViolationFunc" kvp ↦□ vf)

instance isKvOrdering_persistent (kvp : Loc) (kv : go_etcd_io.etcd.client.v3.KV)
    (vf : OrderViolationFunc) : Persistent (isKvOrdering (GF := GF) kvp kv vf) := by
  unfold isKvOrdering; infer_instance

/-- The state of a `*txnOrdering` builder: its current `cmps`, `thenOps`, and `elseOps` slices and
their models. -/
structure TxnOrderingState where
  csl : GoSlice
  tsl : GoSlice
  esl : GoSlice
  ms : List CmpModel
  ts : List OpT
  es : List OpT

/-- Ownership of a `*txnOrdering` builder `txnp` associated with `kvp`. -/
def ownTxnOrdering (txnp kvp : Loc) (innerTxn : go_etcd_io.etcd.client.v3.Txn)
    (ctx : context.Context) (st : TxnOrderingState) : IProp GF :=
  iprop(⌜txnp ≠ null⌝ ∗
    structFieldRef go_etcd_io.etcd.client.v3.ordering.txnOrdering go!"Txn" txnp ↦□ innerTxn ∗
    structFieldRef go_etcd_io.etcd.client.v3.ordering.txnOrdering go!"kvOrdering" txnp ↦□ kvp ∗
    structFieldRef go_etcd_io.etcd.client.v3.ordering.txnOrdering go!"ctx" txnp ↦□ ctx ∗
    sync.isMutex (structFieldRef go_etcd_io.etcd.client.v3.ordering.txnOrdering go!"mu" txnp) iprop(True) ∗
    structFieldRef go_etcd_io.etcd.client.v3.ordering.txnOrdering go!"cmps" txnp ↦ st.csl ∗
    cmpsAt st.csl st.ms ∗
    structFieldRef go_etcd_io.etcd.client.v3.ordering.txnOrdering go!"thenOps" txnp ↦ st.tsl ∗
    opsTAt st.tsl st.ts ∗
    structFieldRef go_etcd_io.etcd.client.v3.ordering.txnOrdering go!"elseOps" txnp ↦ st.esl ∗
    opsTAt st.esl st.es)

/-- Specification of an `OrderViolationFunc` callback `vf`: given `(op, resp, prevRev)` when a
response revision `< prevRev` is observed, returns either `nil` (requesting retry if possible) or a
non-nil error satisfying `PostErr err`. -/
def orderViolationSpec (vf : OrderViolationFunc) (R : w64 → IProp GF)
    (PostErr : GoInterface → IProp GF) : IProp GF :=
  iprop(□ ∀ (opv : go_etcd_io.etcd.client.v3.Op) (r : go_etcd_io.etcd.client.v3.OpResponse)
      (prevRev : w64),
    {{ □ R prevRev }}
      (App (App (App (Val #vf) (Val #opv)) (Val #r)) (Val #prevRev))
    {{ (err : GoInterface), RET #err;
        if decide (err = GoInterface.nil) then True else PostErr err }})

instance orderViolationSpec_persistent (vf : OrderViolationFunc) (R : w64 → IProp GF)
    (PostErr : GoInterface → IProp GF) :
    Persistent (orderViolationSpec (GF := GF) vf R PostErr) := by
  unfold orderViolationSpec; infer_instance

/-- Specification of `kv.Do(ctx, op)` for a `Get` operation `o`. -/
def kvDoGetSpec (kv : go_etcd_io.etcd.client.v3.KV) (ctx : context.Context) (o : OpFull)
    (R : w64 → IProp GF) (PostOk : Loc → w64 → IProp GF)
    (PostErr : GoInterface → IProp GF) : IProp GF :=
  iprop(□ ∀ (opv : go_etcd_io.etcd.client.v3.Op),
    {{ opFullAt opv o }}
      (App (App (ifaceMethod kv go!"Do") (Val #ctx)) (Val #opv))
    {{ (r : go_etcd_io.etcd.client.v3.OpResponse) (err : GoInterface), RET (PairV #r #err);
        if decide (err = GoInterface.nil) then
          ∃ (hdr : Loc) (rev : w64),
            ⌜r.get' ≠ null ∧ hdr ≠ null⌝ ∗
            structFieldRef etcdserverpb.RangeResponse go!"Header" r.get' ↦□ hdr ∗
            structFieldRef etcdserverpb.ResponseHeader go!"Revision" hdr ↦□ rev ∗
            □ R rev ∗ PostOk r.get' rev
        else PostErr err }})

instance kvDoGetSpec_persistent (kv : go_etcd_io.etcd.client.v3.KV) (ctx : context.Context)
    (o : OpFull) (R : w64 → IProp GF) (PostOk : Loc → w64 → IProp GF)
    (PostErr : GoInterface → IProp GF) :
    Persistent (kvDoGetSpec (GF := GF) kv ctx o R PostOk PostErr) := by
  unfold kvDoGetSpec; infer_instance

/-- Specification of `kv.Do(ctx, opTxn)` for a transaction `(ms, ts, es)` consuming an execution
token `P : IProp GF`.
For a read-only transaction (`isReadOnlyM = true`), `Commit` requires `□ P` (as it may retry on
ordering violations); for a mutable transaction (`isReadOnlyM = false`), `Commit` requires only a
single linear `P`, proving in separation logic that `Do` is invoked at most once. -/
def kvDoTxnSpec (kv : go_etcd_io.etcd.client.v3.KV) (ctx : context.Context)
    (ms : List CmpModel) (ts es : List OpT) (R : w64 → IProp GF) (P : IProp GF)
    (PostOk : Loc → w64 → IProp GF) (PostErr : GoInterface → IProp GF) : IProp GF :=
  iprop(□ ∀ (opv : go_etcd_io.etcd.client.v3.Op),
    {{ P ∗ opTAtC false opv (.txn OpFull.txnInit ms ts es) }}
      (App (App (ifaceMethod kv go!"Do") (Val #ctx)) (Val #opv))
    {{ (r : go_etcd_io.etcd.client.v3.OpResponse) (err : GoInterface), RET (PairV #r #err);
        if decide (err = GoInterface.nil) then
          ∃ (hdr : Loc) (rev : w64),
            ⌜r.txn' ≠ null ∧ hdr ≠ null⌝ ∗
            structFieldRef etcdserverpb.TxnResponse go!"Header" r.txn' ↦□ hdr ∗
            structFieldRef etcdserverpb.ResponseHeader go!"Revision" hdr ↦□ rev ∗
            □ R rev ∗ PostOk r.txn' rev
        else PostErr err }})

instance kvDoTxnSpec_persistent (kv : go_etcd_io.etcd.client.v3.KV) (ctx : context.Context)
    (ms : List CmpModel) (ts es : List OpT) (R : w64 → IProp GF) (P : IProp GF)
    (PostOk : Loc → w64 → IProp GF) (PostErr : GoInterface → IProp GF) :
    Persistent (kvDoTxnSpec (GF := GF) kv ctx ms ts es R P PostOk PostErr) := by
  unfold kvDoTxnSpec; infer_instance

/-- From `cmpsAt`, `opsTAt tsl ts`, and `opsTAt esl es`, an `Op` built by `OpTxn(csl, tsl, esl)`
satisfies `opTAtC false opv (.txn OpFull.txnInit ms ts es)`. -/
theorem opTAtC_of_OpTxn (opv : go_etcd_io.etcd.client.v3.Op) (ms : List CmpModel)
    (tsl esl : GoSlice) (ts es : List OpT) (ht : opv.thenOps' = tsl) (he : opv.elseOps' = esl) :
    opFullAt (GF := GF) opv OpFull.txnInit ∗ cmpsAt opv.cmps' ms ∗
      opsTAt tsl ts ∗ opsTAt esl es ⊢
      opTAtC false opv (.txn OpFull.txnInit ms ts es) := by
  unfold opsTAt
  iintro ⟨#Hfull, #Hcmps, ⟨%tvs, #Htvs, #Hts⟩, ⟨%evs, #Hevs, #Hes⟩⟩
  unfold opTAtC
  simp only [Bool.false_eq_true, ↓reduceIte, ht, he]
  iframe #
  ipureintro; rfl

end defs

end ordering
end EtcdGrove
end Perennial
