/-
Lemmas for the proofs of `client/v3/leasing`'s `txn.go` and `util.go` (the transaction builder,
`gatherOps`, `gatherResponseOps`, the guards): comparisons and operation lists. Lean-first (no
Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingKV

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

/-! ## Pure lemmas -/

theorem mapM_txnOpOf_append (a b : List OpFull) (ta tb : List TxnOp)
    (ha : a.mapM txnOpOf = some ta) (hb : b.mapM txnOpOf = some tb) :
    (a ++ b).mapM txnOpOf = some (ta ++ tb) := by
  rw [List.mapM_append, ha, hb]; rfl

theorem mapM_of_map_some (os : List OpFull) (ops : List TxnOp)
    (h : os.map txnOpOf = ops.map some) : os.mapM txnOpOf = some ops := by
  induction os generalizing ops with
  | nil => cases ops <;> simp_all
  | cons o os ih =>
    cases ops with
    | nil => simp at h
    | cons op ops =>
      simp only [List.map_cons, List.cons.injEq] at h
      simp [List.mapM_cons, h.1, ih ops h.2]

theorem leavesL_append (a b : List OpT) : OpT.leavesL (a ++ b) = OpT.leavesL a ++ OpT.leavesL b := by
  induction a with
  | nil => rfl
  | cons t ts ih => simp [OpT.leavesL, ih]


mutual
/-- The size of an operation tree (a recursion measure for `gatherOps`). -/
def OpT.size : OpT → Nat
  | .leaf _ => 1
  | .txn _ _ ts es => 1 + OpT.sizeL ts + OpT.sizeL es

/-- The size of a list of operation trees. -/
def OpT.sizeL : List OpT → Nat
  | [] => 0
  | t :: ts => t.size + OpT.sizeL ts
end

theorem OpT.sizeL_append (a b : List OpT) : OpT.sizeL (a ++ b) = OpT.sizeL a + OpT.sizeL b := by
  induction a with
  | nil => simp [OpT.sizeL]
  | cons t ts ih => simp [OpT.sizeL, ih]; omega

theorem OpT.size_le_of_getElem? (ts : List OpT) (i : Nat) (t : OpT) (h : ts[i]? = some t) :
    t.size ≤ OpT.sizeL ts := by
  induction ts generalizing i with
  | nil => simp at h
  | cons t' ts ih =>
    rcases i with _ | i
    · simp at h; subst h; simp [OpT.sizeL]
    · simp at h; have := ih i h; simp [OpT.sizeL]; omega

theorem OpT.leavesL_eq (ts : List OpT) : OpT.leavesL ts = ts.flatMap OpT.leaves := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [OpT.leavesL, ih]

theorem OpT.leavesL_take_succ (ts : List OpT) (i : Nat) (t : OpT) (h : ts[i]? = some t) :
    OpT.leavesL (ts.take (i + 1)) = OpT.leavesL (ts.take i) ++ t.leaves := by
  rw [OpT.leavesL_eq, OpT.leavesL_eq, List.take_add_one, h]
  simp

theorem OpT.leaves_txn (o : OpFull) (cs : List CmpModel) (ts es : List OpT) :
    (OpT.txn o cs ts es).leaves = OpT.leavesL (ts ++ es) := by
  rw [leavesL_append]; rfl


theorem OpT.chosenL_eq : ∀ (ts : List OpT) (rs : List TxnOpResult),
    OpT.chosenL ts rs = (ts.zip rs).flatMap (fun p => p.1.chosen p.2)
  | [], _ => by simp [OpT.chosenL]
  | _ :: _, [] => by simp [OpT.chosenL]
  | t :: ts, r :: rs => by simp [OpT.chosenL, OpT.chosenL_eq ts rs]

theorem OpT.chosenL_take_succ (ts : List OpT) (rs : List TxnOpResult) (i : Nat) (t : OpT)
    (r : TxnOpResult) (ht : ts[i]? = some t) (hr : rs[i]? = some r) :
    OpT.chosenL (ts.take (i + 1)) (rs.take (i + 1)) =
      OpT.chosenL (ts.take i) (rs.take i) ++ t.chosen r := by
  have hz : ∀ j, (ts.take j).zip (rs.take j) = (ts.zip rs).take j := by
    intro j; simp only [List.zip, List.take_zipWith]
  rw [OpT.chosenL_eq, OpT.chosenL_eq, hz, hz, List.take_add_one]
  have : (ts.zip rs)[i]? = some (t, r) := by simp [List.getElem?_zip_eq_some, ht, hr]
  rw [this]
  simp

theorem OpT.txnOp_txn (o : OpFull) (cs : List CmpModel) (ts es : List OpT) (op : TxnOp)
    (h : (OpT.txn o cs ts es).txnOp = some op) :
    ∃ a b, op = .txn cs a b ∧ OpT.txnOps ts = some a ∧ OpT.txnOps es = some b := by
  simp only [OpT.txnOp] at h
  split at h
  · rename_i a b ha hb
    simp at h; exact ⟨a, b, h.symm, ha, hb⟩
  · simp at h

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]


theorem txnOpsRespN_length :
    ∀ (ps : List Loc) (ops : List TxnOp) (rs : List TxnOpResult),
      txnOpsRespN (GF := GF) ps ops rs ⊢ ⌜ps.length = ops.length ∧ rs.length = ops.length⌝
  | [], [], [] => by iintro -; ipureintro; simp
  | p :: ps, op :: ops, r :: rs => by
    simp only [txnOpsRespN]
    iintro ⟨-, H⟩
    ihave %h := txnOpsRespN_length ps ops rs $$ H
    ipureintro; simp [h.1, h.2]
  | [], [], _ :: _ => by simp only [txnOpsRespN]; iintro H; iexfalso; iexact H
  | [], _ :: _, _ => by simp only [txnOpsRespN]; iintro H; iexfalso; iexact H
  | _ :: _, [], _ => by simp only [txnOpsRespN]; iintro H; iexfalso; iexact H
  | _ :: _, _ :: _, [] => by simp only [txnOpsRespN]; iintro H; iexfalso; iexact H

theorem txnOpsRespN_get :
    ∀ (ps : List Loc) (ops : List TxnOp) (rs : List TxnOpResult) (i : Nat) (p : Loc) (op : TxnOp)
      (r : TxnOpResult), ps[i]? = some p → ops[i]? = some op → rs[i]? = some r →
      txnOpsRespN (GF := GF) ps ops rs ⊢ txnOpRespN p op r
  | [], _, _, _, _, _, _, h, _, _ => by simp at h
  | _ :: _, [], _, _, _, _, _, _, h, _ => by simp at h
  | _ :: _, _ :: _, [], _, _, _, _, _, _, h => by simp at h
  | p' :: ps, op' :: ops, r' :: rs, i, p, op, r, h1, h2, h3 => by
    simp only [txnOpsRespN]
    rcases i with _ | i
    · simp at h1 h2 h3; subst h1 h2 h3
      iintro ⟨H, -⟩; iexact H
    · simp at h1 h2 h3
      iintro ⟨-, H⟩
      iapply txnOpsRespN_get ps ops rs i p op r h1 h2 h3 $$ H


/-! ## Lists of values related elementwise (`opsAt`, `cmpsAt`) -/

/-- The values `vs` and the models `os`, of the same length, related by `P` elementwise (the body
of `opsAt`/`cmpsAt`/`cmpsSetAt`). -/
def listRel {A B : Type} (P : A → B → IProp GF) (vs : List A) (os : List B) : IProp GF :=
  iprop(⌜vs.length = os.length⌝ ∗
    □ ∀ (i : Nat) (v : A) (o : B), ⌜vs[i]? = some v⌝ -∗ ⌜os[i]? = some o⌝ -∗ P v o)

instance listRel_persistent {A B : Type} (P : A → B → IProp GF) (vs : List A) (os : List B) :
    Persistent (listRel P vs os) := by
  unfold listRel; infer_instance

theorem listRel_nil {A B : Type} (P : A → B → IProp GF) : ⊢ listRel P ([] : List A) ([] : List B) := by
  unfold listRel
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %i %v %o %Hv
  simp at Hv

theorem listRel_single {A B : Type} (P : A → B → IProp GF) (v : A) (o : B)
    [Persistent (P v o)] : P v o ⊢ listRel P [v] [o] := by
  unfold listRel
  iintro #H
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %i %v' %o' %Hv %Ho
  rcases i with _ | i
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hv Ho
    subst Hv Ho; iexact H
  · simp at Hv

theorem listRel_cons {A B : Type} (P : A → B → IProp GF) (v : A) (o : B) (vs : List A)
    (os : List B) [Persistent (P v o)] : P v o ∗ listRel P vs os ⊢ listRel P (v :: vs) (o :: os) := by
  unfold listRel
  iintro ⟨#H, %Hl, #H'⟩
  isplitr
  · ipureintro; simp [Hl]
  imodintro
  iintro %i %v' %o' %Hv %Ho
  rcases i with _ | i
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hv Ho
    subst Hv Ho; iexact H
  · simp only [List.getElem?_cons_succ] at Hv Ho
    iapply H' $$ %i %v' %o' %Hv %Ho

theorem listRel_app {A B : Type} (P : A → B → IProp GF) (vs vs' : List A) (os os' : List B) :
    listRel P vs os ∗ listRel P vs' os' ⊢ listRel P (vs ++ vs') (os ++ os') := by
  unfold listRel
  iintro ⟨⟨%Hl, #H⟩, ⟨%Hl', #H'⟩⟩
  isplitr
  · ipureintro; simp [Hl, Hl']
  imodintro
  iintro %i %v %o %Hv %Ho
  by_cases hi : i < vs.length
  · rw [List.getElem?_append_left hi] at Hv
    rw [List.getElem?_append_left (by omega)] at Ho
    iapply H $$ %i %v %o %Hv %Ho
  · rw [List.getElem?_append_right (by omega)] at Hv
    rw [List.getElem?_append_right (by omega)] at Ho
    rw [Hl] at Hv
    iapply H' $$ %(i - os.length) %v %o %Hv %Ho

theorem opsAt_listRel (sl : GoSlice) (os : List OpFull) :
    opsAt (GF := GF) sl os ⊣⊢ ∃ vs, sl ↦*□ vs ∗ listRel opFullAt vs os := by
  unfold opsAt listRel; exact .rfl

theorem cmpsAt_listRel (sl : GoSlice) (ms : List CmpModel) :
    cmpsAt (GF := GF) sl ms ⊣⊢ ∃ cs, sl ↦*□ cs ∗ listRel cmpAt cs ms := by
  unfold cmpsAt listRel; exact .rfl

end defs

end EtcdGrove
end Perennial
