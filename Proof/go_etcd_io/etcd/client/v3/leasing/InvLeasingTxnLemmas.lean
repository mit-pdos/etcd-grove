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

theorem map_some_of_mapM (os : List OpFull) (ops : List TxnOp)
    (h : os.mapM txnOpOf = some ops) : os.map txnOpOf = ops.map some := by
  induction os generalizing ops with
  | nil => simp at h; subst h; rfl
  | cons o os ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind] at h
    cases h1 : txnOpOf o with
    | none => simp [h1] at h
    | some a =>
      cases h2 : os.mapM txnOpOf with
      | none => simp [h1, h2] at h
      | some b =>
        simp [h1, h2] at h
        subst h
        simp [h1, ih b h2]

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

theorem OpT.txnOps_length : ∀ (ts : List OpT) (ops : List TxnOp),
    OpT.txnOps ts = some ops → ops.length = ts.length
  | [], ops, h => by simp [OpT.txnOps] at h; subst h; rfl
  | t :: ts, ops, h => by
    simp only [OpT.txnOps] at h
    split at h
    · rename_i a b _ hb
      simp at h; subst h
      simp [OpT.txnOps_length ts b hb]
    · simp at h

theorem OpT.txnOps_getElem : ∀ (ts : List OpT) (ops : List TxnOp) (i : Nat) (t : OpT),
    OpT.txnOps ts = some ops → ts[i]? = some t → ∃ op, t.txnOp = some op ∧ ops[i]? = some op
  | [], _, _, _, _, h => by simp at h
  | t' :: ts, ops, i, t, h, hi => by
    simp only [OpT.txnOps] at h
    split at h
    · rename_i a b ha hb
      simp at h; subst h
      rcases i with _ | i
      · simp at hi; subst hi; exact ⟨a, ha, rfl⟩
      · simp at hi
        obtain ⟨op, h1, h2⟩ := OpT.txnOps_getElem ts b i t hb hi
        exact ⟨op, h1, by simpa using h2⟩
    · simp at h

theorem OpT.txnOp_txn (o : OpFull) (cs : List CmpModel) (ts es : List OpT) (op : TxnOp)
    (h : (OpT.txn o cs ts es).txnOp = some op) :
    ∃ a b, op = .txn cs a b ∧ OpT.txnOps ts = some a ∧ OpT.txnOps es = some b := by
  simp only [OpT.txnOp] at h
  split at h
  · rename_i a b ha hb
    simp at h; exact ⟨a, b, h.symm, ha, hb⟩
  · simp at h

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A comparison with its operand set is a comparison. -/
theorem cmpSetAt_cmpAt (c : go_etcd_io.etcd.client.v3.Cmp) (m : CmpModel) :
    cmpSetAt (GF := GF) c m ⊢ cmpAt c m := by
  unfold cmpSetAt cmpAt compareAt
  iintro ⟨%Hc, %ksl, %esl, %u, #H1, #H2, #H3, #H4, #H5, #H6, #H7, #H8, -⟩
  iframe %Hc
  iexists ksl, esl, u
  iframe #

theorem cmpsSetAt_cmpsAt (sl : GoSlice) (ms : List CmpModel) :
    cmpsSetAt (GF := GF) sl ms ⊢ cmpsAt sl ms := by
  unfold cmpsSetAt cmpsAt
  iintro ⟨%cs, #Hsl, %Hlen, #H⟩
  iexists cs
  iframe #
  isplitr
  · ipureintro; exact Hlen
  imodintro
  iintro %i %c %m %Hc %Hm
  iapply cmpSetAt_cmpAt
  iapply H $$ %i %c %m %Hc %Hm

/-- `opListAtC` of plain operations does not depend on the capacity flag. -/
theorem opListAtC_leaves (c : Bool) :
    ∀ (vs : List go_etcd_io.etcd.client.v3.Op) (os : List OpFull),
      opListAtC (GF := GF) false vs (os.map OpT.leaf) ⊢ opListAtC c vs (os.map OpT.leaf)
  | [], [] => by simp only [List.map_nil, opListAtC]; iintro -; itrivial
  | [], _ :: _ => by simp only [List.map_cons, opListAtC]; iintro H; iexact H
  | _ :: _, [] => by simp only [List.map_nil, opListAtC]; iintro H; iexact H
  | v :: vs, o :: os => by
    simp only [List.map_cons, opListAtC, opTAtC]
    iintro ⟨H1, H2⟩
    iframe H1
    iapply opListAtC_leaves c vs os $$ H2


theorem opListAtC_length (c : Bool) :
    ∀ (vs : List go_etcd_io.etcd.client.v3.Op) (ts : List OpT),
      opListAtC (GF := GF) c vs ts ⊢ ⌜vs.length = ts.length⌝
  | [], [] => by iintro -; ipureintro; rfl
  | [], _ :: _ => by simp only [opListAtC]; iintro H; iexfalso; iexact H
  | _ :: _, [] => by simp only [opListAtC]; iintro H; iexfalso; iexact H
  | v :: vs, t :: ts => by
    simp only [opListAtC]
    iintro ⟨-, H⟩
    ihave %h := opListAtC_length c vs ts $$ H
    ipureintro; simp [h]

/-- The first of the trees `drop i`. -/
theorem opListAtC_drop (c : Bool) (vs : List go_etcd_io.etcd.client.v3.Op) (ts : List OpT)
    (i : Nat) (v : go_etcd_io.etcd.client.v3.Op) (t : OpT) (hv : vs[i]? = some v)
    (ht : ts[i]? = some t) :
    opListAtC (GF := GF) c (vs.drop i) (ts.drop i) ⊢
      opTAtC c v t ∗ opListAtC c (vs.drop (i + 1)) (ts.drop (i + 1)) := by
  have hvi : i < vs.length := (List.getElem?_eq_some_iff.1 hv).1
  have hti : i < ts.length := (List.getElem?_eq_some_iff.1 ht).1
  rw [List.drop_eq_getElem_cons hvi, List.drop_eq_getElem_cons hti]
  have e1 : vs[i] = v := (List.getElem?_eq_some_iff.1 hv).2
  have e2 : ts[i] = t := (List.getElem?_eq_some_iff.1 ht).2
  rw [e1, e2]
  simp only [opListAtC]
  exact .rfl


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


/-- The `i`-th tree of a list of trees (any capacity flag). -/
theorem opListAtC_get (c : Bool) :
    ∀ (vs : List go_etcd_io.etcd.client.v3.Op) (ts : List OpT) (i : Nat)
      (v : go_etcd_io.etcd.client.v3.Op) (t : OpT), vs[i]? = some v → ts[i]? = some t →
      opListAtC (GF := GF) c vs ts ⊢ opTAtC c v t ∗ True
  | [], _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, _, h => by simp at h
  | v' :: vs, t' :: ts, i, v, t, hv, ht => by
    simp only [opListAtC]
    rcases i with _ | i
    · simp at hv ht; subst hv ht
      iintro ⟨H, -⟩; iframe H
    · simp at hv ht
      iintro ⟨-, H⟩
      iapply opListAtC_get c vs ts i v t hv ht $$ H

/-- The lists of trees of an appended slice. -/
theorem opListAtC_append (c : Bool) :
    ∀ (vs1 vs2 : List go_etcd_io.etcd.client.v3.Op) (ts1 ts2 : List OpT),
      opListAtC (GF := GF) c vs1 ts1 ∗ opListAtC c vs2 ts2 ⊢ opListAtC c (vs1 ++ vs2) (ts1 ++ ts2)
  | [], vs2, [], ts2 => by simp only [List.nil_append, opListAtC]; iintro ⟨-, H⟩; iexact H
  | [], _, _ :: _, _ => by simp only [opListAtC]; iintro ⟨H, -⟩; iexfalso; iexact H
  | _ :: _, _, [], _ => by simp only [opListAtC]; iintro ⟨H, -⟩; iexfalso; iexact H
  | v :: vs1, vs2, t :: ts1, ts2 => by
    simp only [List.cons_append, opListAtC]
    iintro ⟨⟨H1, H2⟩, H3⟩
    iframe H1
    iapply opListAtC_append c vs1 vs2 ts1 ts2 $$ [$H2 $H3]

/-- Plain operations' `opsAt` as trees of plain operations (without the capacity flag). -/
theorem opsAt_opListAtC (sl : GoSlice) (os : List OpFull) (ops : List TxnOp)
    (h : os.map txnOpOf = ops.map some) :
    opsAt (GF := GF) sl os ⊢ ∃ vs, sl ↦*□ vs ∗ opListAtC false vs (os.map OpT.leaf) := by
  iintro H
  ihave H' := opsAt_leaves sl os ops h $$ H
  unfold opsTAt
  iexact H'

/-- An `opsOwn` slice, read-only. -/
theorem opsOwn_opsAt (sl : GoSlice) (os : List OpFull) :
    opsOwn (GF := GF) sl os ⊢ opsAt sl os ∗ ownSliceCap go_etcd_io.etcd.client.v3.Op sl (DFrac.own 1) := by
  unfold opsOwn opsAt
  iintro ⟨%vs, #Hsl, Hcap, %Hlen, #H⟩
  iframe Hcap
  iexists vs
  iframe #
  ipureintro; exact Hlen

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

theorem cmpsSetAt_listRel (sl : GoSlice) (ms : List CmpModel) :
    cmpsSetAt (GF := GF) sl ms ⊣⊢ ∃ cs, sl ↦*□ cs ∗ listRel cmpSetAt cs ms := by
  unfold cmpsSetAt listRel; exact .rfl

theorem opsOwn_listRel (sl : GoSlice) (os : List OpFull) :
    opsOwn (GF := GF) sl os ⊣⊢ ∃ vs, sl ↦*□ vs ∗
      ownSliceCap go_etcd_io.etcd.client.v3.Op sl (DFrac.own 1) ∗ listRel opFullAt vs os := by
  unfold opsOwn listRel; exact .rfl

end defs

end EtcdGrove
end Perennial
