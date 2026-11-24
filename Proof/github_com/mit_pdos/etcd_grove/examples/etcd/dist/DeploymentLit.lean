/- Lean-first (no Rocq counterpart).

# `etcd/dist`: the deployment's composite literal evaluates

`deploymentLit d` (`TopLevelDefs.lean`), the Go composite literal every machine's boot program
evaluates, evaluates without panicking to a value `v` with `deploymentRepr v d`.

The generic part: an array literal, and a slice literal, whose elements are *expressions* (here
struct literals and inner slice literals), each with a WP, evaluate to the values of the elements
(`wp_arrayLit_exprs`, `wp_sliceLit_exprs`); Perennial's `pure_wp_array_lit` and `wp_slice_literal`
cover only elements that are already values, or a list of values fixed beforehand.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.Repr

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-! ## Array and slice literals of expressions -/

/-- The keyed element of an unkeyed array literal element `e` of type `t`. -/
def arrayLitKEe [GooseExts] (t : go.GoType) (e : Expr) : keyed_element :=
  KeyedElement none (ElementExpression t e)

theorem arrayLiteralSize_unkeyed [GooseExts] {A : Type} (t : go.GoType) (f : A → Expr) (es : List A) :
    go.arrayLiteralSize (es.map (fun x => arrayLitKEe t (f x))) = (es.length : Int) := by
  have h : ∀ (F : Int × Int → keyed_element → Int × Int),
      (∀ (a b : Int) (x : A), F (a, b) (KeyedElement none (ElementExpression t (f x))) = (a + 1, b)) →
      ∀ (es : List A) (i m : Int),
        List.foldl F (i, m) (es.map (fun x => KeyedElement none (ElementExpression t (f x)))) =
          (i + es.length, m) := by
    intro F hF es
    induction es with
    | nil => intro i m; simp
    | cons e es ih =>
      intro i m
      simp only [List.map_cons, List.foldl_cons, hF]
      rw [ih (i + 1) m]
      simp only [List.length_cons, Int.natCast_add, Int.natCast_one, Prod.mk.injEq, and_true]
      omega
  unfold go.arrayLiteralSize arrayLitKEe
  rw [h _ (fun _ _ _ => rfl) es 0 0]
  simp only
  omega

section lits
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The element `e` of an array literal of expressions, once the array so far is a value. -/
theorem wp_arrayLit_exprs_set_val {s : Stuckness} {E : CoPset} (n : Int) (t : go.GoType) {V : Type}
    (acc : List V) (e : Expr) (P : V → IProp GF) (i : Int)
    (he : ∀ Ψ : val → IProp GF, iprop(∀ v, P v -∗ Ψ #v) ⊢ WP e @ s; E {{ Ψ }})
    (Φ : val → IProp GF) :
    iprop(∀ v, P v -∗ Φ #(array.mk n (acc.set (sint.nat (W64 i)) v))) ⊢
      WP gl(ArraySet (Val #(array.mk n acc), (#(W64 i), Convert t t e))) @ s; E {{ Φ }} := by
  refine .trans ?_ (tac_wp_bind (K := [EctxItem.AppRCtx (Val (GoInstruction (GoInstruction.Convert t t))),
    EctxItem.PairRCtx #(W64 i) (isPanic_intoVal _),
    EctxItem.PairRCtx #(array.mk n acc) (isPanic_intoVal _),
    EctxItem.AppRCtx (Val (GoInstruction GoInstruction.ArraySet))]) .rfl)
  refine .trans ?_ (he _)
  show _ ⊢ iprop(∀ v, P v -∗
    WP gl(ArraySet (Val #(array.mk n acc), (#(W64 i), Convert t t (Val #v)))) @ s; E {{ Φ }})
  iintro H %v HP
  ispecialize H $$ %v HP
  wp_pures
  iexact H

/-- One element of an array literal of expressions: the array so far `e0`, then the element `e`
(left to right: a pair's left component first). -/
theorem wp_arrayLit_exprs_set {s : Stuckness} {E : CoPset} (n : Int) (t : go.GoType) {V : Type}
    (e0 e : Expr) (Q : List V → IProp GF) (P : V → IProp GF) (i : Int)
    (he0 : ∀ Ψ : val → IProp GF, iprop(∀ acc, Q acc -∗ Ψ #(array.mk n acc)) ⊢ WP e0 @ s; E {{ Ψ }})
    (he : ∀ Ψ : val → IProp GF, iprop(∀ v, P v -∗ Ψ #v) ⊢ WP e @ s; E {{ Ψ }})
    (Φ : val → IProp GF) :
    iprop(∀ acc v, Q acc -∗ P v -∗ Φ #(array.mk n (acc.set (sint.nat (W64 i)) v))) ⊢
      WP gl(ArraySet (e0, (#(W64 i), Convert t t e))) @ s; E {{ Φ }} := by
  refine .trans ?_ (tac_wp_bind (K := [EctxItem.PairLCtx (Pair (Val #(W64 i))
    (App (Val (GoInstruction (GoInstruction.Convert t t))) e)),
    EctxItem.AppRCtx (Val (GoInstruction GoInstruction.ArraySet))]) .rfl)
  refine .trans ?_ (he0 _)
  show _ ⊢ iprop(∀ acc, Q acc -∗
    WP gl(ArraySet (Val #(array.mk n acc), (#(W64 i), Convert t t e))) @ s; E {{ Φ }})
  iintro HΦ %acc HQ
  iapply (wp_arrayLit_exprs_set_val n t acc e P i he Φ)
  iintro %v HP
  iapply HΦ $$ HQ HP

/-- The steps of an array literal of expressions, from index `i` on, after the array so far `e0`. -/
theorem wp_arrayLit_exprs_fold {s : Stuckness} {E : CoPset} (n : Int) (t : go.GoType) {A V : Type}
    (f : A → Expr) (P : A → V → IProp GF)
    (hf : ∀ x (Ψ : val → IProp GF), iprop(∀ v, P x v -∗ Ψ #v) ⊢ WP (f x) @ s; E {{ Ψ }})
    (F : Int × Expr → keyed_element → Int × Expr)
    (hF : ∀ (i : Int) (e : Expr) (x : A), F (i, e) (arrayLitKEe t (f x)) =
      (i + 1, gl(ArraySet (e, (#(W64 i), Convert t t (f x)))))) :
    ∀ (xs : List A) (i : Int) (e0 : Expr) (Q : List V → IProp GF),
      (∀ Ψ : val → IProp GF, iprop(∀ acc, Q acc -∗ Ψ #(array.mk n acc)) ⊢ WP e0 @ s; E {{ Ψ }}) →
      ∀ Φ : val → IProp GF,
        iprop(∀ acc vs, Q acc -∗ ([∗list] x;v ∈ xs;vs, P x v) -∗
          Φ #(array.mk n (arrayLitSets acc i vs))) ⊢
        WP (List.foldl F (i, e0) (xs.map (fun x => arrayLitKEe t (f x)))).2 @ s; E {{ Φ }}
  | [], i, e0, Q, he0, Φ => by
    refine .trans ?_ (he0 Φ)
    iintro H %acc HQ
    iapply H $$ %acc %([] : List V) HQ
    iapply BigSepL2.bigSepL2_nil.2
    iempintro
  | x :: xs, i, e0, Q, he0, Φ => by
    simp only [List.map_cons, List.foldl_cons, hF]
    refine .trans ?_ (wp_arrayLit_exprs_fold n t f P hf F hF xs (i + 1) _
      (fun acc' => iprop(∃ acc v, ⌜acc' = acc.set (sint.nat (W64 i)) v⌝ ∗ Q acc ∗ P x v)) ?_ Φ)
    · iintro H %acc' %vs ⟨%acc, %v, %Heq, HQ, HP⟩ Hvs
      subst Heq
      iapply H $$ %acc %(v :: vs) HQ
      iapply BigSepL2.bigSepL2_cons.2
      iframe
    · intro Ψ
      refine .trans ?_ (wp_arrayLit_exprs_set n t e0 (f x) Q (P x) i he0 (hf x) Ψ)
      iintro H %acc %v HQ HP
      iapply H
      iexists acc, v
      iframe
      ipureintro; rfl

set_option goose.wp.unfoldSliceLiterals true in
/-- **A slice literal**, its array literal's elements chosen as it evaluates (Perennial's
`wp_slice_literal_nonnull` fixes them beforehand). -/
theorem wp_slice_literal_ex {s : Stuckness} {E : CoPset} {st t : go.GoType} {V : Type}
    [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V t] [st ↓u go.SliceType t]
    (kvs : List keyed_element) (Φ : val → IProp GF) :
    iprop(⌜go.arrayLiteralSize kvs < 2 ^ 63⌝ -∗
    WP (App (Val (GoInstruction (CompositeLiteral (go.ArrayType (go.arrayLiteralSize kvs) t))))
          (Val (LiteralValueV kvs))) @ s; E
      {{ v, ∃ l : List V, ⌜v = #(array.mk (go.arrayLiteralSize kvs) l)⌝ ∗
        (∀ sl_ptr : Loc, ⌜sl_ptr ≠ null⌝ -∗
          (slice.mk sl_ptr (W64 (go.arrayLiteralSize kvs)) (W64 (go.arrayLiteralSize kvs)) ↦* l ∗
            ownSliceCap V (slice.mk sl_ptr (W64 (go.arrayLiteralSize kvs))
              (W64 (go.arrayLiteralSize kvs))) (DFrac.own 1)) -∗
          Φ #(slice.mk sl_ptr (W64 (go.arrayLiteralSize kvs)) (W64 (go.arrayLiteralSize kvs)))) }}) ⊢
    WP (App (Val (GoInstruction (CompositeLiteral st))) (Val (LiteralValueV kvs))) @ s; E {{ Φ }} := by
  iintro HΦ
  wp_pures
  by_cases hlen : go.arrayLiteralSize kvs < 2 ^ 63
  · ispecialize HΦ $$ %hlen
    rw [ite_eq_left hlen]
    wp_pures
    wp_alloc_auto
    wp_pure
    wp_pure
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.ArrayType _ t)))) (Val (LiteralValueV kvs)))
    wp_apply_core wp_wand $$ HΦ
    iintro %v ⟨%l, %Hv, HΦ⟩
    subst Hv
    wp_auto
    have h0 : 0 ≤ go.arrayLiteralSize kvs := by
      unfold go.arrayLiteralSize; split; omega
    rw [ite_eq_left ⟨by decide, by word, by word⟩]
    have hz : W64 (go.arrayLiteralSize kvs) - W64 0 = W64 (go.arrayLiteralSize kvs) := by word
    simp only [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, hz]
    wp_pures
    ihave %Hlen := array_len _ _ _ _ $$ tmp
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ tmp
    iapply HΦ $$ %tmp_ptr %Hnn
    isplitl [tmp]
    · iapply slice_array tmp_ptr _ (array.mk (go.arrayLiteralSize kvs) l) (by simp only; omega)
      iexact tmp
    · iapply ownSliceCap_empty _ rfl (by simp only; word)
  · rw [ite_eq_right hlen]; iapply wp_AngelicExit

/-- **A slice literal of expressions** `[]t{f x₀, f x₁, ...}`: each element evaluates (left to right)
to a value related to its source by `P`; the slice owns the values. -/
theorem wp_sliceLit_exprs {s : Stuckness} {E : CoPset} {st t : go.GoType} {A V : Type}
    [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V t] [st ↓u go.SliceType t]
    (f : A → Expr) (P : A → V → IProp GF)
    (hf : ∀ x (Ψ : val → IProp GF), iprop(∀ v, P x v -∗ Ψ #v) ⊢ WP (f x) @ s; E {{ Ψ }})
    (xs : List A) (Φ : val → IProp GF) :
    iprop(∀ (sl : GoSlice) (vs : List V), sl ↦* vs -∗ ([∗list] x;v ∈ xs;vs, P x v) -∗ Φ #sl) ⊢
      WP (App (Val (GoInstruction (CompositeLiteral st)))
        (Val (LiteralValueV (xs.map (fun x => arrayLitKEe t (f x)))))) @ s; E {{ Φ }} := by
  refine .trans ?_ (wp_slice_literal_ex (V := V) _ Φ)
  rw [arrayLiteralSize_unkeyed]
  have he0 : ∀ Ψ : val → IProp GF,
      iprop(∀ acc, ⌜acc = List.replicate (xs.length : Int).toNat (zero_val V)⌝ -∗
        Ψ #(array.mk (xs.length : Int) acc)) ⊢
        WP (GoZeroVal (go.ArrayType (xs.length : Int) t) #() : Expr) @ s; E {{ Ψ }} := by
    intro Ψ
    iintro H
    wp_pures
    iapply H
    ipureintro; rfl
  iintro H %hlen
  iapply (wp_arrayLit_exprs_fold (xs.length : Int) t f P hf _ (fun _ _ _ => rfl) xs 0 _ _ he0)
  iintro %acc %vs %Hacc Hvs
  ihave %Hl := BigSepL2.bigSepL2_length $$ Hvs
  subst Hacc
  have hsets : arrayLitSets (List.replicate (xs.length : Int).toNat (zero_val V)) 0 vs = vs := by
    have := arrayLitSets_eq (zero_val V) vs [] (xs.length : Int).toNat (by omega) (by simp; omega)
    simp only [List.nil_append, List.length_nil, Int.natCast_zero] at this
    rw [this]; simp [← Hl]
  rw [hsets]
  iexists vs
  isplitr
  · ipureintro; rfl
  iintro %sl_ptr %_ ⟨Hsl, -⟩
  iapply H $$ Hsl Hvs

/-- A list related element-wise to the images of another list is that image. -/
theorem bigSepL2_eq_map {A B : Type} (g : A → B) :
    ∀ (xs : List A) (vs : List B), ([∗list] x;v ∈ xs;vs, ⌜v = g x⌝ : IProp GF) ⊢ ⌜vs = xs.map g⌝
  | [], vs => by
    iintro H
    ihave %Hl := BigSepL2.bigSepL2_length $$ H
    ipureintro
    simp only [List.length_nil] at Hl
    simp [List.eq_nil_of_length_eq_zero Hl.symm]
  | x :: xs, vs => by
    iintro H
    ihave %Hl := BigSepL2.bigSepL2_length $$ H
    match vs, Hl with
    | v :: vs, _ =>
      ihave ⟨%Hv, H⟩ := BigSepL2.bigSepL2_cons.1 $$ H
      ihave %Hvs := bigSepL2_eq_map g xs vs $$ H
      ipureintro
      simp [Hv, Hvs]

end lits

/-! ## The deployment's literal -/

namespace EtcdGrove
namespace etcd_dist

open github_com.mit_pdos.etcd_grove.examples.etcd.dist

section exprs
variable [GooseExts] [GoGlobalContext]

/-- A member's struct literal (`deploymentLit`'s element of `Members`). -/
def memberLitE (m : Member) : Expr :=
  App (Val (GoInstruction (CompositeLiteral deployment.Member.ty))) (LiteralValue
    [KeyedElement (some (KeyField go!"Name")) (ElementExpression go.string (Val #m.name)),
     KeyedElement (some (KeyField go!"Peer")) (ElementExpression go.string (Val #m.peer)),
     KeyedElement (some (KeyField go!"Client")) (ElementExpression go.string (Val #m.client))])

/-- A workload's struct literal (`deploymentLit`'s element of `Workloads`). -/
def workloadLitE (w : Workload) : Expr :=
  App (Val (GoInstruction (CompositeLiteral deployment.Workload.ty))) (LiteralValue
    [KeyedElement (some (KeyField go!"Kind")) (ElementExpression deployment.Kind.ty (Val #w.kind)),
     KeyedElement (some (KeyField go!"Clients")) (ElementExpression go.int (Val #w.clients)),
     KeyedElement (some (KeyField go!"Ops")) (ElementExpression go.int (Val #w.ops))])

/-- A workload's client machines' addresses, as a slice literal (`deploymentLit`'s element of
`Nodes`). -/
def nodesLitE (ns : List GoString) : Expr :=
  App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.string)))) (LiteralValue
    (ns.map (fun n => arrayLitKEe go.string (Val #n))))

end exprs

section lit
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : deployment.Assumptions]

theorem wp_memberLitE {s : Stuckness} {E : CoPset} (m : Member) (Ψ : val → IProp GF) :
    iprop(∀ v : deployment.Member, ⌜v = m.val⌝ -∗ Ψ #v) ⊢ WP (memberLitE m) @ s; E {{ Ψ }} := by
  iintro H
  unfold memberLitE
  wp_pures
  iapply H
  ipureintro; rfl

theorem wp_workloadLitE {s : Stuckness} {E : CoPset} (w : Workload) (Ψ : val → IProp GF) :
    iprop(∀ v : deployment.Workload, ⌜v = w.val⌝ -∗ Ψ #v) ⊢ WP (workloadLitE w) @ s; E {{ Ψ }} := by
  iintro H
  unfold workloadLitE
  wp_pures
  iapply H
  ipureintro; rfl

theorem wp_nodesLitE {s : Stuckness} {E : CoPset} (ns : List GoString) (Ψ : val → IProp GF) :
    iprop(∀ sl : GoSlice, sl ↦*□ ns -∗ Ψ #sl) ⊢ WP (nodesLitE ns) @ s; E {{ Ψ }} := by
  iintro H
  unfold nodesLitE
  wp_pure
  iapply (wp_sliceLit_exprs (V := GoString) (t := go.string) (fun n => Val #n)
    (fun n v => iprop(⌜v = n⌝)) (fun n Ψ' => by iintro H'; wp_pures; iapply H'; ipureintro; rfl) ns)
  iintro %sl %vs Hsl Hvs
  ihave %Hvs := bigSepL2_eq_map id ns vs $$ Hvs
  rw [List.map_id] at Hvs
  subst Hvs
  imod (ownSlice_persist _ _ _) $$ Hsl with Hsl
  iapply H $$ Hsl

/-- **The deployment's literal evaluates**: `deploymentLit d` evaluates, without panicking, to a Go
value holding `d` (`deploymentRepr`, persistent). -/
theorem wp_deploymentLit {s : Stuckness} {E : CoPset} (d : Deployment) (Φ : val → IProp GF) :
    iprop(∀ v : deployment.Deployment, deploymentRepr v d -∗ Φ #v) ⊢
      WP (deploymentLit d) @ s; E {{ Φ }} := by
  iintro HΦ
  simp only [deploymentLit]
  wp_pures
  trace_state
  sorry

end lit

end etcd_dist
end EtcdGrove

end Perennial
