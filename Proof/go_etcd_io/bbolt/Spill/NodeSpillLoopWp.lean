/-
`node.spill`'s children's loop (U9k, `notes/bbolt-proof-plan.md`):
`for i := 0; i < len(n.children); i++ { if err := n.children[i].spill(); err != nil { return err } }`
as a wp lemma (`spill_loop_wp`) over the loop's invariant `spLoop` (`Spill/NodeSpillLoop`), taking
the recursion's hypothesis (`spillIH`, the Löb hypothesis of `node__spill.lean`'s `wp_aux`, whose
`spillW` has the same body) later and persistent; and the loop over no children
(`spill_loop_nil_wp`, a leaf).

The loop's code (`spCondE`, `spBodyE`, `spPostE`) is `node.spill.impl`'s, its variables `n`, `i`
and `$res0` substituted by their cells, as `wp_auto` leaves it at the `doFor` (`spLoopE`). The
interfaces (for the assembly):

* `spill_loop_wp K tx r m X0 w0 bl n r0 O lo hi h D0 N0 E0 es0 n_ptr i_ptr res_ptr e0 Φ hl0 :
    □ ▷ spillIH ∗ wtxW K tx r m X0 ∗ wdbW K tx X0.v w0 ∗ n_ptr ↦ n ∗ i_ptr ↦ W64 0 ∗
      res_ptr ↦ e0 ∗ (∀ v, spLoopPost … v -∗ Φ v) ⊢ WP (spLoopE n_ptr i_ptr res_ptr) {{ Φ }}`
  for `hl0 : spLoop X0 w0 bl n r0 O lo hi h D0 N0 E0 X0 w0 r0 es0 0 [] []` (`spLoop_start`
  after the sort); `spLoopPost` is the loop's end (`executeVal`, `spLoop` at the final index past
  the children: `spLoop_fin` applies) or a child's error (`returnVal #()`, the error in
  `$res0`, `spPost`'s error facts relative to `(X0, w0)`).
* `spill_loop_nil_wp … (hn : X.node bl n = some rn) (hl : n ∈ X.live) (h0 : rn.cs = []) :
    wtxW K tx r m X ∗ n_ptr ↦ n ∗ i_ptr ↦ W64 0 ∗
      (wtxW K tx r m X -∗ n_ptr ↦ n -∗ i_ptr ↦ W64 0 -∗ Φ executeVal) ⊢
      WP (spLoopE n_ptr i_ptr res_ptr) {{ Φ }}`.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillChild
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillHeap
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillPiecesCode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section code
variable [GooseExts] [go_gctx : GoGlobalContext]

/-- The loop's condition, `i < len(n.children)`. -/
def spCondE (n_ptr i_ptr : Loc) : Expr :=
  (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Val #i_ptr)) (Let "$a0" (App (Val (GoInstruction (GoLoad nodes.ty))) (App (Val (GoInstruction (StructFieldRef node.ty go!"children"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #n_ptr))))
    (App (App (Val (GoInstruction (FuncResolve go.len [nodes.ty]))) (Val #())) (Var "$a0")))))

/-- The loop's body, `if err := n.children[i].spill(); err != nil { return err }`. -/
def spBodyE (n_ptr i_ptr res_ptr : Loc) : Expr :=
  (Let "$r0" (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType node.ty) go!"spill"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (App (Val (GoInstruction (IndexRef nodes.ty))) (Pair (App (Val (GoInstruction (GoLoad nodes.ty))) (App (Val (GoInstruction (StructFieldRef node.ty go!"children"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #n_ptr)))) (App (Val (GoInstruction (GoLoad go.int))) (Val #i_ptr)))))) (Val #()))
    (Let "err" (App (Val (GoInstruction (GoAlloc go.error))) (App (Val (GoInstruction (GoZeroVal go.error))) (Val #())))
    (App (App (Val exceptionSeq) (Lam BAnon
    (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.error))) (Pair (App (Val (GoInstruction (GoLoad go.error))) (Var "err")) (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil))))))
    (Let "$r0" (App (Val (GoInstruction (GoLoad go.error))) (Var "err"))
    (App (App (Val exceptionSeq) (Lam BAnon
    (App (Val doReturn)
    (Val #()))))
    (App (Val doExecute)
    (App (Val (GoInstruction (GoStore go.error))) (Pair (Val #res_ptr) (Var "$r0"))))))
    (App (Val doExecute)
    (Val #())))))
    (App (Val doExecute)
    (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "err") (Var "$r0")))))))

/-- The loop's post statement, `i++`. -/
def spPostE (i_ptr : Loc) : Expr :=
  (App (Val doExecute)
    (App (Val (GoInstruction (GoStore go.int))) (Pair (Val #i_ptr) (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Val #i_ptr)) (Val #(W64 1)))))))

/-- **The children's loop** at its `doFor`. -/
def spLoopE (n_ptr i_ptr res_ptr : Loc) : Expr :=
  App (App (App (Val doFor) (Val (LamV BAnon (spCondE n_ptr i_ptr))))
    (Val (LamV BAnon (spBodyE n_ptr i_ptr res_ptr)))) (Val (LamV BAnon (spPostE i_ptr)))

end code

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **The children's loop's end** (see the module doc): every child spilled (the loop's
invariant past the children), or a child's error (`spPost`'s error facts from `(X0, w0)`, the
error in `$res0`). -/
def spLoopPost (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X0 : WX) (w0 : WDb) (bl n : Loc)
    (r0 : NRec) (O : List Nat) (lo hi : Option (List w8)) (h : Nat) (D0 : List Nat)
    (N0 : List Loc) (E0 : List El) (n_ptr i_ptr res_ptr : Loc) (e0 : GoInterface) (v : val) :
    IProp GF :=
  iprop((⌜v = executeVal⌝ ∗ n_ptr ↦ n ∗ res_ptr ↦ e0 ∗
      ∃ (j : w64) (X' : WX) (w' : WDb) (r' : NRec) (es : List UE) (st : List FLStep)
        (T : List Loc), i_ptr ↦ j ∗ wtxW K tx r m X' ∗ wdbW K tx X'.v w' ∗
        ⌜spLoop X0 w0 bl n r0 O lo hi h D0 N0 E0 X' w' r' es (sint.nat j) st T ∧
          r'.cs.length ≤ sint.nat j⌝) ∨
    (⌜v = returnVal #()⌝ ∗ n_ptr ↦ n ∗ (∃ j : w64, i_ptr ↦ j) ∗
      ∃ err : GoInterface, res_ptr ↦ err ∗ ⌜err ≠ interface.nil⌝ ∗ fmtErrorOk err ∗
      ∃ (X' : WX) (w' : WDb) (st : List FLStep),
        ⌜spErr X0 X' w0 w' st⌝ ∗
        ((wtxW K tx r m X' ∗ wdbW K tx X'.v w') ∨ (wtxLost K tx r m X' ∗ wdbLost K tx X'.v w'))))

/-- **The children's loop** (see the module doc). -/
theorem spill_loop_wp (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X0 : WX) (w0 : WDb)
    (bl n : Loc) (r0 : NRec) (O : List Nat) (lo hi : Option (List w8)) (h : Nat)
    (D0 : List Nat) (N0 : List Loc) (E0 : List El) (es0 : List UE) (n_ptr i_ptr res_ptr : Loc)
    (e0 : GoInterface) (P : IProp GF) (Φ : val → IProp GF)
    (hl0 : spLoop X0 w0 bl n r0 O lo hi h D0 N0 E0 X0 w0 r0 es0 0 [] [])
    (hfc0 : ∀ y ∈ w0.fl.free, ¬ coversSlot w0.C.pages y.toNat)
    (hts0 : ∀ s ∈ treeSlots w0.C, s < X0.t.mv.pgid'.toNat) :
    (□ ▷ spillIH (GF := GF)) ∗ wtxW K tx r m X0 ∗ wdbW K tx X0.v w0 ∗ poolR K.B.bq K.N P ∗ n_ptr ↦ n ∗
      i_ptr ↦ W64 0 ∗ res_ptr ↦ e0 ∗
      (∀ v, poolR K.B.bq K.N P -∗ spLoopPost K tx r m X0 w0 bl n r0 O lo hi h D0 N0 E0 n_ptr i_ptr res_ptr e0 v -∗ Φ v) ⊢
      WP (spLoopE n_ptr i_ptr res_ptr) {{ Φ }} := by
  unfold spillIH spLoopE spCondE spBodyE spPostE
  iintro ⟨#IH, Hw, Hdb, HR, Hn, Hi, Hres, HΦ⟩
  ihave HI : iprop(∃ (j : w64) (X' : WX) (w' : WDb) (r' : NRec) (es : List UE)
      (st : List FLStep) (T : List Loc),
      "Hi" ∷ i_ptr ↦ j ∗ "Hw" ∷ wtxW K tx r m X' ∗ "Hdb" ∷ wdbW K tx X'.v w' ∗ "HR" ∷ poolR K.B.bq K.N P ∗
      "%Hl" ∷ ⌜spLoop X0 w0 bl n r0 O lo hi h D0 N0 E0 X' w' r' es (sint.nat j) st T ∧
        0 ≤ sint.Z j⌝) $$ [Hi Hw Hdb HR]
  · iexists W64 0, X0, w0, r0, es0, [], []
    iframe
    ipureintro; exact ⟨hl0, by word⟩
  wp_for HI
  obtain ⟨Hl, Hj0⟩ := Hl
  have hrn := Hl.br.node
  have hlv := Hl.live
  icases wtxW_children_acc K tx r m X' bl n r' hrn hlv $$ Hw with ⟨Hnv, Hch, Hwb⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hnv with ⟨Hnv, %Hnn⟩
  ihave %Hcl := ownSlice_len _ _ _ $$ Hch
  iStructNamed Hnv
  wp_auto
  ihave Hnv : (n ↦ r'.nv : IProp GF)
    $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  ihave Hw := Hwb $$ [Hnv Hch]
  · iframe
  by_cases hlt : sint.Z j < sint.Z r'.nv.children'.len
  · simp only [decide_eq_true hlt, ite_true, decide_true]
    have hjn : sint.nat j < r'.cs.length := by
      have h1 : (sint.Z j).toNat < (sint.Z r'.nv.children'.len).toNat := by omega
      rw [Hcl.1]; exact h1
    obtain ⟨c, hc⟩ : ∃ c, r'.cs[sint.nat j]? = some c := ⟨_, List.getElem?_eq_getElem hjn⟩
    icases wdbW_ofC K tx X'.v w' $$ Hdb with ⟨Hdb, %Hvc⟩
    obtain ⟨rc, O', lo', hi', h', F', D', N', E', cs', hrc, hpre, hnext⟩ := spLoop_next Hl hc Hnn Hvc hfc0 hts0
    icases wtxW_children_acc K tx r m X' bl n r' hrn hlv $$ Hw with ⟨Hnv, Hch, Hwb⟩
    iStructNamed Hnv
    wp_auto
    simp only [Hj0, hlt, _root_.and_self, ite_true]
    wp_apply wp_load_slice_index r'.nv.children' (sint.Z j) r'.cs (DFrac.own 1) c Hj0 $$ [Hch] as Hch
    · iframe; ipureintro; exact hc
    ihave Hnv : (n ↦ r'.nv : IProp GF)
      $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ihave Hw := Hwb $$ [Hnv Hch]
    · iframe
    wp_apply IH $$ %K %tx %r %m %X' %w' %bl %c %rc %O' %lo' %hi' %h' %F' %D' %N' %E' %cs' %P %hpre
      [Hw Hdb HR] as %err ⟨HR, Hpost⟩
    · iframe
    iunfold spPost at Hpost
    icases Hpost with (⟨%Herr, %X'', %w'', %st', Hw, Hdb, %Hd⟩ |
      ⟨%Herr, #Hok, %X'', %w'', %st', %He, Hst⟩)
    · subst Herr
      wp_auto
      wp_for_post
      obtain ⟨r'', es', T', hl'⟩ := hnext X'' w'' st' Hd
      have hlen := Hcl.2
      have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by
        have : sint.Z (j + W64 1) = sint.Z j + 1 := by word
        show (sint.Z (j + W64 1)).toNat = (sint.Z j).toNat + 1
        omega
      have hj2 : 0 ≤ sint.Z (j + W64 1) := by word
      iframe
      iexists j + W64 1, X'', w'', r'', es', st ++ st', T'
      rw [hj1]
      iframe
      ipureintro; exact ⟨hl', hj2⟩
    · cases err with
      | nil => exact absurd rfl Herr
      | ok ei =>
        wp_auto
        wp_for_post
        iapply HΦ $$ HR
        unfold spLoopPost
        iright
        isplitr
        · ipureintro; rfl
        iframe Hn
        isplitl [Hi]
        · iexists j; iexact Hi
        iexists GoInterface.ok ei
        iframe Hres Hok
        isplitr
        · ipureintro; exact Herr
        iexists X'', w'', st ++ st'
        iframe Hst
        ipureintro; exact spLoop_err Hl He
  · simp only [decide_eq_false hlt]
    cleanup_bool_decide
    iapply HΦ $$ HR
    unfold spLoopPost
    ileft
    isplitr
    · ipureintro; rfl
    iframe Hn Hres
    iexists j, X', w', r', es, st, T
    iframe Hi Hw Hdb
    ipureintro
    refine ⟨Hl, ?_⟩
    have h1 : (sint.Z r'.nv.children'.len).toNat ≤ (sint.Z j).toNat := by omega
    rw [Hcl.1]; exact h1

/-- **The children's loop over no children** (a leaf): it ends at once. -/
theorem spill_loop_nil_wp (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl n : Loc)
    (rn : NRec) (n_ptr i_ptr res_ptr : Loc) (Φ : val → IProp GF)
    (hn : X.node bl n = some rn) (hl : n ∈ X.live) (h0 : rn.cs = []) :
    wtxW (GF := GF) K tx r m X ∗ n_ptr ↦ n ∗ i_ptr ↦ W64 0 ∗
      (wtxW K tx r m X -∗ n_ptr ↦ n -∗ i_ptr ↦ W64 0 -∗ Φ executeVal) ⊢
      WP (spLoopE n_ptr i_ptr res_ptr) {{ Φ }} := by
  unfold spLoopE spCondE spBodyE spPostE
  iintro ⟨Hw, Hn, Hi, HΦ⟩
  wp_for
  icases wtxW_children_acc K tx r m X bl n rn hn hl $$ Hw with ⟨Hnv, Hch, Hwb⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hnv with ⟨Hnv, %Hnn⟩
  ihave %Hcl := ownSlice_len _ _ _ $$ Hch
  iStructNamed Hnv
  wp_auto
  ihave Hnv : (n ↦ rn.nv : IProp GF)
    $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  ihave Hw := Hwb $$ [Hnv Hch]
  · iframe
  have hlt : ¬ sint.Z (W64 0) < sint.Z rn.nv.children'.len := by
    have h1 := Hcl.1
    rw [h0] at h1
    have h2 : (sint.Z rn.nv.children'.len).toNat = 0 := h1.symm
    have h3 : sint.Z (W64 0) = 0 := by word
    omega
  simp only [decide_eq_false hlt]
  cleanup_bool_decide
  iapply HΦ $$ Hw Hn Hi

end proof

end Spill

end bbolt
end EtcdGrove
end Perennial
