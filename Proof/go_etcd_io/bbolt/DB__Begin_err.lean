/-
The proof of `Spec/go_etcd_io/bbolt/DB__Begin_err.lean` (U5, `notes/bbolt-proof-plan.md`; design
§3.13): the logger (`dbFixed`'s), compared with `discardLogger`; if it is not, a debug line and a
deferred line of the outcome (`%v` of the error: `beginErr_fmtErrorOk`); then `beginRWTx` or the
pool-loan `beginTx`.
-/
module

public import Spec.go_etcd_io.bbolt.DB__Begin_err
public import Proof.go_etcd_io.bbolt.DB__beginTx
public import Proof.go_etcd_io.bbolt.DB__beginRWTx
public import Proof.go_etcd_io.bbolt.Mmap.Logger
import all Spec.go_etcd_io.bbolt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common
open _root_.Perennial.fmt

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

omit hos in
/-- **`lg != discardLogger`** (batch 34). Go's interface comparison panics on equal uncomparable
dynamic types; the model compares the dynamic types, then (equal) checks comparability and uses the
type's own `==` (`Interface.lean`'s `go_eq_interface`). `discardLogger` holds a `*nopLogger`
(bbolt's package facts, `bboltRootInit_discard`), so the types differ, or both are pointers and
`lg`'s value is a location (`logPtrTyped`, `dbFixed`'s). -/
theorem wp_logger_ne_discard (lg : GoInterface) (hty : logPtrTyped lg) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ boltLogger lg }}
      (App (Val (GoInstruction (Convert go.untypedBool go.bool)))
        (App (Val (GoInstruction (GoUnOp GoNot go.bool)))
          (App (Val (GoInstruction (GoOp GoEquals Logger.ty)))
            (Pair (Val #lg) (App (Val (GoInstruction (GoLoad Logger.ty)))
              (Val #(globalAddr discardLogger)))))))
    {{ (b : Bool), RET #b; True }} := by
  wp_start as -
  ihave #Hpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt $$ []
  · iPkgInit
  icases bboltRootInit_discard $$ Hpkg with ⟨%l, #Hd⟩
  wp_auto
  cases lg with
  | nil =>
    simp only [interface.mkOk]
    wp_auto
    iapply HΦ; itrivial
  | ok ii =>
    simp only [interface.mkOk]
    by_cases h : ii.ty = go.GoType.PointerType nopLogger.ty
    · obtain ⟨l', hl⟩ := hty ii rfl _ h
      rw [if_pos h, h, hl]
      wp_auto
      iapply HΦ; itrivial
    · rw [if_neg h]
      wp_auto
      iapply HΦ; itrivial

omit package_sem in
/-- A reader's registration, out of its `rdTxK` (what `txDB` needs). -/
theorem rdTxK_reg (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) :
    rdTxK (GF := GF) K tx src q T v ⊢ rdTxK K tx src q T v ∗
      ∃ r : TxReg, reg tx K.B r ∗ ⌜r.db = K.db⌝ := by
  unfold rdTxK
  iintro ⟨%r, %c, %mv, %k, %Hc, #Hreg, H⟩
  isplitl [H]
  · iexists r, c, mv, k; iframe Hreg H; ipureintro; exact Hc
  · iexists r; iframe Hreg; ipureintro; exact Hc.2.1

private instance BC_full_persistent_be (K : BC) : Persistent (K.full (GF := GF)) := by
  unfold BC.full isBoltP; infer_instance

omit package_sem in
/-- **A new pool-loan reader is a `boltTx`** of its database, and `txDB`. -/
theorem rdTxK_boltTx (K : BC) (tx : Loc) (T : TxView) (v : View) (hro : T.rw = false) :
    K.full (GF := GF) ∗ rdTxK K tx .loan 1 T v ⊢
      txDBDef K.B K.N tx K.db ∗ boltTxDef K.B K.N tx 1 T := by
  iintro ⟨#Hfull, Hrd⟩
  icases rdTxK_reg K tx .loan 1 T v $$ Hrd with ⟨Hrd, %r, #Hreg, %Hr⟩
  isplitl []
  · unfold txDBDef
    iexists r
    iframe Hreg
    isplitl []
    · unfold isBoltDef; iexists K.p, K.sp, K.t0; unfold BC.full; iexact Hfull
    · ipureintro; exact Hr
  iapply (boltTx_rdTx K.B K.N tx 1 T hro).2
  iexists K.db
  isplitl [Hrd]
  · iapply (rdTx_rdTxK K.B K.N tx .loan 1 T).2
    iexists K, v
    iframe Hrd
    ipureintro; exact ⟨rfl, rfl⟩
  · unfold isBoltDef; iexists K.p, K.sp, K.t0; unfold BC.full; iexact Hfull

omit hos package_sem in
/-- A `bool` is an argument `fmt` formats with no method. -/
private theorem logArgOk_bool [go.bool ↓u go.bool] (R : IProp GF) (v : w8) (b : Bool) :
    ⊢ logArgOk (GF := GF) R v (interface.mkOk go.bool #b) := by
  unfold interface.mkOk
  apply logArgOk_of_argWf
  have hb : ¬ _root_.Perennial.fmt.IsIntType go.bool := by
    simp [_root_.Perennial.fmt.IsIntType, go.bool, go.int, go.int64, go.int32, go.int16,
      go.int8, go.uint, go.uint64, go.uint32, go.uint16, go.uint8]
  refine ⟨fun h => absurd h (by simp [go.bool, go.string]), fun h => absurd h ?_,
    Or.inl (Or.inr (Or.inl rfl))⟩
  rintro (hi | ⟨hi, -⟩)
  · exact hb hi
  · rw [go.is_underlying] at hi; exact hb hi

theorem DB.Begin_err.wp_proof (wp_beginTx : DB.beginTx.spec (GF := GF) (hG := hG))
    (wp_beginRWTx : DB.beginRWTx.spec (GF := GF) (hG := hG)) :
    DB.Begin_err.spec (GF := GF) (hG := hG) := by
  intro db γ w Q
  wp_start as ⟨#Hdb, Hpre⟩
  ihave #Hdb' : isBoltDef (bnsOf γ.gs) γ.ns db $$ []
  · unfold isBolt; iexact Hdb
  unfold isBoltDef
  icases Hdb' with ⟨%p, %sp, %t0, #HbP⟩
  ihave #Hcore' : isBoltCoreP (bnsOf γ.gs) γ.ns db p sp t0 $$ []
  · unfold isBoltP; icases HbP with ⟨$, -⟩
  unfold isBoltCoreP
  icases Hcore' with ⟨#Hdbl, #Ht0, %Ht0, #Hpkg, #Hos, #Hfix, -⟩
  ihave #Hfix' := Hfix
  iunfold dbFixed at Hfix'
  icases Hfix' with ⟨-, -, ⟨%lg, #Hlg, #Hlgok⟩, -⟩
  ihave %Hlgty := dbFixed_logPtrTyped _ _ db sp lg $$ Hfix Hlg
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply DB.Logger.wp_proof db lg Ht0.2.1 $$ []
  · iframe #; unfold dbLogger; iexact Hlgok
  try wp_auto
  wp_bind (App (Val (GoInstruction (Convert go.untypedBool go.bool))) _)
  wp_apply wp_logger_ne_discard lg Hlgty $$ [] as %bl -
  · iframe #; unfold dbLogger; iexact Hlgok
  ihave #HK : BC.full (GF := GF) ⟨bnsOf γ.gs, γ.ns, db, p, sp, t0⟩ $$ []
  · unfold BC.full; iexact HbP
  ihave #Hep : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.errors $$ []
  · iPkgInit
  unfold boltState txDB boltTx
  cases bl
  · -- the logger is `discardLogger`: no logging
    wp_auto
    cases w
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hpre with ⟨Htt, Hau⟩
      try wp_auto
      wp_apply wp_beginTx ⟨bnsOf γ.gs, γ.ns, db, p, sp, t0⟩ Q $$ [Htt Hau] as %tx %err Hpost
      · iframe #; iframe
      try wp_auto
      iapply HΦ
      icases Hpost with (⟨%He, %b, %C, Hrd, HQ⟩ | ⟨%Htx, #Herr, Htt, Hau⟩)
      · ileft
        icases rdTxK_boltTx _ tx (TxView.ro (treeData C)) _ rfl $$ [Hrd] with ⟨#Hd, Ht⟩
        · iframe #; iframe
        isplitr
        · ipureintro; exact He
        iframe Hd
        iexists treeData C; iframe
      · iright
        ihave #Hfe := beginErr_fmtErrorOk err $$ [Hep Herr]
        · iframe #
        unfold beginErr
        icases Herr with ⟨%Hne, -⟩
        isplitr
        · ipureintro; exact ⟨Hne, Htx⟩
        iframe
        try iexact Hfe
    · simp only [↓reduceIte]
      try wp_auto
      wp_apply wp_beginRWTx ⟨bnsOf γ.gs, γ.ns, db, p, sp, t0⟩ $$ [] as %tx %err Hpost
      · iframe #
      try wp_auto
      iapply HΦ
      icases Hpost with (⟨%He, #Hd, %D, Ht⟩ | ⟨%Htx, #Herr⟩)
      · ileft
        isplitr
        · ipureintro; exact He
        iframe Hd
        iexists D; iexact Ht
      · iright
        ihave #Hfe := beginErr_fmtErrorOk err $$ [Hep Herr]
        · iframe #
        unfold beginErr
        icases Herr with ⟨%Hne, -⟩
        isplitr
        · ipureintro; exact ⟨Hne, Htx⟩
        iframe
        try iexact Hfe
  · -- not `discardLogger`: a debug line now, a line of the outcome deferred
    cases lg with
    | nil => iexfalso; unfold dbLogger boltLogger; iexact Hlgok
    | ok li =>
    ihave #Hlgok' : boltLogger (GF := GF) (.ok li) $$ []
    · unfold dbLogger; iexact Hlgok
    iclear Hlgok
    irename Hlgok' => Hlgok
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    try wp_auto
    wp_apply wp_boltLog li _ _ [W8 116] _ [interface.mkOk go.bool #w] _ iprop(True) _ (by decide) (by decide) rfl
      $$ Hlgok [Hsl] [] [] as Hsl -
    · iframe
    · try simp only [List.zip_cons_cons, List.zip_nil_left, BigSepL.bigSepL_cons, BigSepL.bigSepL_nil]
      isplitl
      · iapply logArgOk_bool
      · iempintro
    try wp_auto
    cases w
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hpre with ⟨Htt, Hau⟩
      try wp_auto
      wp_apply wp_beginTx ⟨bnsOf γ.gs, γ.ns, db, p, sp, t0⟩ Q $$ [Htt Hau] as %tx %err Hpost
      · iframe #; iframe
      try wp_auto
      icases Hpost with (⟨%He, %b, %C, Hrd, HQ⟩ | ⟨%Htx, #Herr, Htt, Hau⟩)
      · -- success: the debug line
        subst He
        wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl2 ⟨Hsl2, -⟩
        try wp_auto
        wp_apply wp_boltLog li _ _ [W8 116] _ [interface.mkOk go.bool #false] _ iprop(True) _ (by decide) (by decide) rfl
          $$ Hlgok [Hsl2] [] [] as Hsl2 -
        · iframe
        · try simp only [List.zip_cons_cons, List.zip_nil_left, BigSepL.bigSepL_cons, BigSepL.bigSepL_nil]
          isplitl
          · iapply logArgOk_bool
          · iempintro
        try wp_auto
        iapply HΦ
        ileft
        icases rdTxK_boltTx _ tx (TxView.ro (treeData C)) _ rfl $$ [Hrd] with ⟨#Hd, Ht⟩
        · iframe #; iframe
        isplitr
        · ipureintro; rfl
        iframe Hd
        iexists treeData C; iframe
      · -- an error: the error line
        ihave #Hfe := beginErr_fmtErrorOk err $$ [Hep Herr]
        · iframe #
        unfold beginErr
        icases Herr with ⟨%Hne, -⟩
        obtain ⟨ii, rfl⟩ : ∃ ii, err = GoInterface.ok ii := by
          cases err with
          | nil => exact absurd rfl Hne
          | ok ii => exact ⟨ii, rfl⟩
        wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl2 ⟨Hsl2, -⟩
        try wp_auto
        simp only [show sint.nat (W64 (0 + 1)) = 1 from rfl, List.set_cons_succ, List.set_cons_zero]
        wp_apply wp_boltLog li _ _ [W8 116, W8 118] _ [interface.mkOk go.bool #false, GoInterface.ok ii] _ iprop(True) _ (by decide) (by decide) rfl
          $$ Hlgok [Hsl2] [] [] as Hsl2 -
        · iframe
        · try simp only [List.zip_cons_cons, List.zip_nil_left, BigSepL.bigSepL_cons, BigSepL.bigSepL_nil]
          isplitl []
          · iapply logArgOk_bool
          isplitl []
          · iapply logArgOk_of_fmtErrorOk _ _ (by simp [methodVerbs]) (GoInterface.ok ii) $$ Hfe
          · iempintro
        try wp_auto
        iapply HΦ
        iright
        isplitr
        · ipureintro; exact ⟨Hne, Htx⟩
        iframe
        try iexact Hfe
    · simp only [↓reduceIte]
      try wp_auto
      wp_apply wp_beginRWTx ⟨bnsOf γ.gs, γ.ns, db, p, sp, t0⟩ $$ [] as %tx %err Hpost
      · iframe #
      try wp_auto
      icases Hpost with (⟨%He, #Hd, %D, Ht⟩ | ⟨%Htx, #Herr⟩)
      · -- success: the debug line
        subst He
        wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl2 ⟨Hsl2, -⟩
        try wp_auto
        wp_apply wp_boltLog li _ _ [W8 116] _ [interface.mkOk go.bool #true] _ iprop(True) _ (by decide) (by decide) rfl
          $$ Hlgok [Hsl2] [] [] as Hsl2 -
        · iframe
        · try simp only [List.zip_cons_cons, List.zip_nil_left, BigSepL.bigSepL_cons, BigSepL.bigSepL_nil]
          isplitl
          · iapply logArgOk_bool
          · iempintro
        try wp_auto
        iapply HΦ
        ileft
        isplitr
        · ipureintro; rfl
        iframe Hd
        iexists D; iexact Ht
      · -- an error: the error line
        ihave #Hfe := beginErr_fmtErrorOk err $$ [Hep Herr]
        · iframe #
        unfold beginErr
        icases Herr with ⟨%Hne, -⟩
        obtain ⟨ii, rfl⟩ : ∃ ii, err = GoInterface.ok ii := by
          cases err with
          | nil => exact absurd rfl Hne
          | ok ii => exact ⟨ii, rfl⟩
        wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl2 ⟨Hsl2, -⟩
        try wp_auto
        simp only [show sint.nat (W64 (0 + 1)) = 1 from rfl, List.set_cons_succ, List.set_cons_zero]
        wp_apply wp_boltLog li _ _ [W8 116, W8 118] _ [interface.mkOk go.bool #true, GoInterface.ok ii] _ iprop(True) _ (by decide) (by decide) rfl
          $$ Hlgok [Hsl2] [] [] as Hsl2 -
        · iframe
        · try simp only [List.zip_cons_cons, List.zip_nil_left, BigSepL.bigSepL_cons, BigSepL.bigSepL_nil]
          isplitl []
          · iapply logArgOk_bool
          isplitl []
          · iapply logArgOk_of_fmtErrorOk _ _ (by simp [methodVerbs]) (GoInterface.ok ii) $$ Hfe
          · iempintro
        try wp_auto
        iapply HΦ
        iright
        isplitr
        · ipureintro; exact ⟨Hne, Htx⟩
        iframe
        try iexact Hfe

end proof

end bbolt
end EtcdGrove
end Perennial
