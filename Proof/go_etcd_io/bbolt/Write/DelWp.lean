/-
**`Bucket.Delete`'s proof** (U7k, `notes/bbolt-proof-plan.md`): a writer's `Delete` over `wtxW`
(q = 1, `boltTxDef_wtxW`), the handle's bucket (`wtxWQ_handle`, `hD1`), the key as a `keyR` key
(the caller's, or one of the transaction's: `delKey_keyR`), the checks, `Bucket.Cursor_i`, `seek_w`;
a key not found returns with the records unchanged (`PubW.wget_lookup`); a found key's flags are
plain (`leaf_plain_nonroot`), then `Cursor.node` and `node.del`, closed by `delPost`/`delPostNF`
and `boltTxDef_wclose`. The logger and the deferred line as `PutWp`'s, the deferred line's lent
resources any `R` lending the key (the closed `boltTx` and the key, `delR_lend`).
-/
module

public import Proof.go_etcd_io.bbolt.Write.WrCur
public import Spec.go_etcd_io.bbolt.Bucket__Delete
public import Spec.go_etcd_io.bbolt.node__del
public import Proof.go_etcd_io.bbolt.Write.PutWp
public import Proof.go_etcd_io.bbolt.Read.TxBytes
import all Spec.go_etcd_io.bbolt.Api

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Write
section delwp
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

omit package_sem in
/-- **`Delete`'s key as a `keyR` key** of the writer's view: the caller's (`heap dk`), or one the
transaction returned (persistent heap bytes, or bytes of its view, `viewOf_agree`); given back. -/
theorem delKey_keyR [HasExt osFsExt] (B : BNs) (tx : Loc) (r : TxReg) (v : View) (key : GoSlice)
    (kb : List w8) (dk : DFrac) (own : Bool) :
    (if own then key ↦*{dk} kb else txBytesDef (GF := GF) B tx key kb) ∗ reg tx B r ∗ viewOf r v ⊢
      ∃ kr, keyR v key kr kb ∗
        (keyR v key kr kb -∗ (if own then key ↦*{dk} kb else txBytesDef B tx key kb)) := by
  cases own
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iintro ⟨#Hk, #Hreg, #Hvo⟩
    ihave #Hk' := Hk
    iunfold txBytesDef at Hk'
    icases Hk' with (#Hs | ⟨%r', %v', #Hreg', #Hvo', %Hin⟩)
    · iexists (KeyR.heap DFrac.discard)
      unfold keyR
      iframe Hs
      iintro -
      iexact Hk
    · iunfold reg at Hreg Hreg'
      icombine Hreg Hreg' gives %hr
      obtain ⟨-, rfl⟩ := hr
      ihave %Hvv := viewOf_agree r v v' $$ [Hvo Hvo']
      · iframe #
      subst Hvv
      iexists KeyR.view
      unfold keyR
      isplitr
      · ipureintro; exact Hin
      iintro -
      iexact Hk
  · simp only [↓reduceIte]
    iintro ⟨Hk, -, -⟩
    iexists (KeyR.heap dk)
    unfold keyR
    iframe Hk
    iintro H
    iexact H

/-- A `keyR` key's bytes, lent by the writer's state (a view key through its cells). -/
theorem keyR_wtxW_lend [HasExt osFsExt] (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX)
    (key : GoSlice) (kr : KeyR) (kb : List w8) :
    wtxW (GF := GF) K tx r m X ∗ keyR X.v key kr kb ⊢ ∃ dq : DFrac, key ↦*{dq} kb ∗
      (key ↦*{dq} kb -∗ wtxW K tx r m X ∗ keyR X.v key kr kb) := by
  cases kr with
  | heap d =>
    unfold keyR
    iintro ⟨Hw, Hk⟩
    iexists d
    iframe Hk
    iintro Hk
    iframe
  | view =>
    unfold keyR
    iintro ⟨Hw, %Hin⟩
    icases wtxW_cells_acc K tx r m X $$ Hw with ⟨%Hbase, Hc, Hwb⟩
    icases viewCells_src_acc wq X.v Hbase key Src.view kb (by intro h; cases h) $$ [Hc]
      with ⟨%dq, Hk, Hcb⟩
    · unfold srcOwn; iframe; ipureintro; exact Hin
    iexists dq
    iframe Hk
    iintro Hk
    ihave Hc := Hcb $$ Hk
    ihave Hw := Hwb $$ Hc
    iframe
    ipureintro; exact Hin

/-- The deferred line's lent resources: the closed transaction and `Delete`'s key. -/
theorem delR_lend [HasExt osFsExt] (B : BNs) (N : Namespace) (tx : Loc) (T : TxView)
    (key : GoSlice) (kb : List w8) (dk : DFrac) (own : Bool) :
    boltTxDef (GF := GF) B N tx 1 T ∗ (if own then key ↦*{dk} kb else txBytesDef B tx key kb) ⊢
      ∃ dq : DFrac, key ↦*{dq} kb ∗ (key ↦*{dq} kb -∗
        boltTxDef B N tx 1 T ∗ (if own then key ↦*{dk} kb else txBytesDef B tx key kb)) := by
  cases own
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iintro ⟨Ht, #Hk⟩
    icases txBytesDef_acc B N tx 1 T key kb $$ [Ht] with ⟨%dq, Hb, Hback⟩
    · iframe; iframe #
    iexists dq
    iframe Hb
    iintro Hb
    ihave Ht := Hback $$ Hb
    iframe; iframe #
  · simp only [↓reduceIte]
    iintro ⟨Ht, Hk⟩
    iexists dk
    iframe Hk
    iintro Hk
    iframe

/-- `node.del`'s inodes after a found key, as long as its entries. -/
theorem delAt_len (ins : List Inode) (ws : List WEntry) (kb : List w8) (hl : ins.length = ws.length)
    (hf : wsFound ws kb) : (ins.eraseIdx (wsIdx ws kb)).length = (wsDelAt ws kb).length := by
  have hi : wsIdx ws kb < ws.length := by
    unfold wsFound at hf
    cases h : ws[wsIdx ws kb]? with
    | none => rw [h] at hf; cases hf
    | some w => exact (List.getElem?_eq_some_iff.1 h).1
  unfold wsDelAt
  rw [if_pos hf]
  simp only [List.length_eraseIdx, List.length_append, List.length_take, List.length_drop]
  split <;> omega

theorem Bucket.Delete.wp_writer [HasExt osFsExt]
    (hcur : Bucket.Cursor_i.spec (GF := GF) (hG := hG))
    (hseek : Cursor.seek_w.spec (GF := GF) (hG := hG))
    (hnode : Cursor.node.spec (GF := GF) (hG := hG))
    (hdel : node.del.spec (GF := GF) (hG := hG))
    (hEq : bytes.Equal.spec (GF := GF) (hG := hG))
    (tx : Loc) (γ : BoltName) (T : TxView) (b : Loc) (n : GoString) (m : BktData)
    (key : GoSlice) (kb : GoString) (dk : DFrac) (own : Bool)
    (hD1 : ∀ X : WX, gensOK T X →
      ∀ b n, X.handles !! b = some (n, T.gen n) → bktLoc X n = some b) :
  {{ boltTx (GF := GF) tx γ 1 T ∗ boltBkt tx γ b n (T.gen n) ∗
      (if own then key ↦*{dk} kb else txBytes tx γ key kb) ∗
      ⌜T.rw = true ∧ T.cur.lookup n = some m⌝ }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"Delete")) (Val #key))
  {{ RET #GoInterface.nil; boltTx tx γ 1 (T.setBkt n (m.delete kb)) ∗
      (if own then key ↦*{dk} kb else txBytes tx γ key kb) }} := by
  wp_start as ⟨Ht, #Hb, Hko, %Hpre⟩
  obtain ⟨hrw, Hm⟩ := Hpre
  unfold boltTx boltBkt txBytes at *
  ihave Ht := (boltTxDef_wtxW _ _ tx T hrw).1 $$ Ht
  icases Ht with ⟨%K, %r, %c, %X, %HK, #Hfull, #Hvo, Hv, Hw, Hst, %Hf⟩
  obtain ⟨hKB, hKN, hTc⟩ := HK
  obtain ⟨hok, hcur', hbase, hgens, hwr, hwc⟩ := Hf
  unfold boltBktDef
  icases Hb with ⟨%r', #Hreg', #Hbtx, #Hh, -⟩
  ihave #Hreg'' : reg (GF := GF) tx K.B r' $$ []
  · rw [hKB]; iexact Hreg'
  ihave Hw : wtxWQ (GF := GF) K tx r true 1 X $$ [Hw]
  · rw [wtxWQ_one]; iexact Hw
  icases wtxWQ_handle K tx r r' true 1 X b n (T.gen n) $$ [Hw] with ⟨Hw, %Hhd⟩
  · iframe; iframe #
  ihave Hw : wtxW (GF := GF) K tx r true X $$ [Hw]
  · rw [← wtxWQ_one]; iexact Hw
  obtain ⟨hrr, hhd⟩ := Hhd
  subst r'
  have hbl := hD1 X hgens b n hhd
  icases delKey_keyR (bnsOf γ.gs) tx r X.v key kb dk own $$ [Hko] with ⟨%kr, Hkr, Hkback⟩
  · iframe; iframe #
  icases wtxW_pkgInit K tx r true X $$ Hw with ⟨Hw, #Hpkg⟩
  icases putW_db_acc K tx r true X $$ Hw with ⟨#Hcore, Hdb, Hwdb⟩
  ihave #Hcore' : isBoltCoreP K.B K.N K.db K.p K.sp K.t0 $$ []
  · unfold BC.core; iexact Hcore
  unfold isBoltCoreP
  icases Hcore' with ⟨#Hdbl, #Ht0, %Ht0, -, #Hos, #Hfix, #Hml, #Hmm, #Hsl, #Hpi, #Hti⟩
  ihave #Hfix' := Hfix
  iunfold dbFixed at Hfix'
  icases Hfix' with ⟨-, -, ⟨%lg, #Hlg, #Hlgok⟩, -⟩
  ihave %Hlgty := dbFixed_logPtrTyped _ _ K.db K.sp lg $$ Hfix Hlg
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply DB.Logger.wp_proof K.db lg Ht0.2.1 $$ []
  · iframe #; unfold dbLogger; iexact Hlgok
  try wp_auto
  ihave Hw := Hwdb $$ Hdb
  wp_bind (App (Val (GoInstruction (Convert go.untypedBool go.bool))) _)
  wp_apply cm_logger_ne_discard lg Hlgty $$ [] as %bl -
  · iframe #; unfold dbLogger; iexact Hlgok
  have hR1 : (wtxW K tx r true X ∗ keyR X.v key kr kb : IProp GF) ⊢ ∃ dq : DFrac, key ↦*{dq} kb ∗
      (key ↦*{dq} kb -∗ wtxW K tx r true X ∗ keyR X.v key kr kb) :=
    keyR_wtxW_lend K tx r true X key kr kb
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ key_ptr ↦ key ∗ lg_ptr ↦ lg ∗
      wtxW K tx r true X ∗ keyR X.v key kr kb ∗
      ∃ f : GoFunc, defer ↦ f ∗ □ (∀ (e : GoInterface) (R : IProp GF),
        ⌜R ⊢ ∃ dq : DFrac, key ↦*{dq} kb ∗ (key ↦*{dq} kb -∗ R)⌝ -∗
        (⌜e = interface.nil⌝ ∨ fmtErrorOk e) -∗
        err_ptr ↦ e -∗ key_ptr ↦ key -∗ lg_ptr ↦ lg -∗ R -∗
        WP (App (Val #f) (Val #())) {{ v, ⌜v = #()⌝ ∗ err_ptr ↦ e ∗ R }})))) $$
    [key lg defer Hw Hkr]
  · cases bl
    · wp_auto
      iframe
      isplitr
      · ipureintro; rfl
      imodintro
      iintro %e %R %hRl - Herr - - HR
      wp_auto
      iframe; try (ipureintro; rfl)
    · cases lg with
      | nil => iexfalso; unfold dbLogger boltLogger; iexact Hlgok
      | ok li =>
      ihave #Hlgok' : boltLogger (GF := GF) (.ok li) $$ []
      · unfold dbLogger; iexact Hlgok
      wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      try wp_auto
      wp_apply wp_boltLog li _ _ [W8 113] _ [interface.mkOk (go.GoType.SliceType go.byte) #key] _
        iprop(wtxW K tx r true X ∗ keyR X.v key kr kb) _ (by decide) (by decide) rfl $$ Hlgok' [Hsl] []
        [Hw Hkr] as Hsl ⟨Hw, Hkr⟩
      · iframe
      · try simp only [List.zip_cons_cons, List.zip_nil_left]
        isplitl
        · iapply logArgOk_bytesR _ _ key kb hR1
        · iempintro
      · iframe
      try wp_auto
      isplitr
      · ipureintro; rfl
      iframe
      imodintro
      iintro %e %R %hRl Hen Herr Hkp Hlgp HR
      wp_auto
      cases e with
        | nil =>
          wp_auto
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %sl2 ⟨Hsl2, -⟩
          try wp_auto
          wp_apply wp_boltLog li _ _ [W8 113] _ [interface.mkOk (go.GoType.SliceType go.byte) #key] _
            R _ (by decide) (by decide) rfl $$ Hlgok' [Hsl2] [] [HR] as Hsl2 HR
          · iframe
          · try simp only [List.zip_cons_cons, List.zip_nil_left]
            isplitl
            · iapply logArgOk_bytesR _ _ key kb hRl
            · iempintro
          · iexact HR
          try wp_auto
          iframe; try (ipureintro; rfl)
        | ok ii =>
          icases Hen with (%he | #Hfe)
          · cases he
          wp_auto
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %sl2 ⟨Hsl2, -⟩
          try wp_auto
          wp_apply wp_boltLog li _ _ [W8 113, W8 118] _
            [interface.mkOk (go.GoType.SliceType go.byte) #key, GoInterface.ok ii] _
            R _ (by decide) (by decide) rfl $$ Hlgok' [Hsl2] [] [HR] as Hsl2 HR
          · simp only [show sint.nat (W64 (0 + 1)) = 1 from rfl, List.set_cons_succ, List.set_cons_zero]
            iexact Hsl2
          · try simp only [List.zip_cons_cons, List.zip_nil_left]
            isplitl
            · iapply logArgOk_bytesR _ _ key kb hRl
            isplitl
            · iapply logArgOk_of_fmtErrorOk _ _ (by simp [methodVerbs]) (GoInterface.ok ii) $$ Hfe
            · iempintro
          · iexact HR
          try wp_auto
          iframe; try (ipureintro; rfl)
  iintro %v ⟨%hv, Hkp, Hlgp, Hw, Hkr, %f, Hdefer, #Hdf⟩
  subst hv
  icases putW_db_acc K tx r true X $$ Hw with ⟨-, Hdb, Hwdb⟩
  wp_auto
  rw [decide_eq_false Ht0.2.1]
  wp_auto
  ihave Hw := Hwdb $$ Hdb
  icases wtxW_writable_acc K tx r true X $$ Hw with ⟨Hwr, Hwb⟩
  have hwrt : X.t.t.writable' = true := hok.1.1
  wp_method_call
  wp_call
  wp_auto
  rw [hwrt]
  wp_auto
  ihave Hw := Hwb $$ Hwr
  obtain ⟨B, hB⟩ := PubW.bktLoc_rec X hok n b hbl
  have hloc := PubW.bktLocalOK_of_wOK X hok b B hB
  have hpm := PubW.pmFresh_of_wOK X hok
  have hmd : m = GMap.ofList (lbktEnts X b) :=
    PubW.wdata_bkt X n b m hbl (by rw [← hcur']; exact Hm)
  icases wtxW_cursor_acc K tx r true X b B hB $$ Hw with ⟨-, -, Hsk, %dt, Htx, Hwbc⟩
  wp_apply hcur K tx r true 1 b dt $$ [Hsk Htx] as %cu ⟨%stk, Hc, Hs, Hcap, Hsk, Htx⟩
  · iframe; iframe #
  ihave Hw := Hwbc $$ Hsk Htx
  try wp_auto
  wp_apply hseek K tx r true X b cu stk [] key kb kr hloc hpm $$
    [Hw Hc Hs Hcap Hkr] as %k %vl %fl ⟨%stk', %els, %pids, Hw, Hc, Hs, Hcap, Hkr, %Hrt, Hkv⟩
  · iframe
  try wp_auto
  obtain ⟨Hp, Hr⟩ := Hrt
  have hlk := PubW.wget_lookup X b els pids kb hloc Hp Hr
  rw [← hmd] at hlk
  obtain ⟨p, ws, ⟨j, hpj⟩, hL, hle⟩ := WOpen.lPath_leaf X b B hB hloc els pids Hp
  have hI := WOpen.lPath_posI X b B hB hloc els pids Hp j p hpj
  have hroot : b ≠ X.rl := Write.bktLoc_ne_root X hwr n b hbl
  have hplain := leaf_plain_nonroot X b B hok hB hroot p hI ws hL
  have hand : ∀ f : w32, f &&& W32 1 = W32 0 ↔ ¬ isBktFlag f := by
    intro f; unfold isBktFlag; simp
  rw [hle] at hlk
  rw [hle]
  wp_bind (App (App (Val #(functions bytes.Equal [])) (Val #key)) (Val #k))
  iapply (wp_wand (Φ := fun v => iprop(∃ beq : Bool,
      ⌜v = #beq ∧ (beq = true ↔ (match ws[wsIdx ws kb]? with
        | none => kb = []
        | some w => kb = w.key)) ∧ fl &&& W32 1 = W32 0⌝ ∗
      wtxW (GF := GF) K tx r true X ∗ keyR X.v key kr kb))) $$ [Hw Hkr Hkv]
  · cases hw : ws[wsIdx ws kb]? with
    | none =>
      icases Hkv with %Hnil
      obtain ⟨rfl, rfl, rfl⟩ := Hnil
      icases keyR_wtxW_lend K tx r true X key kr kb $$ [Hw Hkr] with ⟨%dq, Hkk, Hkb⟩
      · iframe
      wp_apply hEq key slice.nil dq DFrac.discard kb [] $$ [Hkk] as ⟨Hkk, -⟩
      · iframe; iapply ownSlice_nil
      ihave ⟨Hw, Hkr⟩ := Hkb $$ Hkk
      iexists (decide (kb = []))
      iframe
      ipureintro
      exact ⟨rfl, by simp, by decide⟩
    | some w =>
      icases Hkv with ⟨%Hkw, #Hks, #Hvs⟩
      have hwm : w ∈ ws := List.mem_of_getElem? hw
      obtain ⟨hlks, hlvs⟩ := WOpen.leaf_live X b B hB hloc p hI ws hL w hwm
      ihave Hw : wtxWQ (GF := GF) K tx r true 1 X $$ [Hw]
      · rw [wtxWQ_one]; iexact Hw
      icases wtxWQ_keyR_src_acc K tx r true 1 X key kr kb k _ w.key
        (WOpen.leafSrc_live X b B hB hloc _ hlks) $$ [Hw Hkr] with ⟨%d1, %d2, Hnm, Hkk, Hback⟩
      · iframe; iframe #
      wp_apply hEq key k d1 d2 kb w.key $$ [Hnm Hkk] as ⟨Hnm, Hkk⟩
      · iframe
      icases Hback $$ Hnm Hkk with ⟨Hw, Hkr⟩
      ihave Hw : wtxW (GF := GF) K tx r true X $$ [Hw]
      · rw [← wtxWQ_one]; iexact Hw
      iexists (decide (kb = w.key))
      iframe
      ipureintro
      exact ⟨rfl, by simp, by rw [Hkw.2]; exact (hand _).2 (hplain w hwm)⟩
  iintro %v ⟨%beq, %Hbeq, Hw, Hkr⟩
  obtain ⟨hv, hbeq, hfl⟩ := Hbeq
  subst hv
  wp_auto
  cases beq
  · -- not found: the records unchanged
    simp only [Bool.not_false]
    wp_auto
    have hnc : ¬ (match ws[wsIdx ws kb]? with | none => kb = [] | some w => kb = w.key) :=
      fun h => absurd (hbeq.2 h) (by simp)
    have hnone : m !! kb = none := by
      show m.lookup kb = none
      rw [hlk]
      cases hw : ws[wsIdx ws kb]? with
      | none => rfl
      | some w =>
        rw [hw] at hnc
        simp only
        rw [if_neg]
        intro h; exact hnc h.1.symm
    have hT : T.setBkt n (m.delete kb) = T := by
      rw [GMap.delete_notin _ _ hnone]
      unfold TxView.setBkt
      rw [GMap.insert_id _ _ _ Hm]
    ihave Ht : boltTxDef (GF := GF) (bnsOf γ.gs) γ.ns tx 1 T $$ [Hv Hw Hst]
    · iapply (boltTxDef_wtxW _ _ tx T hrw).2
      iexists K, r, c, X
      iframe; iframe #
      ipureintro; exact ⟨⟨hKB, hKN, hTc⟩, hok, hcur', hbase, hgens, hwr, hwc⟩
    ihave Hko := Hkback $$ Hkr
    wp_bind (App (Val #f) (Val #()))
    iapply (wp_wand (Φ := fun v => iprop(⌜v = #()⌝ ∗ err_ptr ↦ GoInterface.nil ∗
        (boltTxDef (GF := GF) (bnsOf γ.gs) γ.ns tx 1 T ∗
          (if own then key ↦*{dk} kb else txBytesDef (bnsOf γ.gs) tx key kb))))) $$
      [err Hkp Hlgp Ht Hko]
    · iapply Hdf $$ %GoInterface.nil %_ %(delR_lend (bnsOf γ.gs) γ.ns tx T key kb dk own) [] err Hkp
        Hlgp [Ht Hko]
      · ileft; ipureintro; rfl
      · iframe
    iintro %vret ⟨%hvret, err, Ht, Hko⟩
    subst hvret
    wp_auto
    iapply HΦ
    rw [hT]
    iframe
  simp only [Bool.not_true]
  wp_auto
  rw [decide_eq_true hfl]
  wp_auto
  icases wtxW_nodes_nonnull K tx r true X b B hB $$ Hw with ⟨Hw, %Hnn⟩
  icases wtxW_matReady_path K tx r true X b B hok hB hloc els pids Hp $$ Hw with ⟨Hw, %Hmr⟩
  wp_apply hnode K tx r true X b B cu stk' els pids (DFrac.own 1) hB hloc Hp Hnn Hmr
    $$ [Hw Hc Hs] as %l ⟨%X3, Hw, Hc, Hs, %Hcn⟩
  · iframe
  obtain ⟨Hmg, Hok3f, Hloc3, B3, pid, HB3, Hlast, Hres⟩ := Hcn
  have hok3 := Hok3f hok
  have hlf : leafFor X3 b kb l :=
    lRoutes_leafFor' X X3 b l els pids kb hok Hp Hr Hmg ⟨B3, HB3, pid, Hlast, Hres⟩
  obtain ⟨B3', rl, bnd, HB3', Hrl, Hll, -, -⟩ := id hlf
  rw [HB3] at HB3'
  cases HB3'
  have hcl3 := Write.wOK_bktClean X3 hok3 b B3 HB3
  have hnc := hcl3.2.2.2.2.2.2.2.1 l rl Hrl
  obtain ⟨hlB3, B4, hB4, -, -, -, hlive4, -⟩ := id Hloc3
  rw [HB3] at hB4
  cases hB4
  have hlive3 := hlive4 l rl Hrl
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ := matGrow_keepW Hmg
  icases wtxW_cells_acc K tx r true X3 $$ Hw with ⟨%Hbase3, Hcells, Hwbc⟩
  ihave Hw := Hwbc $$ Hcells
  icases wtxW_pkgInit K tx r true X3 $$ Hw with ⟨Hw, #Hpkg3⟩
  icases wtxW_open K tx r true X3 $$ Hw with ⟨-, -, -, Hh, Hcv, Hsk, Hclose⟩
  ihave %Hok3 := wtxHeap_heapOK tx (DFrac.own 1) X3 $$ Hh
  icases wtxHeap_setNode_acc tx (DFrac.own 1) X3 b B3 l rl HB3 Hrl $$ Hh
    with ⟨Hno, Hbo, Hf, Hrf, Hback⟩
  rw [decide_eq_true hlive3]
  ihave Hkr : keyR X3.v key kr kb $$ [Hkr]
  · rw [k3]; iexact Hkr
  wp_apply hdel X3.v l b rl wq key kb kr hnc.2.1 hnc.2.2.2.1 hnc.2.2.2.2.2.1 Hbase3
    $$ [Hno Hcv Hkr] as ⟨Hpost, Hcv, Hkr⟩
  · iframe; try iframe #
  try wp_auto
  icases Hpost with (⟨%Hnf, Hno⟩ | ⟨%Hfd, %sl, Hno⟩)
  · -- the key in no entry of the leaf
    have hpar : rl.nv.parent' ≠ l := Hok3.2.2.2.1 b B3 l rl HB3 Hrl
    ihave Hh := Hback $$ %rl %hpar [Hno] [Hbo] [Hf] Hrf
    · iexact Hno
    · iexact Hbo
    · iexact Hf
    ihave Hh : wtxHeap (GF := GF) tx (DFrac.own 1) X3 $$ [Hh]
    · rw [setNode_self' X3 b l B3 rl HB3 Hrl]; iexact Hh
    ihave Hw := Hclose $$ %X3 [] Hh Hcv Hsk
    · ipureintro; exact ⟨rfl, rfl, rfl⟩
    obtain ⟨hd4, hg4, hwr4, hk4⟩ :=
      delPostNF T X X3 n b l B3 rl kb hok hcur' hgens hwr hbl Hmg hok3 HB3 Hrl hlf Hnf
    have hT' : T.setBkt n (m.delete kb) =
        TxView.ofC (c.1, c.2.1, c.2.2.1.insert n (m.delete kb), c.2.2.2) := by
      rw [hTc]; rfl
    have hv4 := hk4.v
    imod boltTxDef_wclose K tx r c _ X _ (T.setBkt n (m.delete kb)) ⊤ (by simp) hT' hk4
      (fun extra => txShape_matGrow _ X X3 b extra hloc Hmg)
      ⟨hok3, hrw, by rw [hd4, Hm]; rfl, by rw [hv4]; exact hbase, hg4, hwr4,
        Write.wrCurFacts_gen T _ X3 rfl (Write.wrCurFacts_matGrow T X X3 b hok Hmg hwc)⟩ $$
      [Hv Hw Hst] with Ht
    · rw [hKB, hv4]; iframe; iframe #
    ihave Hkr : keyR X.v key kr kb $$ [Hkr]
    · rw [← k3]; iexact Hkr
    ihave Hko := Hkback $$ Hkr
    ihave Ht : boltTxDef (GF := GF) (bnsOf γ.gs) γ.ns tx 1 (T.setBkt n (m.delete kb)) $$ [Ht]
    · rw [hKB, hKN] at *; iexact Ht
    wp_bind (App (Val #f) (Val #()))
    iapply (wp_wand (Φ := fun v => iprop(⌜v = #()⌝ ∗ err_ptr ↦ GoInterface.nil ∗
        (boltTxDef (GF := GF) (bnsOf γ.gs) γ.ns tx 1 (T.setBkt n (m.delete kb)) ∗
          (if own then key ↦*{dk} kb else txBytesDef (bnsOf γ.gs) tx key kb))))) $$
      [err Hkp Hlgp Ht Hko]
    · iapply Hdf $$ %GoInterface.nil %_
        %(delR_lend (bnsOf γ.gs) γ.ns tx (T.setBkt n (m.delete kb)) key kb dk own) [] err Hkp Hlgp
        [Ht Hko]
      · ileft; ipureintro; rfl
      · iframe
    iintro %vret ⟨%hvret, err, Ht, Hko⟩
    subst hvret
    wp_auto
    iapply HΦ
    iframe
  · -- the entry removed
    have hpar : (rl.withEntsU sl (rl.ins.eraseIdx (wsIdx rl.ws kb)) (wsDelAt rl.ws kb) true).nv.parent'
        ≠ l := Hok3.2.2.2.1 b B3 l rl HB3 Hrl
    ihave Hh := Hback $$ %(rl.withEntsU sl (rl.ins.eraseIdx (wsIdx rl.ws kb)) (wsDelAt rl.ws kb) true)
      %hpar [Hno] [Hbo] [Hf] Hrf
    · iexact Hno
    · iexact Hbo
    · iexact Hf
    ihave Hw := Hclose $$
      %(X3.setNode b l (rl.withEntsU sl (rl.ins.eraseIdx (wsIdx rl.ws kb)) (wsDelAt rl.ws kb) true))
      [] Hh Hcv Hsk
    · ipureintro; rw [setNode_eq X3 b l B3 _ HB3]; exact ⟨rfl, rfl, rfl⟩
    obtain ⟨hok4, hd4, hg4, hwr4, hk4⟩ :=
      delPost T X X3 n b l B3 rl kb sl (rl.ins.eraseIdx (wsIdx rl.ws kb)) hok hcur' hgens hwr hbl Hmg
        hok3 Hok3.2.1 HB3 Hrl hlf (delAt_len _ _ _ hnc.2.2.1 Hfd)
    have hT' : T.setBkt n (m.delete kb) =
        TxView.ofC (c.1, c.2.1, c.2.2.1.insert n (m.delete kb), c.2.2.2) := by
      rw [hTc]; rfl
    have hv4 := hk4.v
    imod boltTxDef_wclose K tx r c _ X _ (T.setBkt n (m.delete kb)) ⊤ (by simp) hT' hk4
      (fun extra => (txShape_matGrow _ X X3 b extra hloc Hmg).trans (txShape_delAt _ X3 b l B3 rl sl _ kb true extra HB3 Hrl))
      ⟨hok4, hrw, by rw [hd4, Hm]; rfl, by rw [hv4]; exact hbase, hg4, hwr4,
        Write.wrCurFacts_leafStep T _ X X3 b l B3 _ hok Hmg HB3 (Write.bktLoc_ne_root X hwr n b hbl) rfl hwc⟩ $$
      [Hv Hw Hst] with Ht
    · rw [hKB, hv4]; iframe; iframe #
    ihave Hkr : keyR X.v key kr kb $$ [Hkr]
    · rw [← k3]; iexact Hkr
    ihave Hko := Hkback $$ Hkr
    ihave Ht : boltTxDef (GF := GF) (bnsOf γ.gs) γ.ns tx 1 (T.setBkt n (m.delete kb)) $$ [Ht]
    · rw [hKB, hKN] at *; iexact Ht
    wp_bind (App (Val #f) (Val #()))
    iapply (wp_wand (Φ := fun v => iprop(⌜v = #()⌝ ∗ err_ptr ↦ GoInterface.nil ∗
        (boltTxDef (GF := GF) (bnsOf γ.gs) γ.ns tx 1 (T.setBkt n (m.delete kb)) ∗
          (if own then key ↦*{dk} kb else txBytesDef (bnsOf γ.gs) tx key kb))))) $$
      [err Hkp Hlgp Ht Hko]
    · iapply Hdf $$ %GoInterface.nil %_
        %(delR_lend (bnsOf γ.gs) γ.ns tx (T.setBkt n (m.delete kb)) key kb dk own) [] err Hkp Hlgp
        [Ht Hko]
      · ileft; ipureintro; rfl
      · iframe
    iintro %vret ⟨%hvret, err, Ht, Hko⟩
    subst hvret
    wp_auto
    iapply HΦ
    iframe

end delwp
end Write

end bbolt
end EtcdGrove
end Perennial
