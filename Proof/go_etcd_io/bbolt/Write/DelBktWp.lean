/-
U7m (`notes/bbolt-proof-plan.md`): **the root bucket's `DeleteBucket`** over the writer's records
in mode `false` (`wtxW`, the exclusive part taken out: `Write/DelBktXcl`) and its database side
(`wdbW`, for `child.free()`), for `Tx.DeleteBucket`.

The not-found post has a second case: for the empty name in an empty root bucket, `c.seek` returns
no key (`nil`), `bytes.Equal(newKey, nil)` holds for the empty `newKey`, and the zero flags give
`ErrIncompatibleValue`, not `ErrBucketNotFound` (U7m's finding; `Tx.DeleteBucket.spec` states
`ErrBucketNotFound` for every absent name).
-/
module

public import Proof.go_etcd_io.bbolt.Write.DelBktXcl
public import Proof.go_etcd_io.bbolt.Write.CreateBktWp
public import Spec.go_etcd_io.bbolt.Bucket__ForEachBucket_w
public import Spec.go_etcd_io.bbolt.node__del
public import Spec.go_etcd_io.bbolt.Bucket__free_dead
public import Proof.go_etcd_io.bbolt.Write.DelBktPure
public import Proof.go_etcd_io.bbolt.Write.DelBktCur
public import Proof.go_etcd_io.bbolt.Read.PubWCur

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Write

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- What a successful `DeleteBucket` of the present `n` gives of the new records `X'` and database
side `w'`, from `X` and `w`: the facts `boltTxDef` closes with at `T.dropBkt n`, the view and meta
copy kept, the committed state kept, the freelist's agreement and the page tokens; and the cursor's
writer facts (`wrCurFacts`, maintainer 16's addition to `boltTx`'s writer facts: the deleted bucket
out of `liveB` and the root's `bm`, `n`'s generation bumped so `wRoot n = 0`, the other buckets'
`nm`, `nloc` and `ib.root'` unchanged). -/
def deleteOK (T : TxView) (r : TxReg) (n : GoString) (X X' : WX) (w w' : WDb) : Prop :=
  wOK X' ∧ wtxData X' = T.cur.delete n ∧ gensOK (T.dropBkt n) X' ∧ wrFacts X' ∧
    X'.v = X.v ∧ X'.t.mv = X.t.mv ∧ w'.C = w.C ∧ flViewU X' w'.fl ∧
    (∀ extra, txShape (GF := GF) r.n.pg X extra ⊢ txShape r.n.pg X' extra) ∧
    wrCurFacts (T.dropBkt n) X'

omit [GooseSemantics] [GooseInterp] go_gctx hos in
/-- `node.del`'s inodes after a found key, as long as its entries (as `Write/DelWp.delAt_len`). -/
theorem dbkDelAt_len (ins : List Inode) (ws : List WEntry) (kb : List w8)
    (hl : ins.length = ws.length) (hf : wsFound ws kb) :
    (ins.eraseIdx (wsIdx ws kb)).length = (wsDelAt ws kb).length := by
  have hi : wsIdx ws kb < ws.length := by
    unfold wsFound at hf
    cases h : ws[wsIdx ws kb]? with
    | none => rw [h] at hf; cases hf
    | some w => exact (List.getElem?_eq_some_iff.1 h).1
  unfold wsDelAt
  rw [if_pos hf]
  simp only [List.length_eraseIdx, List.length_append, List.length_take, List.length_drop]
  split <;> omega

/-- **The root bucket's `DeleteBucket`.** -/
theorem Bucket.DeleteBucket.wp_root
    (hBw : Bucket.Bucket_w.spec (GF := GF) (hG := hG))
    (hCur : Bucket.Cursor_i.spec (GF := GF) (hG := hG))
    (hSeek : Cursor.seek_w.spec (GF := GF) (hG := hG))
    (hFeb : Bucket.ForEachBucket_w.spec (GF := GF) (hG := hG))
    (hNode : Cursor.node.spec (GF := GF) (hG := hG))
    (hDel : node.del.spec (GF := GF) (hG := hG))
    (hFree : Bucket.free_dead.spec (GF := GF) (hG := hG))
    (hClone : cloneBytes.spec (GF := GF) (hG := hG))
    (hEq : bytes.Equal.spec (GF := GF) (hG := hG))
    (K : BC) (tx : Loc) (r : TxReg) (X : WX) (w : WDb) (T : TxView) (name : GoSlice)
    (n : GoString) (dq : DFrac) (hok : wOK X) (hcur : T.cur = wtxData X) (hgens : gensOK T X)
    (hwr : wrFacts X) (hwc : wrCurFacts T X) (hfl : flViewU X w.fl) :
  {{ wtxW (GF := GF) K tx r false X ∗ wdbW K tx X.v w ∗ name ↦*{dq} n }}
    (App (Val (X.rl @!! go.GoType.PointerType Bucket.ty @!! go!"DeleteBucket")) (Val #name))
  {{ (err : GoInterface), RET #err; name ↦*{dq} n ∗
      (if T.cur.lookup n = none then
         iprop(wtxW K tx r false X ∗ wdbW K tx X.v w ∗
           (globalAddr go_etcd_io.bbolt.errors.ErrBucketNotFound ↦□ err ∨
            ⌜n = []⌝ ∗ globalAddr go_etcd_io.bbolt.errors.ErrIncompatibleValue ↦□ err))
       else iprop(⌜err = GoInterface.nil⌝ ∗ ∃ (X' : WX) (w' : WDb), wtxW K tx r false X' ∗
         wdbW K tx X.v w' ∗ ⌜deleteOK (GF := GF) T r n X X' w w'⌝)) }} := by
  wp_start as ⟨Hw, Hwdb, Hname⟩
  obtain ⟨R, hR⟩ : ∃ R, X.t.bs !! X.rl = some R := Option.isSome_iff_exists.1 hok.1.2.2.2.2.1
  icases cb_core K tx r false X $$ Hw with ⟨#Hkc, #Hpkg, Hw⟩
  ihave #Hcore' : isBoltCoreP K.B K.N K.db K.p K.sp K.t0 $$ []
  · unfold BC.core; iexact Hkc
  unfold isBoltCoreP
  icases Hcore' with ⟨#Hdbl, #Ht0, %Ht0, -, #Hos, #Hfix, #Hml, #Hmm, #Hsl, #Hpi, #Hti⟩
  ihave #Hfix' := Hfix
  iunfold dbFixed at Hfix'
  icases Hfix' with ⟨-, -, ⟨%lg, #Hlg, #Hlgok⟩, -⟩
  ihave %Hlgty := dbFixed_logPtrTyped K.db K.sp lg $$ Hfix Hlg
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  icases wtxW_bkt_tx_acc K tx r false X X.rl R hR $$ Hw with ⟨%dqt, Htxf, Hwb⟩
  try wp_auto
  ihave Hw := Hwb $$ Htxf
  icases wtxW_db_acc K tx r false X $$ Hw with ⟨%Hrdb, -, Hdbf, Hst, Hwb⟩
  rw [Hrdb]
  try wp_auto
  wp_apply DB.Logger.wp_proof K.db lg Ht0.2.1 $$ []
  · iframe #; unfold dbLogger; iexact Hlgok
  try wp_auto
  wp_bind (App (Val (GoInstruction (Convert go.untypedBool go.bool))) _)
  wp_apply cm_logger_ne_discard lg Hlgty $$ [] as %bl -
  · iframe #; unfold dbLogger; iexact Hlgok
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ name ↦*{dq} n ∗ key_ptr ↦ name ∗
      lg_ptr ↦ lg ∗ ∃ f : GoFunc, defer ↦ f ∗ □ (∀ e : GoInterface,
        (⌜e = interface.nil⌝ ∨ fmtErrorOk e) -∗ err_ptr ↦ e -∗ key_ptr ↦ name -∗ lg_ptr ↦ lg -∗
        name ↦*{dq} n -∗
        WP (App (Val #f) (Val #())) {{ v, ⌜v = #()⌝ ∗ err_ptr ↦ e ∗ name ↦*{dq} n }})))) $$
      [Hname key lg defer]
  · cases bl
    · wp_auto
      iframe
      isplitr
      · ipureintro; rfl
      imodintro
      iintro %e - Herr - - Hn
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
      wp_apply wp_boltLog li _ _ [W8 113] _ [interface.mkOk (go.GoType.SliceType go.byte) #name] _
        (name ↦*{dq} n) _ (by decide) (by decide) rfl $$ Hlgok' [Hsl] [] [Hname] as Hsl Hname
      · iframe
      · try simp only [List.zip_cons_cons, List.zip_nil_left]
        isplitl
        · iapply logArgOk_bytes
        · iempintro
      · iexact Hname
      try wp_auto
      isplitr
      · ipureintro; rfl
      iframe
      imodintro
      iintro %e Hen Herr Hkey Hlg Hn
      wp_auto
      cases e with
      | nil =>
        wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl2 ⟨Hsl2, -⟩
        try wp_auto
        wp_apply wp_boltLog li _ _ [W8 113] _ [interface.mkOk (go.GoType.SliceType go.byte) #name] _
          (name ↦*{dq} n) _ (by decide) (by decide) rfl $$ Hlgok' [Hsl2] [] [Hn] as Hsl2 Hn
        · iframe
        · try simp only [List.zip_cons_cons, List.zip_nil_left]
          isplitl
          · iapply logArgOk_bytes
          · iempintro
        · iexact Hn
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
        rw [show ([interface.mkOk (go.GoType.SliceType go.byte) #name, GoInterface.nil] :
            List GoInterface).set (sint.nat (W64 (0 + 1))) (GoInterface.ok ii) =
            [interface.mkOk (go.GoType.SliceType go.byte) #name, GoInterface.ok ii] from rfl]
        try wp_auto
        wp_apply wp_boltLog li _ _ [W8 113, W8 118] _
          [interface.mkOk (go.GoType.SliceType go.byte) #name, GoInterface.ok ii] (DFrac.own 1)
          (name ↦*{dq} n) _ (by decide) (by decide) rfl $$ Hlgok' [Hsl2] [] [Hn] as Hsl2 Hn
        · iframe
        · try simp only [List.zip_cons_cons, List.zip_nil_left]
          isplitl
          · iapply logArgOk_bytes
          isplitl
          · iapply logArgOk_of_fmtErrorOk _ _ (by simp [methodVerbs]) (GoInterface.ok ii) $$ Hfe
          · iempintro
        · iexact Hn
        try wp_auto
        iframe; try (ipureintro; rfl)
  iintro %v ⟨%hv, Hname, Hkey, Hlgp, %f, Hdefer, #Hdf⟩
  subst hv
  ihave Hw := Hwb $$ Hdbf Hst
  icases wtxW_bkt_tx_acc K tx r false X X.rl R hR $$ Hw with ⟨%dqt, Htxf, Hwb⟩
  try wp_auto
  ihave Hw := Hwb $$ Htxf
  icases wtxW_db_acc K tx r false X $$ Hw with ⟨-, -, Hdbf, Hst, Hwb⟩
  rw [Hrdb]
  try wp_auto
  rw [decide_eq_false Ht0.2.1]
  try wp_auto
  ihave Hw := Hwb $$ Hdbf Hst
  icases wtxW_bkt_tx_acc K tx r false X X.rl R hR $$ Hw with ⟨%dqt, Htxf, Hwb⟩
  try wp_auto
  ihave Hw := Hwb $$ Htxf
  have hwrt : X.t.t.writable' = true := hok.1.1
  icases wtxW_bkt_tx_acc K tx r false X X.rl R hR $$ Hw with ⟨%dqt, Htxf, Hwb⟩
  wp_method_call
  wp_call
  try wp_auto
  ihave Hw := Hwb $$ Htxf
  icases wtxW_writable_acc K tx r false X $$ Hw with ⟨Hwrf, Hwb⟩
  try wp_auto
  rw [hwrt]
  try wp_auto
  ihave Hw := Hwb $$ Hwrf
  ihave #Hpke : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.errors $$ []
  · iPkgInit
  ihave #Hei : (go_etcd_io.bbolt.errors.bboltErrorsInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpke
  unfold go_etcd_io.bbolt.errors.bboltErrorsInit go_etcd_io.bbolt.errors.bboltErrorsVars
  icases Hei with ⟨%enf, #Hnf, %-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hiv, -, -, #Hbnf⟩
  wp_apply hClone name n dq $$ [Hname] as %nk ⟨Hnk, -, Hname⟩
  · iframe #; iframe
  imod ownSlice_persist nk _ _ $$ Hnk with #Hnk
  try wp_auto
  icases wtxW_cursor_acc K tx r false X X.rl R hR $$ Hw with ⟨#Hkc2, #Hreg, Hst, %dt, Htx, Hwbc⟩
  wp_apply hCur K tx r false 1 X.rl dt $$ [Hst Htx] as %cur ⟨%stk, Hcu, Hs, Hscap, Hst, Htx⟩
  · iframe; iframe #
  ihave Hw := Hwbc $$ Hst Htx
  try wp_auto
  have hloc := PubW.bktLocalOK_of_wOK X hok X.rl R hR
  have hpm := PubW.pmFresh_of_wOK X hok
  wp_apply hSeek K tx r false X X.rl cur stk [] nk n (KeyR.heap DFrac.discard) hloc hpm
    $$ [Hw Hcu Hs Hscap] as %k %vl %fl ⟨%stk', %els, %pids, Hw, Hcu, Hs, Hscap, -, %Hrt, Hkv⟩
  · iframe; unfold keyR; iexact Hnk
  obtain ⟨Hp, Hr⟩ := Hrt
  have hlk := root_lookup X R hok hR hloc els pids n Hp Hr
  rw [← hcur] at hlk
  unfold wsFound at hlk
  ihave Hk : (∃ (kb : List w8) (dk : DFrac), k ↦*{dk} kb ∗ (k ↦*{dk} kb -∗ wtxW K tx r false X) ∗
      ⌜(kb = n → ((T.cur !! n).isSome ∧ ¬ (fl &&& W32 1 = W32 0)) ∨
          (T.cur !! n = none ∧ n = [] ∧ fl = W32 0)) ∧
        (kb ≠ n → T.cur !! n = none) ∧
        (kb = n → (T.cur !! n).isSome → ∃ w ∈ lLeaf X X.rl pids, w.key = n)⌝) $$ [Hw Hkv]
  · cases hm : (lLeaf X X.rl pids)[wsIdx (lLeaf X X.rl pids) n]? with
    | none =>
      rw [hm] at hlk
      icases Hkv with %hk0
      obtain ⟨hk0, -, hfl0⟩ := hk0
      subst hk0
      have hnone : T.cur !! n = none := by
        cases h : T.cur !! n with
        | none => rfl
        | some _ => exact absurd (hlk.1 (by rw [h]; rfl)) (by simp)
      iexists [], DFrac.own 1
      ihave Hnil : (slice.nil ↦*{DFrac.own 1} ([] : List w8)) $$ []
      · iapply ownSlice_nil
      iframe Hnil
      isplitl
      · iintro -; iexact Hw
      ipureintro
      exact ⟨fun h => Or.inr ⟨hnone, h.symm, hfl0⟩, fun _ => hnone,
        fun _ h => by rw [hnone] at h; cases h⟩
    | some w =>
      rw [hm] at hlk
      icases Hkv with ⟨%hk0, #Hks, -⟩
      obtain ⟨-, hfl⟩ := hk0
      obtain ⟨p, ws, ⟨j, hpj⟩, hL, hle⟩ := WOpen.lPath_leaf X X.rl R hR hloc els pids Hp
      have hpI := WOpen.lPath_posI X X.rl R hR hloc els pids Hp j p hpj
      have hwl : w ∈ lLeaf X X.rl pids := List.mem_of_getElem? hm
      have hwm : w ∈ ws := by rw [← hle]; exact hwl
      obtain ⟨hlks, -⟩ := WOpen.leaf_live X X.rl R hR hloc p hpI ws hL w hwm
      icases wtxW_cells_acc K tx r false X $$ Hw with ⟨%Hbase, Hcells, Hwbc⟩
      icases viewCells_src_acc wq X.v Hbase k _ w.key
        (WOpen.leafSrc_live X X.rl R hR hloc _ hlks) $$ [Hcells] with ⟨%dk, Hkk, Hcb⟩
      · iframe; iframe #
      iexists w.key, dk
      iframe Hkk
      isplitl
      · iintro Hkk
        ihave Hc := Hcb $$ Hkk
        iapply Hwbc $$ Hc
      ipureintro
      have hbf := (lLeaf_flag X X.rl R hok hR hloc els pids Hp w hwl).2 rfl
      refine ⟨fun h => Or.inl ⟨hlk.2 (by simp [h]), by rw [hfl]; exact hbf⟩, fun h => ?_,
        fun h _ => ⟨w, hwl, h⟩⟩
      cases h' : T.cur !! n with
      | none => rfl
      | some _ =>
        have := hlk.1 (by rw [h']; rfl)
        simp at this; exact absurd this h
  icases Hk with ⟨%kb, %dk, Hkk, Hkb, %Hkb⟩
  try wp_auto
  wp_apply hEq nk k DFrac.discard dk n kb $$ [Hnk Hkk] as ⟨-, Hkk⟩
  · iframe; iframe #
  ihave Hw := Hkb $$ Hkk
  by_cases hkw' : ¬ n = kb
  · -- not found
    have hkw := hkw'
    have hnone : T.cur !! n = none := Hkb.2.1 (Ne.symm hkw)
    rw [decide_eq_false hkw]
    try wp_auto
    wp_bind (App (Val #_) (Val #()))
    iapply (wp_wand (Φ := fun v => iprop(⌜v = #()⌝ ∗ err_ptr ↦ GoInterface.ok enf ∗
      name ↦*{dq} n))) $$ [err Hkey Hlgp Hname]
    · unfold go_etcd_io.bbolt.errors.bboltErrVar
      icases Hbnf with ⟨%e2, #He2, %-, #Hfe2⟩
      ihave %Heq := typedPointsto_agree_wand _ _ _ _ _ $$ Hnf He2
      cases Heq
      iapply Hdf $$ [] err Hkey Hlgp Hname
      iright; iexact Hfe2
    iintro %vret ⟨%hvret, err, Hname⟩
    subst hvret
    wp_auto
    iapply HΦ
    rw [if_pos hnone]
    iframe; iframe #
  have hkw : n = kb := Classical.not_not.1 hkw'
  rw [decide_eq_true hkw]
  try wp_auto
  rcases Hkb.1 hkw.symm with ⟨hfound, hbf⟩ | ⟨hnone, hn0, hfl0⟩
  rotate_left
  · -- the empty name in an empty root bucket: `ErrIncompatibleValue`
    subst hfl0
    rw [decide_eq_true (show W32 0 &&& W32 1 = W32 0 by decide)]
    unfold go_etcd_io.bbolt.errors.bboltErrVar
    icases Hiv with ⟨%e, #He, %-, #Hfe⟩
    try wp_auto
    wp_bind (App (Val #_) (Val #()))
    iapply (wp_wand (Φ := fun v => iprop(⌜v = #()⌝ ∗ err_ptr ↦ GoInterface.ok e ∗ name ↦*{dq} n)))
      $$ [err Hkey Hlgp Hname]
    · iapply Hdf $$ [] err Hkey Hlgp Hname
      iright; iexact Hfe
    iintro %vret ⟨%hvret, err, Hname⟩
    subst hvret
    wp_auto
    iapply HΦ
    rw [if_pos hnone]
    iframe; iframe #
    iright; iframe #; ipureintro; exact hn0
  rw [decide_eq_false hbf]
  try wp_auto
  have hin : ∃ w ∈ lLeaf X X.rl pids, w.key = n := Hkb.2.2 hkw.symm hfound
  have hsome : T.cur.lookup n ≠ none := by
    intro h; rw [show T.cur.lookup n = T.cur !! n from rfl, h] at hfound; cases hfound
  -- `child := b.Bucket(newKey)`
  have hhg : ∀ c', R.bm !! n = some c' → X.handles !! c' = some (n, T.gen n) :=
    fun c' h => hgens.2.1 n c' (by unfold bktLoc; rw [hR]; exact h)
  wp_apply hBw K tx r false X X.rl R nk n (KeyR.heap DFrac.discard) (T.gen n) hR hloc hpm hwrt hhg
    $$ [Hw] as %cb ⟨%X1, Hw, -, -, %Hpost⟩
  · unfold keyR; iframe; iexact Hnk
  rcases Hpost with ⟨-, -, hnone⟩ | ⟨hbn, hcase, hok'⟩
  · have := PubW.wtxData_none_of X n hnone
    rw [← hcur] at this
    rw [this] at hfound; cases hfound
  obtain ⟨hok1, hd1⟩ := hok' hok
  obtain ⟨R1, C, hR1, hn1, hst1, hC, hcr, hrl1, hv1, hmv1, hg1, hwr1, hfl1, hsh1⟩ :=
    dbk_opened (GF := GF) T X X1 R cb n w.fl hok hcur hgens hwr hfl hR hbn hcase hok1
  have hR1' : X1.t.bs !! X1.rl = some R1 := by rw [hrl1]; exact hR1
  try wp_auto
  -- `child.ForEachBucket(…)`: no nested bucket, the callback never runs
  have hloc1 := PubW.bktLocalOK_of_wOK X1 hok1 cb C hC
  have hpm1 := PubW.pmFresh_of_wOK X1 hok1
  have hnb := allEnts_plain_nonroot X1 cb C hok1 hC (by rw [hrl1]; exact hcr)
  wp_apply hFeb K tx r false X1 cb _ hloc1 hpm1 hnb $$ [Hw] as %ferr ⟨%hferr, Hw⟩
  · iexact Hw
  subst hferr
  try wp_auto
  icases wtxW_heapOK' K tx r false X1 $$ Hw with ⟨Hw, %Hhok1⟩
  have hCtx : C.bv.tx' = tx := (Hhok1.2.2.1 cb C hC).1
  -- `delete(b.buckets, string(newKey))`
  have hl1 : X1.rl ∈ X1.liveB := hok1.2.2.2.2.2.1.1
  icases wtxW_bm_acc K tx r false X1 X1.rl R1 hR1' hl1 $$ Hw with ⟨Hbf, Hbm, Hbb⟩
  rw [hrl1]
  try wp_auto
  wp_apply wp_bytes_to_string $$ [Hnk] as -
  · iexact Hnk
  try wp_auto
  wp_apply wp_mapDelete $$ [Hbm] as Hbm
  · iexact Hbm
  ihave Hw := Hbb $$ %(GMap.delete n R1.bm) Hbf Hbm
  -- the child dead, `child.nodes = nil`, `child.rootNode = nil`
  have hC2 : (X1.setBkt X.rl (bUnopen R1 n)).t.bs !! cb = some C := by
    show (X1.t.bs.insert X.rl _) !! cb = _
    rw [GMap.lookup_insert_ne _ _ (Ne.symm hcr)]; exact hC
  ihave Hw := wtxW_killBkt K tx r false _ cb C hC2 $$ Hw
  icases wtxW_dead_nil K tx r false _ cb _ (killBkt_bs_none _ cb C) (killBkt_deadB _ cb C)
    (killBkt_liveB _ cb C) $$ Hw with ⟨Hnf, Hrnf, Hwb⟩
  try wp_auto
  rw [show (map.nil : Loc) = null from rfl]
  ihave Hw := Hwb $$ Hnf Hrnf
  -- `child.free()`
  iunfold wdbW at Hwdb
  icases Hwdb with ⟨Hwl, %Hwf⟩
  ihave Hwdb : wdbW (GF := GF) K tx X.v w $$ [Hwl]
  · unfold wdbW; iframe; ipureintro; exact Hwf
  have htxw : X1.t.mv.txid' = w.wtxid := by
    have h0 := hok1.1.2.2.2.1
    have hvt : X1.v.txid = w.C.txid := by rw [hv1, Hwf.2.2]; rfl
    apply BitVec.eq_of_toNat_eq
    unfold WDb.wtxid
    rw [toNat_W64_of_lt _ (by have := X1.t.mv.txid'.isLt; omega)]
    omega
  have hfp := dbk_freePre X1 cb C R1 n w.fl w.wtxid hok1 hwr1 hR1' hn1 hC hfl1 htxw
  obtain ⟨t, ht⟩ : ∃ t : RTree, C.ib.root' ≠ W64 0 → ltIs (pltree X1.v) cb t ∧
      t.pid = C.ib.root' ∧ w.fl.canFreeAll w.wtxid (t.pos.filterMap (pExt X1.v)) := by
    by_cases h0 : C.ib.root' = W64 0
    · exact ⟨RTree.mk 0 false [] [], fun h => absurd h0 h⟩
    · obtain ⟨t, h1, h2, h3⟩ := (hfp h0).2
      exact ⟨t, fun _ => ⟨h1, h2, h3⟩⟩
  have hX4 : ((X1.setBkt X.rl (bUnopen R1 n)).killBkt cb C).setDead cb (deadRec { C with ns := ∅ }) =
      delMid X1 cb C R1 n (deadRec { C with ns := ∅ }) := by
    unfold delMid; rw [hrl1]
  rw [hX4]
  have hpm0 : X1.t.pm = ∅ := hok1.1.2.1.1
  wp_apply hFree K tx r false (delMid X1 cb C R1 n (deadRec { C with ns := ∅ })) w cb
    (deadRec { C with ns := ∅ }) t (by unfold delMid; exact killBkt_bs_none _ cb C) (setDead_lookup _ _ _)
    (by unfold delMid WX.setDead; exact killBkt_liveB _ cb C) hCtx rfl
    (fun h0 => ⟨(hfp h0).1, hok1.2.2.2.2.2.2.2, (ht h0).1, (ht h0).2.1,
      fun pid _ => by show X1.t.pm !! pid = none; rw [hpm0]; rfl, (ht h0).2.2, htxw⟩)
    $$ [Hw Hwdb] as ⟨%X5, %w5, Hw, Hwdb, %Hfr⟩
  · iframe Hw
    rw [show (delMid X1 cb C R1 n (deadRec { C with ns := ∅ })).v = X.v from hv1]
    iexact Hwdb
  -- the records after the free: `delMid` with the child's dead record `D'`
  obtain ⟨D', hX5, hD⟩ : ∃ D', X5 = delMid X1 cb C R1 n D' ∧
      ((C.ib.root' = W64 0 ∧ D' = deadRec { C with ns := ∅ } ∧ w5 = w) ∨
       (C.ib.root' ≠ W64 0 ∧ ltIs (pltree X1.v) cb t ∧ t.pid = C.ib.root' ∧
         D' = { deadRec { C with ns := ∅ } with ib := { C.ib with root' := W64 0 } } ∧
         w5 = w.withFl (w.fl.freeAll w.wtxid (t.pos.filterMap (pExt X1.v))))) := by
    rcases Hfr with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
    · exact ⟨_, h1, Or.inl ⟨h0, rfl, h2⟩⟩
    · exact ⟨_, h1.trans (delMid_setDead _ _ _ _ _ _ _), Or.inr ⟨h0, (ht h0).1, (ht h0).2.1, rfl, h2⟩⟩
  subst hX5
  have hdo1 : objsDisj X1.t := Hhok1.2.1
  have hcr1 : cb ≠ X1.rl := by rw [hrl1]; exact hcr
  have hok5 := wOK_delMid T X1 cb C R1 n D' hok1 hwr1 hg1 hR1' hn1 hC hdo1 hfl1.2.2.1
  have hYrl : (delMid X1 cb C R1 n D').t.bs !! X.rl = some (bUnopen R1 n) := by
    rw [delMid_bs, if_neg hcr, ← hrl1, if_pos rfl]
  have hrl5 : (delMid X1 cb C R1 n D').rl = X.rl := hrl1
  have hv5 : (delMid X1 cb C R1 n D').v = X.v := hv1
  have hst5 : sameTreeB R (bUnopen R1 n) := hst1
  have Hp5 : lPath (delMid X1 cb C R1 n D') X.rl els pids :=
    (lPath_congr_bkt X _ X.rl R _ hv5 hR hYrl hst5 els pids).2 Hp
  have Hr5 : lRoutes (delMid X1 cb C R1 n D') X.rl els pids n :=
    (lRoutes_congr_bkt X _ X.rl R _ hv5 hR hYrl hst5 els pids n).2 Hr
  have hin5 : ∃ w ∈ lLeaf (delMid X1 cb C R1 n D') X.rl pids, w.key = n := by
    rw [lLeaf_congr_bkt X _ X.rl R _ hv5 hR hYrl hst5 pids]; exact hin
  -- `c.node()`
  have hloc5 := PubW.bktLocalOK_of_wOK _ hok5 X.rl _ hYrl
  icases wtxW_nodes_nonnull K tx r false _ X.rl _ hYrl $$ Hw with ⟨Hw, %Hnn⟩
  icases wtxW_matReady_path K tx r false _ X.rl _ hok5 hYrl hloc5 els pids Hp5 $$ Hw
    with ⟨Hw, %Hmr⟩
  try wp_auto
  wp_apply hNode K tx r false _ X.rl _ cur stk' els pids (DFrac.own 1) hYrl hloc5 Hp5 Hnn Hmr
    $$ [Hw Hcu Hs] as %l ⟨%X6, Hw, Hcu, Hs, %Hcn⟩
  · iframe
  obtain ⟨Hmg, Hok6f, Hloc6, B6, pid, HB6, Hlast, Hres⟩ := Hcn
  have hok6 := Hok6f hok5
  have hlf : leafFor X6 X.rl n l :=
    lRoutes_leafFor' _ X6 X.rl l els pids n hok5 Hp5 Hr5 Hmg ⟨B6, HB6, pid, Hlast, Hres⟩
  obtain ⟨B6', rl, bnd, HB6', Hrl, Hll, -, -⟩ := id hlf
  rw [HB6] at HB6'
  cases HB6'
  have hfd : wsFound rl.ws n := by
    rw [← hrl5] at Hp5 Hr5 Hmg HB6 hin5
    exact dbk_found _ X6 l B6 rl n els pids hok5 Hp5 Hr5 Hmg HB6 Hrl ⟨pid, Hlast, Hres⟩ hin5
  have hcl6 := Write.wOK_bktClean X6 hok6 X.rl B6 HB6
  have hnc := hcl6.2.2.2.2.2.2.2.1 l rl Hrl
  obtain ⟨-, B4, hB4, -, -, -, hlive4, -⟩ := id Hloc6
  rw [HB6] at hB4
  cases hB4
  have hlive6 := hlive4 l rl Hrl
  obtain ⟨-, k2, -, -, -, -, -, k8⟩ := matGrow_keepW Hmg
  icases wtxW_cells_acc K tx r false X6 $$ Hw with ⟨%Hbase6, Hcells, Hwbc⟩
  ihave Hw := Hwbc $$ Hcells
  icases wtxW_open K tx r false X6 $$ Hw with ⟨-, -, -, Hh, Hcv, Hsk, Hclose⟩
  ihave %Hok6 := wtxHeap_heapOK tx (DFrac.own 1) X6 $$ Hh
  icases wtxHeap_setNode_acc tx (DFrac.own 1) X6 X.rl B6 l rl HB6 Hrl $$ Hh
    with ⟨Hno, Hbo, Hf, Hrf, Hback⟩
  rw [decide_eq_true hlive6]
  ihave Hkr : keyR (GF := GF) X6.v nk (KeyR.heap DFrac.discard) n $$ []
  · unfold keyR; iexact Hnk
  try wp_auto
  wp_apply hDel X6.v l X.rl rl wq nk n (KeyR.heap DFrac.discard) hnc.2.1 hnc.2.2.2.1
    hnc.2.2.2.2.2.1 Hbase6 $$ [Hno Hcv Hkr] as ⟨Hpost, Hcv, -⟩
  · iframe; try iframe #
  icases Hpost with (⟨%Hnf, -⟩ | ⟨-, %sl, Hno⟩)
  · exact absurd hfd Hnf
  have hpar : (rl.withEntsU sl (rl.ins.eraseIdx (wsIdx rl.ws n)) (wsDelAt rl.ws n) true).nv.parent'
      ≠ l := Hok6.2.2.2.1 X.rl B6 l rl HB6 Hrl
  ihave Hh := Hback $$ %(rl.withEntsU sl (rl.ins.eraseIdx (wsIdx rl.ws n)) (wsDelAt rl.ws n) true)
    %hpar [Hno] [Hbo] [Hf] Hrf
  · iexact Hno
  · iexact Hbo
  · iexact Hf
  ihave Hw := Hclose $$
    %(X6.setNode X.rl l (rl.withEntsU sl (rl.ins.eraseIdx (wsIdx rl.ws n)) (wsDelAt rl.ws n) true))
    [] Hh Hcv Hsk
  · ipureintro; rw [setNode_eq X6 X.rl l B6 _ HB6]; exact ⟨rfl, rfl, rfl⟩
  -- the post
  have h6rl : X6.rl = X.rl := k2.trans hrl5
  have hbmn : B6.bm !! n = none := by
    obtain ⟨B, hB, e⟩ := k8 X.rl B6 HB6
    rw [hYrl] at hB; cases hB; rw [e]; exact GMap.lookup_delete _ _
  have hdel : deleteOK (GF := GF) T r n X
      (X6.setNode X.rl l (rl.withEntsU sl (rl.ins.eraseIdx (wsIdx rl.ws n)) (wsDelAt rl.ws n) true))
      w w5 := by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := dbk_post (GF := GF) T r X X1 X6 cb C R1 n D' w w5
      l B6 rl sl _ t hok hcur hgens hwr hfl hsome hok1 hd1 hR1 hn1 hC hcr hrl1 hv1 hmv1 hg1 hwr1
      hfl1 hdo1 htxw hsh1 hD Hmg hok6 Hok6.2.1 HB6 Hrl hlf hfd (dbkDelAt_len _ _ _ hnc.2.2.1 hfd)
    have hwc1 : wrCurFacts T X1 := by
      rcases hcase with ⟨-, h⟩ | hop
      · subst h; exact hwc
      · exact wrCurFacts_bktOpened T X X1 cb n (T.gen n) hop hok hwc
    have hwc5 := wrCurFacts_delMid T X1 cb C R1 n D' hok1 hok5 hwr1 hg1 hR1' hn1 hwc1
    have hwc6 := wrCurFacts_matGrow T _ X6 X.rl hok5 Hmg hwc5
    have hwc7 := wrCurFacts_dropRoot T X6 n l B6 rl sl (rl.ins.eraseIdx (wsIdx rl.ws n)) hok6 (by rw [h6rl]; exact HB6) Hrl
      (by rw [h6rl]; exact hlf) hbmn hwc6
    rw [h6rl] at hwc7
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, hwc7⟩
  try wp_auto
  wp_bind (App (Val #_) (Val #()))
  iapply (wp_wand (Φ := fun v => iprop(⌜v = #()⌝ ∗ err_ptr ↦ GoInterface.nil ∗ name ↦*{dq} n)))
    $$ [err Hkey Hlgp Hname]
  · iapply Hdf $$ [] err Hkey Hlgp Hname
    ileft; ipureintro; rfl
  iintro %vret ⟨%hvret, err, Hname⟩
  subst hvret
  wp_auto
  iapply HΦ
  rw [if_neg hsome]
  iframe
  isplitr
  · ipureintro; rfl
  iexists w5
  iframe
  isplitl [Hwdb]
  · rw [← hv1]; iexact Hwdb
  · ipureintro; exact hdel

end proof

end Write

end bbolt
end EtcdGrove
end Perennial
