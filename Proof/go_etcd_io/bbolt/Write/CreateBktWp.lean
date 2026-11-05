/-
U7l (`notes/bbolt-proof-plan.md`): **the root bucket's `CreateBucket`** over the writer's records
(`wtxW`), for `Tx.CreateBucket`.
-/
module

public import Proof.go_etcd_io.bbolt.Write.CreateBktPost
public import Proof.go_etcd_io.bbolt.Write.CreateBkt
public import Proof.go_etcd_io.bbolt.Write.WOkLeafPre
public import Proof.go_etcd_io.bbolt.Write.Retarget
public import Proof.go_etcd_io.bbolt.Read.LeafFor
public import Proof.go_etcd_io.bbolt.Read.PubWBkt
public import Proof.go_etcd_io.bbolt.Read.PubWBktFl
public import Proof.go_etcd_io.bbolt.Read.WCtx
public import Proof.go_etcd_io.bbolt.Read.WOpenH
public import Proof.go_etcd_io.bbolt.Spill.DerefHeap
public import Proof.go_etcd_io.bbolt.Rebalance.HeapRbl
public import Proof.go_etcd_io.bbolt.Rebalance.NodeRblBase
public import Proof.go_etcd_io.bbolt.Commit.AssembleLog
public import Proof.go_etcd_io.bbolt.Mmap.Logger
public import Proof.go_etcd_io.bbolt.Mmap.Infra
public import Proof.go_etcd_io.bbolt.Inv.ShapeOpsOpen
public import Proof.go_etcd_io.bbolt.Inv.ShapeOpsGens
public import Proof.go_etcd_io.bbolt.Inv.ShapeOpsMat
public import Proof.go_etcd_io.bbolt.Inv.ShapeOpsBkt
public import Spec.go_etcd_io.bbolt.Bucket__Bucket_w
public import Spec.go_etcd_io.bbolt.Bucket__Cursor_i
public import Spec.go_etcd_io.bbolt.Cursor__seek_w
public import Spec.go_etcd_io.bbolt.Cursor__node
public import Spec.go_etcd_io.bbolt.node__put
public import Spec.go_etcd_io.bbolt.Bucket__write
public import Spec.go_etcd_io.bbolt.cloneBytes
public import Perennial.Spec.bytes.Equal

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

/-- What a successful `CreateBucket` of the absent `n` gives of the new records `X'`, from `X`. -/
def createOK (T : TxView) (r : TxReg) (n : GoString) (X X' : WX) : Prop :=
  wOK X' ∧ wtxData X' = T.cur.insert n ∅ ∧ gensOK T X' ∧ wrFacts X' ∧ XclKeep X X' ∧
    ∀ extra, txShape (GF := GF) r.n.pg X extra ⊢ txShape r.n.pg X' extra

omit package_sem in
/-- The transaction's `db` field's share out of `wtxW` (`Mmap/TxAlloc`'s `wtxW_db_acc`). -/
theorem cb_db_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) :
    wtxW (GF := GF) K tx r m X ⊢ ⌜r.db = K.db⌝ ∗ reg tx K.B r ∗
      tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} r.db ∗ statsTok r m 1 ∗
      (tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} r.db -∗ statsTok r m 1 -∗ wtxW K tx r m X) := by
  unfold wtxW wtxCore
  iintro ⟨⟨#Hpkg, #Hcore, %Hr, #Hreg, Hh, Hfills, Hbk, Hnl, Hdbf, Hview, Hst⟩, Hcells, Hmap⟩
  iframe Hdbf Hst
  isplitr
  · ipureintro; exact Hr.1
  iframe #
  iintro Hdbf Hst
  iframe; iframe #
  ipureintro; exact Hr

omit package_sem in
theorem cb_core (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) :
    wtxW (GF := GF) K tx r m X ⊢ K.core ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗
      wtxW K tx r m X := by
  unfold wtxW wtxCore
  iintro ⟨⟨#Hp, #H, Hr⟩, Hc⟩
  iframe #; iframe

omit hos package_sem in
/-- A byte slice is a good log argument, lent by `R = s ↦*{dq} b`. -/
theorem logArgOk_bytes (s : GoSlice) (b : List w8) (dq : DFrac) (v : w8) :
    ⊢ logArgOk (GF := GF) (s ↦*{dq} b) v (interface.mkOk (go.GoType.SliceType go.byte) #s) := by
  unfold interface.mkOk logArgOk
  iright; iright; iright
  iexists s, b
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  imodintro
  iintro Hs
  iexists dq
  iframe
  iintro Hs; iexact Hs

omit hos package_sem in
theorem xclKeep_trans {X Y Z : WX} (h1 : XclKeep X Y) (h2 : XclKeep Y Z) : XclKeep X Z :=
  ⟨h2.v.trans h1.v, h2.mv.trans h1.mv, fun fl h => h2.fl fl (h1.fl fl h)⟩

omit hos package_sem in
/-- `CreateBucket`'s error variables (persistent `errors.New` values, `fmt`-formatted). -/
theorem cb_errVars :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.errors ⊢
      go_etcd_io.bbolt.errors.bboltErrVar (globalAddr go_etcd_io.bbolt.errors.ErrBucketExists) ∗
      go_etcd_io.bbolt.errors.bboltErrVar
        (globalAddr go_etcd_io.bbolt.errors.ErrBucketNameRequired) ∗
      go_etcd_io.bbolt.errors.bboltErrVar
        (globalAddr go_etcd_io.bbolt.errors.ErrIncompatibleValue) := by
  iintro #Hep
  ihave #Hei : (go_etcd_io.bbolt.errors.bboltErrorsInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hep
  unfold go_etcd_io.bbolt.errors.bboltErrorsInit go_etcd_io.bbolt.errors.bboltErrorsVars
  icases Hei with ⟨%_, #-, %_, -, -, -, -, -, -, -, -, -, -, #Hx, #Hn, -, -, -, -, #Hi, -⟩
  iframe #

theorem Bucket.CreateBucket.wp_root
    (hBw : Bucket.Bucket_w.spec (GF := GF) (hG := hG))
    (hCur : Bucket.Cursor_i.spec (GF := GF) (hG := hG))
    (hSeek : Cursor.seek_w.spec (GF := GF) (hG := hG))
    (hNode : Cursor.node.spec (GF := GF) (hG := hG))
    (hPut : node.put.spec (GF := GF) (hG := hG))
    (hWrite : Bucket.write.spec (GF := GF) (hG := hG))
    (hClone : cloneBytes.spec (GF := GF) (hG := hG))
    (hEq : bytes.Equal.spec (GF := GF) (hG := hG))
    (K : BC) (tx : Loc) (r : TxReg) (X : WX) (T : TxView) (name : GoSlice) (n : GoString)
    (dq : DFrac) (hok : wOK X) (hcur : T.cur = wtxData X) (hgens : gensOK T X)
    (hwr : wrFacts X) (hkm : n.length ≤ maxKeySize) :
  {{ wtxW (GF := GF) K tx r true X ∗ name ↦*{dq} n }}
    (App (Val (X.rl @!! go.GoType.PointerType Bucket.ty @!! go!"CreateBucket")) (Val #name))
  {{ (b : Loc) (err : GoInterface), RET (PairV #b #err); name ↦*{dq} n ∗
      (if n.length = 0 then iprop(⌜err ≠ GoInterface.nil⌝ ∗ wtxW K tx r true X)
       else if T.cur.lookup n ≠ none then
         iprop(globalAddr go_etcd_io.bbolt.errors.ErrBucketExists ↦□ err ∗ wtxW K tx r true X)
       else iprop(⌜err = GoInterface.nil⌝ ∗ ∃ X' : WX, wtxW K tx r true X' ∗
         boltBktDef K.B tx b n (T.gen n) ∗ ⌜createOK (GF := GF) T r n X X'⌝)) }} := by
  wp_start as ⟨Hw, Hname⟩
  obtain ⟨R, hR⟩ : ∃ R, X.t.bs !! X.rl = some R := Option.isSome_iff_exists.1 hok.1.2.2.2.2.1
  icases cb_core K tx r true X $$ Hw with ⟨#Hkc, #Hpkg, Hw⟩
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
  icases wtxW_bkt_tx_acc K tx r true X X.rl R hR $$ Hw with ⟨%dqt, Htxf, Hwb⟩
  try wp_auto
  ihave Hw := Hwb $$ Htxf
  icases cb_db_acc K tx r true X $$ Hw with ⟨%Hrdb, -, Hdbf, Hst, Hwb⟩
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
  icases wtxW_bkt_tx_acc K tx r true X X.rl R hR $$ Hw with ⟨%dqt, Htxf, Hwb⟩
  try wp_auto
  ihave Hw := Hwb $$ Htxf
  icases cb_db_acc K tx r true X $$ Hw with ⟨-, -, Hdbf, Hst, Hwb⟩
  rw [Hrdb]
  try wp_auto
  rw [decide_eq_false Ht0.2.1]
  try wp_auto
  ihave Hw := Hwb $$ Hdbf Hst
  icases wtxW_bkt_tx_acc K tx r true X X.rl R hR $$ Hw with ⟨%dqt, Htxf, Hwb⟩
  try wp_auto
  ihave Hw := Hwb $$ Htxf
  icases wtxW_writable_acc K tx r true X $$ Hw with ⟨Hwrf, Hwb⟩
  have hwrt : X.t.t.writable' = true := hok.1.1
  rw [hwrt]
  try wp_auto
  ihave Hw := Hwb $$ Hwrf
  ihave %Hnl := ownSlice_len _ _ _ $$ Hname
  ihave #Hpke : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.errors $$ []
  · iPkgInit
  icases cb_errVars $$ Hpke with ⟨#Hex, #Hnr, #Hiv⟩
  by_cases hn0 : n.length = 0
  · have hl0 : name.len = W64 0 := by
      have h1 := Hnl.1; rw [hn0] at h1; simp only [sint.nat] at h1
      unfold sint.Z at Hnl; apply BitVec.eq_of_toInt_eq; simp; omega
    rw [decide_eq_true hl0]
    unfold go_etcd_io.bbolt.errors.bboltErrVar
    icases Hnr with ⟨%e, #He, %-, #Hfe⟩
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
    rw [if_pos hn0]
    iframe
    ipureintro; exact fun h => by cases h
  have hl0 : name.len ≠ W64 0 := by
    intro h; apply hn0; have h1 := Hnl.1; rw [h] at h1; exact h1
  rw [decide_eq_false hl0]
  try wp_auto
  wp_apply hClone name n dq $$ [Hname] as %nk ⟨Hnk, -, Hname⟩
  · iframe #; iframe
  imod ownSlice_persist nk _ _ $$ Hnk with #Hnk
  try wp_auto
  icases wtxW_cursor_acc K tx r true X X.rl R hR $$ Hw with ⟨#Hkc2, #Hreg, Hst, %dt, Htx, Hwbc⟩
  wp_apply hCur K tx r true 1 X.rl dt $$ [Hst Htx] as %cur ⟨%stk, Hcu, Hs, Hscap, Hst, Htx⟩
  · iframe; iframe #
  ihave Hw := Hwbc $$ Hst Htx
  try wp_auto
  have hloc := PubW.bktLocalOK_of_wOK X hok X.rl R hR
  have hpm := PubW.pmFresh_of_wOK X hok
  wp_apply hSeek K tx r true X X.rl cur stk [] nk n (KeyR.heap DFrac.discard) hloc hpm
    $$ [Hw Hcu Hs Hscap] as %k %vl %fl ⟨%stk', %els, %pids, Hw, Hcu, Hs, Hscap, -, %Hrt, Hkv⟩
  · iframe; unfold keyR; iexact Hnk
  obtain ⟨Hp, Hr⟩ := Hrt
  have hlk := root_lookup X R hok hR hloc els pids n Hp Hr
  rw [← hcur] at hlk
  unfold wsFound at hlk
  ihave Hk : (∃ (kb : List w8) (dk : DFrac), k ↦*{dk} kb ∗ (k ↦*{dk} kb -∗ wtxW K tx r true X) ∗
      ⌜(kb = n → (T.cur !! n).isSome ∧ ¬ (fl &&& W32 1 = W32 0)) ∧
        (kb ≠ n → T.cur !! n = none)⌝) $$ [Hw Hkv]
  · cases hm : (lLeaf X X.rl pids)[wsIdx (lLeaf X X.rl pids) n]? with
    | none =>
      rw [hm] at hlk
      icases Hkv with %hk0
      obtain ⟨hk0, -, -⟩ := hk0
      subst hk0
      iexists [], DFrac.own 1
      ihave Hnil : (slice.nil ↦*{DFrac.own 1} ([] : List w8)) $$ []
      · iapply ownSlice_nil
      iframe Hnil
      isplitl
      · iintro -; iexact Hw
      ipureintro
      refine ⟨fun h => absurd (by rw [← h]; rfl) hn0, fun _ => ?_⟩
      cases h : T.cur !! n with
      | none => rfl
      | some _ => exact absurd (hlk.1 (by rw [h]; rfl)) (by simp)
    | some w =>
      rw [hm] at hlk
      icases Hkv with ⟨%hk0, #Hks, -⟩
      obtain ⟨-, hfl⟩ := hk0
      obtain ⟨p, ws, ⟨j, hpj⟩, hL, hle⟩ := WOpen.lPath_leaf X X.rl R hR hloc els pids Hp
      have hpI := WOpen.lPath_posI X X.rl R hR hloc els pids Hp j p hpj
      have hwl : w ∈ lLeaf X X.rl pids := List.mem_of_getElem? hm
      have hwm : w ∈ ws := by rw [← hle]; exact hwl
      obtain ⟨hlks, -⟩ := WOpen.leaf_live X X.rl R hR hloc p hpI ws hL w hwm
      icases wtxW_cells_acc K tx r true X $$ Hw with ⟨%Hbase, Hcells, Hwbc⟩
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
      refine ⟨fun h => ⟨hlk.2 (by simp [h]), by rw [hfl]; exact hbf⟩, fun h => ?_⟩
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
  by_cases hkw : n = kb
  · obtain ⟨hfound, hbf⟩ := Hkb.1 hkw.symm
    rw [decide_eq_true hkw]
    try wp_auto
    rw [decide_eq_false hbf]
    unfold go_etcd_io.bbolt.errors.bboltErrVar
    icases Hex with ⟨%e, #He, %-, #Hfe⟩
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
    rw [if_neg hn0, if_pos (by intro h; rw [h] at hfound; cases hfound)]
    iframe; iframe #
  have hnew : T.cur !! n = none := Hkb.2 (Ne.symm hkw)
  rw [decide_eq_false hkw]
  try wp_auto
  -- the empty bucket's value
  icases typedPointsto_not_null_dup _ _ _ $$ bucket with ⟨bucket, %Hbkn⟩
  iStructNamed bucket
  ihave Hnil : (slice.nil ↦*{DFrac.own 1} ([] : List Inode)) $$ []
  · iapply ownSlice_nil
  have p1 : pageFits ([] : List InodeM) := by
    unfold pageFits; refine ⟨by decide, ?_, by simp⟩
    rw [show (pageBody true ([] : List InodeM)).length = 0 by rfl]; decide
  have p2 : insSize ([] : List Inode) = 16 + (pageBody true ([] : List InodeM)).length := by rfl
  have p3 : insSize ([] : List Inode) < 2 ^ 31 := by unfold insSize; simp
  have p4 : ([] : List InodeM).length < 0xFFFF := by decide
  wp_apply hWrite bucket_ptr «$v0_ptr» (zero_val InBucket) «$v1_ptr»
      ({ bucket' := null, isLeaf' := true, unbalanced' := false, spilled' := false,
         key' := slice.nil, pgid' := 0, parent' := null, children' := slice.nil,
         inodes' := slice.nil } : go_etcd_io.bbolt.node) [] []
      (DFrac.own 1) (DFrac.own 1) (DFrac.own 1) (fun _ => DFrac.own 1) (fun _ => DFrac.own 1)
      rfl p4 p1 p2 p3
    $$ [InBucket «$v0» rootNode «$v1» Hnil] as %val ⟨Hval, -, -, -, -, -, -, -⟩
  · iframe #; iframe
    iapply (BigSepL2.bigSepL2_nil (PROP := IProp GF)).mpr; iempintro
  imod ownSlice_persist val _ _ $$ Hval with #Hval
  try wp_auto
  -- `c.node()`
  icases wtxW_nodes_nonnull K tx r true X X.rl R hR $$ Hw with ⟨Hw, %Hnn⟩
  icases wtxW_matReady_path K tx r true X X.rl R hok hR hloc els pids Hp $$ Hw with ⟨Hw, %Hmr⟩
  wp_apply hNode K tx r true X X.rl R cur stk' els pids (DFrac.own 1) hR hloc Hp Hnn Hmr
    $$ [Hw Hcu Hs] as %l ⟨%X3, Hw, Hcu, Hs, %Hcn⟩
  · iframe
  obtain ⟨Hmg, Hok3f, Hloc3, B3, pid, HB3, Hlast, Hres⟩ := Hcn
  have hok3 := Hok3f hok
  have hlf : leafFor X3 X.rl n l :=
    lRoutes_leafFor' X X3 X.rl l els pids n hok Hp Hr Hmg ⟨B3, HB3, pid, Hlast, Hres⟩
  obtain ⟨B3', rl, bnd, HB3', Hrl, Hll, -, -⟩ := id hlf
  rw [HB3] at HB3'
  cases HB3'
  have hcl3 := Write.wOK_bktClean X3 hok3 X.rl B3 HB3
  have hnc := hcl3.2.2.2.2.2.2.2.1 l rl Hrl
  obtain ⟨hlB3, B4, hB4, -, -, -, hlive4, -⟩ := id Hloc3
  rw [HB3] at hB4
  cases hB4
  have hlive3 := hlive4 l rl Hrl
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ := matGrow_keepW Hmg
  icases wtxW_cells_acc K tx r true X3 $$ Hw with ⟨%Hbase3, Hcells, Hwbc⟩
  ihave Hw := Hwbc $$ Hcells
  icases wtxW_open K tx r true X3 $$ Hw with ⟨-, -, -, Hh, Hcv, Hsk, Hclose⟩
  ihave %Hok3 := wtxHeap_heapOK tx (DFrac.own 1) X3 $$ Hh
  have Htx3 : B3.bv.tx' = tx := Hok3.2.2.1 X.rl B3 HB3
  have HlB3 : X.rl ∈ X3.liveB := hlB3
  icases wtxHeap_setNode_acc tx (DFrac.own 1) X3 X.rl B3 l rl HB3 Hrl $$ Hh
    with ⟨Hno, Hbo, Hf, Hrf, Hback⟩
  rw [decide_eq_true hlive3, decide_eq_true HlB3]
  isimp only [objOwn] at Hbo
  icases Hbo with ⟨Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10⟩
  have Hroot1 : X.rl = B3.bv.tx'.[Tx, go!"root"] := by
    rw [Htx3, ← k2]; exact Hok3.1
  rw [if_pos Hroot1, Htx3]
  unfold txFields
  icases Hf with ⟨Hf1, Hf2, Hmeta, Hpages, Hf5, Hf6, Hmv, Hpm, Hbufs⟩
  have hpg3 : 0 < X3.t.mv.pgid'.toNat := by have := hok3.1.2.2.1; omega
  wp_apply hPut X3.v l X.rl rl tx X3.t.t.meta' X3.t.mv (DFrac.own 1) (DFrac.own 1) wq nk nk val n n
      (emptyBktVal (zero_val InBucket))
      (Src.own DFrac.discard) (Src.own DFrac.discard) (Src.own DFrac.discard)
      (W64 0) (W32 1) hnc.1 hnc.2.1 hnc.2.2.2.1 hnc.2.2.2.2.2.1 (by simpa using hpg3)
      (by omega) (by omega) (by intro h; cases h)
      (by intro h; cases h) (by intro h; cases h) Hbase3
    $$ [Hno Hcv Q2 Hmeta Hmv] as ⟨%sl, %ins', Hno, Hcv, Q2, Hmeta, Hmv⟩
  · iframe; iframe #; unfold srcOwn; simp only; unfold emptyBktVal; iframe #
  have hpage : B3.bv.page' = null :=
    hcl3.2.2.2.2.2.1 (hok3.1.2.1.2.2.2.2 B3 (by rw [k2]; exact HB3))
  icases (objOwn_live_node _ _ _ _ _).1 $$ Hno with ⟨Hn5, Hins5, Hcap5, Hws5, Hch5, Hchcap5, Hkey5⟩
  ihave %Hinsl := BigSepL2.bigSepL2_length $$ Hws5
  ihave Hno := (objOwn_live_node _ l (DFrac.own 1) X.rl _).2
    $$ [Hn5 Hins5 Hcap5 Hws5 Hch5 Hchcap5 Hkey5]
  · iframe
  have hpar : rl.nv.parent' ≠ l := Hok3.2.2.2.1 X.rl B3 l rl HB3 Hrl
  ihave Hh := Hback $$ %(rl.withEnts sl ins' (wsPutAt rl.ws n (createEnt n (zero_val InBucket))))
    %(by simpa [NRec.withEnts] using hpar) [Hno] [Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10]
    [Hf1 Hf2 Hmeta Hpages Hf5 Hf6 Hmv Hpm Hbufs] Hrf
  · unfold createEnt; iexact Hno
  · isimp only [objOwn]
    rw [if_pos Hroot1, Htx3, hpage]
    iframe
  · iframe
  ihave Hw := Hclose $$ %(X3.setNode X.rl l (rl.withEnts sl ins'
      (wsPutAt rl.ws n (createEnt n (zero_val InBucket))))) [] Hh Hcv Hsk
  · ipureintro; rw [setNode_eq X3 X.rl l B3 _ HB3]; exact ⟨rfl, rfl, rfl⟩
  have hcp := createPost T X X3 n (zero_val InBucket) l B3 rl sl ins' hok hcur hgens hwr Hmg hok3
    Hok3.2.1 HB3 Hrl hlf hnew (by omega) hkm rfl Hinsl
  have hsh4 : ∀ extra, txShape (GF := GF) r.n.pg X extra ⊢ txShape r.n.pg
      (X3.setNode X.rl l (rl.withEnts sl ins' (wsPutAt rl.ws n (createEnt n (zero_val InBucket)))))
      extra := by
    intro extra
    refine (txShape_matGrow r.n.pg X X3 X.rl extra hloc Hmg).trans ?_
    refine txShape_putAt r.n.pg X3 X.rl l B3 rl sl ins' n (createEnt n (zero_val InBucket)) extra
      HB3 Hrl ?_
    rw [Hll]
    exact entNoTok_inline X3.v B3 _ (emptyBktVal_root _ rfl)
  obtain ⟨X4, hX4⟩ : ∃ X4, X4 = X3.setNode X.rl l (rl.withEnts sl ins'
      (wsPutAt rl.ws n (createEnt n (zero_val InBucket)))) := ⟨_, rfl⟩
  rw [← hX4] at hcp hsh4
  rw [← hX4]
  obtain ⟨hok4, hd4, hgens4, hwr4, hk4⟩ := hcp
  have hrl4 : X4.rl = X.rl := by rw [hX4, setNode_eq X3 X.rl l B3 _ HB3]; exact k2
  obtain ⟨R4, hR4⟩ : ∃ R, X4.t.bs !! X.rl = some R := by
    rw [← hrl4]; exact Option.isSome_iff_exists.1 hok4.1.2.2.2.2.1
  have hloc4 := PubW.bktLocalOK_of_wOK X4 hok4 X.rl R4 hR4
  have hpm4 := PubW.pmFresh_of_wOK X4 hok4
  have hwrt4 : X4.t.t.writable' = true := hok4.1.1
  have hhg4 : ∀ c', R4.bm !! n = some c' → X4.handles !! c' = some (n, T.gen n) :=
    fun c' h => hgens4.2 n c' (by unfold bktLoc; rw [hrl4, hR4]; exact h)
  wp_apply hBw K tx r true X4 X.rl R4 nk n (KeyR.heap DFrac.discard) (T.gen n) hR4 hloc4 hpm4 hwrt4
    hhg4 $$ [Hw] as %b ⟨%X', Hw, -, Hcf, %Hpost⟩
  · unfold keyR; iframe; iexact Hnk
  have hin4 : (wtxData X4) !! n = some ∅ := by rw [hd4]; exact GMap.lookup_insert _ _ _
  rcases Hpost with ⟨-, -, hnone⟩ | ⟨hbn, hcase, hok'⟩
  · rw [← hrl4] at hnone
    have := PubW.wtxData_none_of X4 n hnone
    rw [hin4] at this; cases this
  icases Hcf with (%hb0 | #Hcf)
  · exact absurd hb0 hbn
  obtain ⟨hokX', hdX'⟩ := hok' hok4
  have hbX' : ∃ C, X'.t.bs !! b = some C := by
    rcases hcase with ⟨hbm, hXX⟩ | hop
    · subst X'
      exact Option.isSome_iff_exists.1 ((hok4.1.2.2.2.2.2 X.rl R4 hR4).2 n b hbm)
    · obtain ⟨B, C, w, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hX'⟩ := hop
      exact ⟨C, by rw [hX']; simp⟩
  obtain ⟨C, hC⟩ := hbX'
  have hrl' : X'.rl = X4.rl := by
    rcases hcase with ⟨-, hXX⟩ | hop
    · subst X'
      rfl
    · obtain ⟨B, C, w, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hX'⟩ := hop
      rw [hX']
  have hbrl : b ≠ X.rl := by
    rcases hcase with ⟨hbm, hXX⟩ | hop
    · subst X'
      exact hrl4 ▸ hwr4.2.2 R4 (hrl4 ▸ hR4) n b hbm
    · obtain ⟨B, C', w, hB, -, -, -, -, -, hcf, -, -, -, -, -, -, -, -, -⟩ := hop
      intro e
      rw [e] at hcf
      have := bobjs_bkt X4.t X.rl R4 hR4
      rw [Option.isNone_iff_eq_none] at hcf; rw [hcf] at this; cases this
  icases wtxW_heapOK' K tx r true X' $$ Hw with ⟨Hw, %Hhok'⟩
  ihave Hw : wtxWQ (GF := GF) K tx r true 1 X' $$ [Hw]
  · rw [wtxWQ_one]; iexact Hw
  icases wtxWQ_child_tx K tx r true 1 X' b C hC (by rw [hrl', hrl4]; exact hbrl) Hhok' $$ Hw
    with ⟨Hw, #Hbtx⟩
  icases wtxWQ_reg_rw K tx r true 1 X' $$ Hw with ⟨Hw, #Hreg', %Hrw⟩
  ihave Hw : wtxW (GF := GF) K tx r true X' $$ [Hw]
  · rw [← wtxWQ_one]; iexact Hw
  ihave #Hbkt : boltBktDef (GF := GF) K.B tx b n (T.gen n) $$ []
  · unfold boltBktDef
    iexists r
    iframe #
    unfold handleFrag
    simp only [Hrw, ite_true]
    iframe #
  have hpost : createOK (GF := GF) T r n X X' := by
    rcases hcase with ⟨-, hXX⟩ | hop
    · subst X'
      exact ⟨hok4, hd4, hgens4, hwr4, hk4, hsh4⟩
    · have hop' : bktOpened X4 X' X4.rl b n (T.gen n) := by rw [hrl4]; exact hop
      have hk' : XclKeep X4 X' := by
        obtain ⟨B, C', w, hB, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hX'⟩ := id hop
        exact ⟨by rw [hX'], by rw [hX'],
          fun fl h => PubW.flViewU_bktOpened_root' X4 X' b n (T.gen n) fl hok4 hokX' hop' h⟩
      refine ⟨hokX', by rw [hdX', hd4], ?_, ?_, xclKeep_trans hk4 hk', fun extra =>
        (hsh4 extra).trans (txShape_bktOpened r.n.pg X4 X' X.rl b n (T.gen n) extra hokX' hop)⟩
      · exact gensOK_bktOpened T X4 X' X.rl b n (T.gen n) hop hok4.2.2.2.2.1 (Nat.le_refl _)
          (fun _ => rfl) hgens4
      · exact PubW.wrFacts_bktOpened X4 X' X.rl b n (T.gen n) hop (hrl4 ▸ hok4.2.2.2.2.2.1.1)
          (by rw [hrl4, hR4]; rfl) hwr4
  wp_bind (App (Val #_) (Val #()))
  iapply (wp_wand (Φ := fun v => iprop(⌜v = #()⌝ ∗ err_ptr ↦ GoInterface.nil ∗ name ↦*{dq} n)))
    $$ [err Hkey Hlgp Hname]
  · iapply Hdf $$ [] err Hkey Hlgp Hname
    ileft; ipureintro; rfl
  iintro %vret ⟨%hvret, err, Hname⟩
  subst hvret
  wp_auto
  iapply HΦ
  rw [if_neg hn0, if_neg (by rw [hnew]; exact fun h => h rfl)]
  iframe Hname
  isplitr
  · ipureintro; rfl
  iexists X'
  iframe Hw; iframe #
  ipureintro; exact hpost

end proof

end Write

end bbolt
end EtcdGrove
end Perennial
