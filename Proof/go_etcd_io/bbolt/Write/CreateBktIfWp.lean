/-
U7l (`notes/bbolt-proof-plan.md`): **the root bucket's `CreateBucketIfNotExists`** over the writer's
records (`wtxW`), for `Tx.CreateBucketIfNotExists`: `Write/CreateBktWp`'s proof, with the cached
child returned early (its handle from `gensOK`) and an existing bucket entry opened and cached as
`Bucket.Bucket_w` does (`openBucket_w`, `wtxW_bktOpen`, `WOpen.wOK_bktOpened`).
-/
module

public import Proof.go_etcd_io.bbolt.Write.WrCur
public import Proof.go_etcd_io.bbolt.Write.CreateBktWp
public import Proof.go_etcd_io.bbolt.Read.WOpenWOK
public import Proof.go_etcd_io.bbolt.Read.WQ
public import Proof.go_etcd_io.bbolt.Rebalance.BktRbl
public import Spec.go_etcd_io.bbolt.Bucket__openBucket_w

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

/-- What `CreateBucketIfNotExists` of a present `n` gives of the records `X'`: the data kept. -/
def openOK (T : TxView) (r : TxReg) (X X' : WX) : Prop :=
  wOK X' ∧ wtxData X' = wtxData X ∧ gensOK T X' ∧ wrFacts X' ∧ XclKeep X X' ∧
    (∀ extra, txShape (GF := GF) r.n.pg X extra ⊢ txShape r.n.pg X' extra) ∧ wrCurFacts T X'

omit hos in
theorem cbi_ownMap_nonnull (l : Loc) (dq : DFrac) (m : GMap GoString Loc) :
    (l ↦${dq} m : IProp GF) ⊢ ⌜l ≠ null⌝ := by
  rw [ownMap_unseal]
  iintro H
  iNamed H
  ihave %Hp := heapPointsto_pos _ _ _ $$ Hown
  ipureintro
  intro h; subst h; simp [null] at Hp

theorem Bucket.CreateBucketIfNotExists.wp_root
    (hBw : Bucket.Bucket_w.spec (GF := GF) (hG := hG))
    (hCur : Bucket.Cursor_i.spec (GF := GF) (hG := hG))
    (hSeek : Cursor.seek_w.spec (GF := GF) (hG := hG))
    (hNode : Cursor.node.spec (GF := GF) (hG := hG))
    (hPut : node.put.spec (GF := GF) (hG := hG))
    (hWrite : Bucket.write.spec (GF := GF) (hG := hG))
    (hClone : cloneBytes.spec (GF := GF) (hG := hG))
    (hEq : bytes.Equal.spec (GF := GF) (hG := hG))
    (hopen : Bucket.openBucket_w.spec (GF := GF) (hG := hG))
    (K : BC) (tx : Loc) (r : TxReg) (X : WX) (T : TxView) (name : GoSlice) (n : GoString)
    (dq : DFrac) (hok : wOK X) (hcur : T.cur = wtxData X) (hgens : gensOK T X)
    (hwr : wrFacts X) (hwc : wrCurFacts T X) (hkm : n.length ≤ maxKeySize) :
  {{ wtxW (GF := GF) K tx r true X ∗ name ↦*{dq} n }}
    (App (Val (X.rl @!! go.GoType.PointerType Bucket.ty @!! go!"CreateBucketIfNotExists"))
      (Val #name))
  {{ (b : Loc) (err : GoInterface), RET (PairV #b #err); name ↦*{dq} n ∗
      (if n.length = 0 then iprop(⌜err ≠ GoInterface.nil⌝ ∗ wtxW K tx r true X)
       else iprop(⌜err = GoInterface.nil⌝ ∗ ∃ X' : WX, wtxW K tx r true X' ∗
         boltBktDef K.B tx b n (T.gen n) ∗
         ⌜if T.cur !! n = none then createOK (GF := GF) T r n X X' else openOK (GF := GF) T r X X'⌝))
    }} := by
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
  ihave %Hlgty := dbFixed_logPtrTyped _ _ K.db K.sp lg $$ Hfix Hlg
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  icases wtxW_bkt_tx_acc K tx r true X X.rl R hR $$ Hw with ⟨%dqt, Htxf, Hwb⟩
  try wp_auto
  ihave Hw := Hwb $$ Htxf
  icases wtxW_db_acc K tx r true X $$ Hw with ⟨%Hrdb, -, Hdbf, Hst, Hwb⟩
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
  icases wtxW_db_acc K tx r true X $$ Hw with ⟨-, -, Hdbf, Hst, Hwb⟩
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
  -- the cached child
  icases wtxW_hdlFrags K tx r true X $$ Hw with ⟨Hw, #Hhf⟩
  icases wtxW_buckets_fld K tx r true X X.rl R hR $$ Hw with ⟨Hbf, Hwb⟩
  try wp_auto
  ihave Hw := Hwb $$ Hbf
  icases wtxW_bm_acc K tx r true X X.rl R hR _ _ rfl rfl $$ Hw with ⟨Hbm, Hwb⟩
  ihave %Hbmn := cbi_ownMap_nonnull _ _ _ $$ Hbm
  ihave Hw := Hwb $$ Hbm
  rw [show (map.nil : Loc) = null from rfl, decide_eq_false Hbmn]
  try wp_auto
  wp_apply wp_bytes_to_string $$ [Hnk] as -
  · iexact Hnk
  icases wtxW_bkt_acc K tx r true X X.rl R hR $$ Hw with ⟨Ho, Hwb⟩
  isimp only [objOwn] at Ho
  icases Ho with ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10⟩
  try wp_auto
  wp_apply wp_map_lookup1 $$ [H9] as H9
  · iexact H9
  ihave Hw := Hwb $$ [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10]
  · isimp only [objOwn]; iframe
  try wp_auto
  have hcR := (hok.1.2.2.2.2.2 X.rl R hR)
  obtain ⟨c, hbmc⟩ | hbmc : (∃ c, R.bm !! n = some c) ∨ R.bm !! n = none := by
    cases R.bm !! n <;> simp
  · rw [hbmc]
    have hcn : c ≠ null := hcR.1.2.2.2.2.2.2.2.2.2.2 n c hbmc
    simp only [Option.getD_some]
    rw [decide_eq_false hcn]
    try wp_auto
    have hbl : bktLoc X n = some c := by unfold bktLoc; rw [hR]; exact hbmc
    ihave #Hcf := hdlFrags_lookup r X.handles c (n, T.gen n) (hgens.2.1 n c hbl) $$ Hhf
    obtain ⟨C, hC⟩ := Option.isSome_iff_exists.1 (hcR.2 n c hbmc)
    have hcrl : c ≠ X.rl := hwr.2.2 R hR n c hbmc
    icases wtxW_heapOK' K tx r true X $$ Hw with ⟨Hw, %Hhok⟩
    ihave Hw : wtxWQ (GF := GF) K tx r true 1 X $$ [Hw]
    · rw [wtxWQ_one]; iexact Hw
    icases wtxWQ_child_tx K tx r true 1 X c C hC hcrl Hhok $$ Hw with ⟨Hw, #Hbtx⟩
    icases wtxWQ_reg_rw K tx r true 1 X $$ Hw with ⟨Hw, #Hreg', %Hrw⟩
    ihave Hw : wtxW (GF := GF) K tx r true X $$ [Hw]
    · rw [← wtxWQ_one]; iexact Hw
    have hfound : T.cur !! n ≠ none := by rw [hcur]; exact PubW.wtxData_some_of X hok n c hbl
    wp_bind (App (Val #_) (Val #()))
    iapply (wp_wand (Φ := fun v => iprop(⌜v = #()⌝ ∗ err_ptr ↦ GoInterface.nil ∗ name ↦*{dq} n)))
      $$ [err Hkey Hlgp Hname]
    · iapply Hdf $$ [] err Hkey Hlgp Hname
      ileft; ipureintro; rfl
    iintro %vret ⟨%hvret, err, Hname⟩
    subst hvret
    wp_auto
    iapply HΦ
    rw [if_neg hn0]
    iframe Hname
    isplitr
    · ipureintro; rfl
    iexists X
    iframe Hw
    isplitr
    · unfold boltBktDef
      iexists r
      iframe #
      unfold handleFrag
      simp only [Hrw, ite_true]
      iframe #
    ipureintro
    rw [if_neg hfound]
    exact ⟨hok, rfl, hgens, hwr, ⟨rfl, rfl, fun _ h => h⟩, fun _ => .rfl, hwc⟩
  rw [hbmc]
  simp only [Option.getD_none]
  rw [decide_eq_true (show (zero_val Loc : Loc) = null from rfl)]
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
        (kb ≠ n → T.cur !! n = none)⌝ ∗
      □ (∀ w : WEntry, ⌜(lLeaf X X.rl pids)[wsIdx (lLeaf X X.rl pids) n]? = some w⌝ -∗
        ⌜fl = w.flags⌝ ∗ srcOwn X.v vl (leafSrc X X.rl w.vs) w.value)) $$ [Hw Hkv]
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
      isplitr
      · ipureintro
        refine ⟨fun h => absurd (by rw [← h]; rfl) hn0, fun _ => ?_⟩
        cases h : T.cur !! n with
        | none => rfl
        | some _ => exact absurd (hlk.1 (by rw [h]; rfl)) (by simp)
      imodintro
      iintro %w %hw
      exact absurd hw (by simp)
    | some w =>
      rw [hm] at hlk
      icases Hkv with ⟨%hk0, #Hks, #Hvs⟩
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
      isplitr
      · ipureintro
        have hbf := (lLeaf_flag X X.rl R hok hR hloc els pids Hp w hwl).2 rfl
        refine ⟨fun h => ⟨hlk.2 (by simp [h]), by rw [hfl]; exact hbf⟩, fun h => ?_⟩
        cases h' : T.cur !! n with
        | none => rfl
        | some _ =>
          have := hlk.1 (by rw [h']; rfl)
          simp at this; exact absurd this h
      imodintro
      iintro %w' %hw'
      cases hw'
      iframe #
      ipureintro; exact hfl
  icases Hk with ⟨%kb, %dk, Hkk, Hkb, %Hkb, #Hvl⟩
  try wp_auto
  wp_apply hEq nk k DFrac.discard dk n kb $$ [Hnk Hkk] as ⟨-, Hkk⟩
  · iframe; iframe #
  ihave Hw := Hkb $$ Hkk
  by_cases hkw : n = kb
  · obtain ⟨hfs, hbf⟩ := Hkb.1 hkw.symm
    have hm := hlk.1 hfs
    obtain ⟨w, hw, hwk⟩ : ∃ w, (lLeaf X X.rl pids)[wsIdx (lLeaf X X.rl pids) n]? = some w ∧
        w.key = n := by
      cases h : (lLeaf X X.rl pids)[wsIdx (lLeaf X X.rl pids) n]? with
      | none => rw [h] at hm; cases hm
      | some w => rw [h] at hm; exact ⟨w, rfl, by simpa using hm⟩
    have hfound : T.cur !! n ≠ none := fun h => by rw [h] at hfs; cases hfs
    obtain ⟨p, ws, ⟨j, hpj⟩, hL, hle⟩ := WOpen.lPath_leaf X X.rl R hR hloc els pids Hp
    have hI := WOpen.lPath_posI X X.rl R hR hloc els pids Hp j p hpj
    have hwl : w ∈ lLeaf X X.rl pids := List.mem_of_getElem? hw
    have hwm : w ∈ ws := by rw [← hle]; exact hwl
    obtain ⟨-, hlv⟩ := WOpen.leaf_live X X.rl R hR hloc p hI ws hL w hwm
    have hflag : isBktFlag w.flags := (lLeaf_flag X X.rl R hok hR hloc els pids Hp w hwl).2 rfl
    have hbmw : R.bm !! w.key = none := hwk ▸ hbmc
    rw [decide_eq_true hkw]
    try wp_auto
    rw [decide_eq_false hbf]
    icases Hvl $$ %w %hw with ⟨-, #Hvs⟩
    obtain ⟨hbv, hvs', hent, htk, hninl⟩ :=
      WOpen.leafBkt X X.rl R hR hloc p hI ws hL w hwm hflag hbmw
    have hsrc : leafSrc X X.rl w.vs = w.vs := by
      unfold leafSrc; rw [hR]; simp only; rw [if_neg hninl]
    rw [hsrc]
    have h16 : 16 ≤ w.value.length := by cases hbv.1 <;> assumption
    have hinl : inBucketRoot w.value = 0 → 16 < w.value.length := by
      intro h0
      have h1 := (hbv.2.1 h0).1.2.2.2.1
      have h2 : (inlinePage w.value).length = w.value.length - 16 := by
        unfold inlinePage bucketHeaderSize; simp
      omega
    icases wtxW_heapOK' K tx r true X $$ Hw with ⟨Hw, %Hok⟩
    have htxB : R.bv.tx' = tx := (Hok.2.2.1 X.rl R hR).1
    have hwrt : X.t.t.writable' = true := hok.1.1
    try wp_auto
    wp_apply hopen K tx r true X X.rl R vl w.vs w.value hR hwrt hlv h16 hinl $$ [Hw]
      as %c ⟨%C, Hw, Hco, Hfill, %Hcr⟩
    · iframe; iframe #
    obtain ⟨hcn, hrec⟩ := Hcr
    icases Hfill with ⟨%f, %Hnan, Hfp⟩
    icases wtxW_fill_fresh K tx r true X c f $$ [Hw Hfp] with ⟨Hw, Hfp, %Hfr⟩
    · iframe
    isimp only [objOwn] at Hco
    icases Hco with ⟨C1, C2, C3, C4, C5, C6, C7, C8, C9, C10⟩
    icases wtxW_bkt_fresh K tx r true X c _ $$ [Hw C1] with ⟨Hw, C1, %Hbo⟩
    · iframe
    ihave Hco : objOwn X.v c (DFrac.own 1) true (.bkt C) $$ [C1 C2 C3 C4 C5 C6 C7 C8 C9 C10]
    · isimp only [objOwn]; iframe
    icases wtxW_bktOpen K tx r true X X.rl R hR hloc.1 $$ Hw with ⟨Hbf, Hbm, Hcells, Hback⟩
    try wp_auto
    rw [show (map.nil : Loc) = null from rfl, decide_eq_false Hbmn]
    try wp_auto
    wp_apply wp_bytes_to_string $$ [Hnk] as -
    · iexact Hnk
    wp_apply wp_mapInsert $$ [Hbm] as Hbm
    · iexact Hbm
    imod Hback $$ %n %c %C %(T.gen n) Hbf Hcells Hbm Hco [Hfp] [] with ⟨Hw, #Hcf⟩
    · iexists f; iframe; ipureintro; exact Hnan
    · ipureintro; exact ⟨Hbo, Hfr.1, hrec.2.1, hrec.2.2.2.2.2.1, hrec.2.2.2.2.2.2.2.2⟩
    have hwa : w ∈ X.allEnts X.rl := by
      have hfa := WOpen.route_found_at X X.rl els pids n hloc Hp Hr
      obtain ⟨w', hw', hk'⟩ := (lRoutes_found' X X.rl els pids n hloc Hp Hr).2 (by
        unfold wsFound; rw [hw]; simp [hwk])
      have := hfa w' hw' hk'
      rw [hw] at this; cases this; exact hw'
    have hrec' : openedRec R.bv.tx' w.value w.vs C := by rw [htxB]; exact hrec
    have hplain : ∀ pg, bktLeafPg X.v.pages w.value pg → ∀ j < pageCount pg,
        leafFlags pg j % 2 = 0 := by
      intro pg hpg j hj
      by_cases h0 : inBucketRoot w.value = 0
      · rcases hpg with ⟨-, rfl⟩ | ⟨h0', -⟩
        · exact ((hbv.2.1 h0).1.2.2.2.2 j hj).2
        · exact absurd h0 h0'
      · exact (hbv.2.2 h0 pg hpg j hj).1
    obtain ⟨hokX', hdX'⟩ := WOpen.wOK_bktOpened X X.rl c R C w n (T.gen n) hok Hok.2.1 hR hwa hwk
      hflag hbmc Hbo hrec' hbv (hwk ▸ hent) htk hplain hcn
    have hop : bktOpened X ((X.setBkt X.rl { R with bm := R.bm.insert n c }).addBkt c C
        (n, T.gen n)) X.rl c n (T.gen n) := by
      obtain ⟨hib, htx, hrn, hnm, hbm', hns, hil, hni, -⟩ := hrec
      refine ⟨R, C, w, hR, hwa, hwk, hflag, hbmc, hcn,
        by rw [Hbo]; rfl, hib, by rw [htx, htxB], hrn, hnm, hbm', hns, ?_, hni, rfl⟩
      intro h0
      obtain ⟨h1, h2, h3⟩ := hil h0
      refine ⟨h1, h2, ?_⟩
      rcases h3 with ⟨-, a, b⟩ | ⟨a, b⟩
      · exact Or.inl ⟨by rcases hvs' with e | e <;> simp_all, a, b⟩
      · exact Or.inr ⟨a, b⟩
    obtain ⟨X', hX'⟩ : ∃ X', X' = (X.setBkt X.rl { R with bm := R.bm.insert n c }).addBkt c C
        (n, T.gen n) := ⟨_, rfl⟩
    rw [← hX'] at hop hokX' hdX'
    ihave Hw : wtxW (GF := GF) K tx r true X' $$ [Hw]
    · rw [hX']; iexact Hw
    obtain ⟨B', C', w', -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hXe⟩ := id hop
    have hCX : X'.t.bs !! c = some C' := by rw [hXe]; simp
    icases wtxW_heapOK' K tx r true X' $$ Hw with ⟨Hw, %Hhok'⟩
    ihave Hw : wtxWQ (GF := GF) K tx r true 1 X' $$ [Hw]
    · rw [wtxWQ_one]; iexact Hw
    have hcrl : c ≠ X'.rl := by
      rw [hXe]; intro e; rw [e] at Hbo
      have := bobjs_bkt X.t X.rl R hR
      rw [Hbo] at this; cases this
    icases wtxWQ_child_tx K tx r true 1 X' c C' hCX hcrl Hhok' $$ Hw with ⟨Hw, #Hbtx⟩
    icases wtxWQ_reg_rw K tx r true 1 X' $$ Hw with ⟨Hw, #Hreg', %Hrw⟩
    ihave Hw : wtxW (GF := GF) K tx r true X' $$ [Hw]
    · rw [← wtxWQ_one]; iexact Hw
    have hpost : openOK (GF := GF) T r X X' := by
      have hk' : XclKeep X X' :=
        ⟨by rw [hXe], by rw [hXe],
          fun fl h => PubW.flViewU_bktOpened_root' X X' c n (T.gen n) fl hok hokX' hop h⟩
      refine ⟨hokX', hdX', ?_, ?_, hk', fun extra =>
        txShape_bktOpened r.n.pg X X' X.rl c n (T.gen n) extra hokX' hop, ?_⟩
      · exact gensOK_bktOpened T X X' X.rl c n (T.gen n) hop hok.2.2.2.2.1 (Nat.le_refl _)
          (fun _ => rfl) (fun h => absurd rfl h) hgens
      · exact PubW.wrFacts_bktOpened X X' X.rl c n (T.gen n) hop hloc.1 (by rw [hR]; rfl) hwr
      · exact wrCurFacts_bktOpened T X X' c n (T.gen n) hop hok hwc
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
    rw [if_neg hn0]
    iframe Hname
    isplitr
    · ipureintro; rfl
    iexists X'
    iframe Hw
    isplitr
    · unfold boltBktDef
      iexists r
      iframe #
      unfold handleFrag
      simp only [Hrw, ite_true]
      iframe #
    ipureintro; rw [if_neg hfound]; exact hpost
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
  have Htx3 : B3.bv.tx' = tx := (Hok3.2.2.1 X.rl B3 HB3).1
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
    fun c' h => hgens4.2.1 n c' (by unfold bktLoc; rw [hrl4, hR4]; exact h)
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
        (hsh4 extra).trans (txShape_bktOpened r.n.pg X4 X' X.rl b n (T.gen n) extra hokX' hop), ?_⟩
      · exact gensOK_bktOpened T X4 X' X.rl b n (T.gen n) hop hok4.2.2.2.2.1 (Nat.le_refl _)
          (fun _ => rfl) (fun h => absurd hrl4.symm h) hgens4
      · exact PubW.wrFacts_bktOpened X4 X' X.rl b n (T.gen n) hop (hrl4 ▸ hok4.2.2.2.2.2.1.1)
          (by rw [hrl4, hR4]; rfl) hwr4
      · exact wrCurFacts_bktOpened T X4 X' b n (T.gen n) (hrl4 ▸ hop) hok4
          (wrCurFacts_createPost T X X3 n (zero_val InBucket) l B3 rl sl ins' hok hcur Hmg hok3 HB3 Hrl
            hlf hnew rfl hwc)
  wp_bind (App (Val #_) (Val #()))
  iapply (wp_wand (Φ := fun v => iprop(⌜v = #()⌝ ∗ err_ptr ↦ GoInterface.nil ∗ name ↦*{dq} n)))
    $$ [err Hkey Hlgp Hname]
  · iapply Hdf $$ [] err Hkey Hlgp Hname
    ileft; ipureintro; rfl
  iintro %vret ⟨%hvret, err, Hname⟩
  subst hvret
  wp_auto
  iapply HΦ
  rw [if_neg hn0]
  iframe Hname
  isplitr
  · ipureintro; rfl
  iexists X'
  iframe Hw; iframe #
  ipureintro; rw [if_pos hnew]; exact hpost

end proof

end Write

end bbolt
end EtcdGrove
end Perennial
