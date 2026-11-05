/-
**`Bucket.Put`'s proof** (U7k, `notes/bbolt-proof-plan.md`): a writer's `Put` over `wtxW` (q = 1,
`boltTxDef_wtxW`), the handle's bucket (`wtxWQ_handle`, `hD1`), the checks, `cloneBytes`,
`Bucket.Cursor_i`, `seek_w`, `Cursor.node` (`wtxW_matReady_path`), `node.put` with `putEnt`, closed
by `putPost` and `boltTxDef_wclose`; the logger and the deferred line as `Tx.Commit_err`'s.
-/
module

public import Spec.go_etcd_io.bbolt.Bucket__Put
public import Spec.go_etcd_io.bbolt.cloneBytes
public import Spec.go_etcd_io.bbolt.Bucket__Cursor_i
public import Spec.go_etcd_io.bbolt.Cursor__seek_w
public import Spec.go_etcd_io.bbolt.Cursor__node
public import Spec.go_etcd_io.bbolt.node__put
public import Perennial.Spec.bytes.Equal
public import Proof.go_etcd_io.bbolt.Write.WOkLeafPut
public import Proof.go_etcd_io.bbolt.Write.WOkLeafPre
public import Proof.go_etcd_io.bbolt.Write.Retarget
public import Proof.go_etcd_io.bbolt.Read.PubWGet
public import Proof.go_etcd_io.bbolt.Read.LeafFor
public import Proof.go_etcd_io.bbolt.Read.WOpenH
public import Proof.go_etcd_io.bbolt.Read.WOpen
public import Proof.go_etcd_io.bbolt.Read.WCtx
public import Proof.go_etcd_io.bbolt.Inv.ShapeOpsBkt
public import Proof.go_etcd_io.bbolt.Inv.ShapeOpsMat
public import Proof.go_etcd_io.bbolt.Mmap.Logger
public import Proof.go_etcd_io.bbolt.Mmap.Infra
public import Proof.go_etcd_io.bbolt.Commit.AssembleLog
public import Proof.go_etcd_io.bbolt.Rebalance.HeapRbl
public import Proof.go_etcd_io.bbolt.Rebalance.NodeRblBase
public import Proof.go_etcd_io.bbolt.Spill.DerefHeap
import all Spec.go_etcd_io.bbolt.Api

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Write
section putwp
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The writer's `tx.db` field out of `wtxW` and back. -/
theorem putW_db_acc [HasExt osFsExt] (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) :
    wtxW (GF := GF) K tx r m X ⊢ K.core ∗ tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} K.db ∗
      (tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} K.db -∗ wtxW K tx r m X) := by
  unfold wtxW wtxCore
  iintro ⟨⟨#Hpkg, #Hcore, %Hc, #Hreg, Hheap, Hfills, Hbk, Hnl, Hdb, Hvo, Hst⟩, Hvc, Hmap⟩
  have hdb : r.db = K.db := Hc.1
  rw [hdb]
  iframe Hdb
  isplitr
  · iexact Hcore
  iintro Hdb
  iframe; iframe #
  ipureintro; exact ⟨rfl, Hc.2⟩

omit package_sem in
/-- A `[]byte` key whose bytes `R` lends is a good log argument (`%q`). -/
theorem logArgOk_bytes (R : IProp GF) (v : w8) (key : GoSlice) (kb : GoString)
    (h : R ⊢ ∃ dq : DFrac, key ↦*{dq} kb ∗ (key ↦*{dq} kb -∗ R)) :
    ⊢ logArgOk (GF := GF) R v (interface.mkOk (go.GoType.SliceType go.byte) #key) := by
  unfold interface.mkOk logArgOk
  iintro
  iright; iright; iright
  iexists key, kb
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  imodintro
  iintro HR
  iapply h $$ HR

omit package_sem in
/-- A bbolt error variable's value: not nil, formatted by `fmt`. -/
theorem bboltErrVar_get (a : Loc) :
    go_etcd_io.bbolt.errors.bboltErrVar (GF := GF) a ⊢
      ∃ e : GoInterface, a ↦□ e ∗ ⌜e ≠ GoInterface.nil⌝ ∗ fmtErrorOk e := by
  unfold go_etcd_io.bbolt.errors.bboltErrVar
  iintro ⟨%e, #He, %-, #Hf⟩
  iexists (GoInterface.ok e)
  iframe #
  ipureintro; intro h; cases h

theorem Bucket.Put.wp_writer [HasExt osFsExt]
    (hclone : cloneBytes.spec (GF := GF) (hG := hG))
    (hcur : Bucket.Cursor_i.spec (GF := GF) (hG := hG))
    (hseek : Cursor.seek_w.spec (GF := GF) (hG := hG))
    (hnode : Cursor.node.spec (GF := GF) (hG := hG))
    (hput : node.put.spec (GF := GF) (hG := hG))
    (hEq : bytes.Equal.spec (GF := GF) (hG := hG))
    (tx : Loc) (γ : BoltName) (T : TxView) (b : Loc) (n : GoString) (m : BktData)
    (key value : GoSlice) (kb vb : GoString) (dk : DFrac)
    (hD1 : ∀ X : WX, gensOK T X →
      ∀ b n, X.handles !! b = some (n, T.gen n) → bktLoc X n = some b) :
  {{ boltTx (GF := GF) tx γ 1 T ∗ boltBkt tx γ b n (T.gen n) ∗ key ↦*{dk} kb ∗ value ↦*□ vb ∗
      ⌜T.rw = true ∧ T.cur.lookup n = some m ∧ kb.length + vb.length ≤ bboltEntryMax⌝ }}
    (App (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"Put")) (Val #key)) (Val #value))
  {{ (err : GoInterface), RET #err; key ↦*{dk} kb ∗
      (if kb.length = 0 ∨ maxKeySize < kb.length
       then iprop(⌜err ≠ GoInterface.nil⌝ ∗ boltTx tx γ 1 T)
       else iprop(⌜err = GoInterface.nil⌝ ∗ boltTx tx γ 1 (T.setBkt n (m.insert kb vb)))) }} := by
  wp_start as ⟨Ht, #Hb, Hkey, #Hval, %Hpre⟩
  obtain ⟨hrw, Hm, hbnd⟩ := Hpre
  unfold boltTx boltBkt at *
  ihave Ht := (boltTxDef_wtxW _ _ tx T hrw).1 $$ Ht
  icases Ht with ⟨%K, %r, %c, %X, %HK, #Hfull, #Hvo, Hv, Hw, Hst, %Hf⟩
  obtain ⟨hKB, hKN, hTc⟩ := HK
  obtain ⟨hok, hcur', hbase, hgens, hwr⟩ := Hf
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
  icases wtxW_pkgInit K tx r true X $$ Hw with ⟨Hw, #Hpkg⟩
  icases putW_db_acc K tx r true X $$ Hw with ⟨#Hcore, Hdb, Hwdb⟩
  ihave #Hcore' : isBoltCoreP K.B K.N K.db K.p K.sp K.t0 $$ []
  · unfold BC.core; iexact Hcore
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
  wp_apply DB.Logger.wp_proof K.db lg Ht0.2.1 $$ []
  · iframe #; unfold dbLogger; iexact Hlgok
  try wp_auto
  wp_bind (App (Val (GoInstruction (Convert go.untypedBool go.bool))) _)
  wp_apply cm_logger_ne_discard lg Hlgty $$ [] as %bl -
  · iframe #; unfold dbLogger; iexact Hlgok
  have hR : (key ↦*{dk} kb : IProp GF) ⊢ ∃ dq : DFrac, key ↦*{dq} kb ∗ (key ↦*{dq} kb -∗ key ↦*{dk} kb) := by
    iintro H; iexists dk; iframe H; iintro H; iexact H
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ key_ptr ↦ key ∗ lg_ptr ↦ lg ∗
      key ↦*{dk} kb ∗
      ∃ f : GoFunc, defer ↦ f ∗ □ (∀ e : GoInterface, (⌜e = interface.nil⌝ ∨ fmtErrorOk e) -∗
        err_ptr ↦ e -∗ key_ptr ↦ key -∗ lg_ptr ↦ lg -∗ key ↦*{dk} kb -∗
        WP (App (Val #f) (Val #())) {{ v, ⌜v = #()⌝ ∗ err_ptr ↦ e ∗ key ↦*{dk} kb }})))) $$ [key lg defer Hkey]
  · cases bl
    · wp_auto
      iframe
      isplitr
      · ipureintro; rfl
      imodintro
      iintro %e - Herr - - Hk
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
        (key ↦*{dk} kb) _ (by decide) (by decide) rfl $$ Hlgok' [Hsl] [] [Hkey] as Hsl Hkey
      · iframe
      · try simp only [List.zip_cons_cons, List.zip_nil_left]
        isplitl
        · iapply logArgOk_bytes _ _ key kb hR
        · iempintro
      · iexact Hkey
      try wp_auto
      isplitr
      · ipureintro; rfl
      iframe
      imodintro
      iintro %e Hen Herr Hkp Hlgp Hk
      wp_auto
      icases Hen with (%he | #Hfe)
      · subst he
        wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl2 ⟨Hsl2, -⟩
        try wp_auto
        wp_apply wp_boltLog li _ _ [W8 113] _ [interface.mkOk (go.GoType.SliceType go.byte) #key] _
          (key ↦*{dk} kb) _ (by decide) (by decide) rfl $$ Hlgok' [Hsl2] [] [Hk] as Hsl2 Hk
        · iframe
        · try simp only [List.zip_cons_cons, List.zip_nil_left]
          isplitl
          · iapply logArgOk_bytes _ _ key kb hR
          · iempintro
        · iexact Hk
        try wp_auto
        iframe; try (ipureintro; rfl)
      · cases e with
        | nil =>
          wp_auto
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %sl2 ⟨Hsl2, -⟩
          try wp_auto
          wp_apply wp_boltLog li _ _ [W8 113] _ [interface.mkOk (go.GoType.SliceType go.byte) #key] _
            (key ↦*{dk} kb) _ (by decide) (by decide) rfl $$ Hlgok' [Hsl2] [] [Hk] as Hsl2 Hk
          · iframe
          · try simp only [List.zip_cons_cons, List.zip_nil_left]
            isplitl
            · iapply logArgOk_bytes _ _ key kb hR
            · iempintro
          · iexact Hk
          try wp_auto
          iframe; try (ipureintro; rfl)
        | ok ii =>
          wp_auto
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %sl2 ⟨Hsl2, -⟩
          try wp_auto
          wp_apply wp_boltLog li _ _ [W8 113, W8 118] _
            [interface.mkOk (go.GoType.SliceType go.byte) #key, GoInterface.ok ii] _
            (key ↦*{dk} kb) _ (by decide) (by decide) rfl $$ Hlgok' [Hsl2] [] [Hk] as Hsl2 Hk
          · simp only [show sint.nat (W64 (0 + 1)) = 1 from rfl, List.set_cons_succ, List.set_cons_zero]
            iexact Hsl2
          · try simp only [List.zip_cons_cons, List.zip_nil_left]
            isplitl
            · iapply logArgOk_bytes _ _ key kb hR
            isplitl
            · iapply logArgOk_of_fmtErrorOk _ _ (by simp [methodVerbs]) (GoInterface.ok ii) $$ Hfe
            · iempintro
          · iexact Hk
          try wp_auto
          iframe; try (ipureintro; rfl)
  iintro %v ⟨%hv, Hkp, Hlgp, Hkey, %f, Hdefer, #Hdf⟩
  subst hv
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
  ihave #Hep : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.errors $$ []
  · iPkgInit
  ihave #Hei : (go_etcd_io.bbolt.errors.bboltErrorsInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hep
  unfold go_etcd_io.bbolt.errors.bboltErrorsInit go_etcd_io.bbolt.errors.bboltErrorsVars
  icases Hei with ⟨%_, #-, %_, #-, -, -, -, -, -, -, -, -, -, -, -, #EKR, #EKL, -, -, #EIV, -, -⟩
  ihave %Hkl := ownSlice_len _ _ _ $$ Hkey
  by_cases hk0 : kb.length = 0
  · icases bboltErrVar_get _ $$ EKR with ⟨%e, #He, %Hne, #Hfe⟩
    have hl0 : key.len = W64 0 := by
      obtain ⟨h1, h2⟩ := Hkl
      rw [hk0] at h1
      word
    rw [decide_eq_true hl0]
    wp_auto
    wp_bind (App (Val #f) (Val #()))
    iapply (wp_wand (Φ := fun v => iprop(⌜v = #()⌝ ∗ err_ptr ↦ e ∗ key ↦*{dk} kb))) $$
      [err Hkp Hlgp Hkey]
    · iapply Hdf $$ [] err Hkp Hlgp Hkey
      iright; iexact Hfe
    iintro %vret ⟨%hvret, err, Hkey⟩
    subst hvret
    wp_auto
    iapply HΦ
    iframe Hkey
    rw [if_pos (Or.inl hk0)]
    isplitr
    · ipureintro; exact Hne
    iapply (boltTxDef_wtxW _ _ tx T hrw).2
    iexists K, r, c, X
    iframe; iframe #
    ipureintro; exact ⟨⟨hKB, hKN, hTc⟩, hok, hcur', hbase, hgens, hwr⟩
  have hl0 : key.len ≠ W64 0 := by
    obtain ⟨h1, h2⟩ := Hkl
    intro h; rw [h] at h1; exact hk0 h1
  rw [decide_eq_false hl0]
  wp_auto
  have hZ : sint.Z key.len = (kb.length : Int) := by
    obtain ⟨h1, h2⟩ := Hkl
    simp only [sint.nat, sint.Z] at h1 h2 ⊢
    omega
  have hmk : sint.Z (W64 32768) = 32768 := by decide
  rw [hmk, hZ]
  by_cases hkL : maxKeySize < kb.length
  · rw [decide_eq_true (show (32768 : Int) < kb.length by unfold maxKeySize at hkL; omega)]
    icases bboltErrVar_get _ $$ EKL with ⟨%e, #He, %Hne, #Hfe⟩
    wp_auto
    wp_bind (App (Val #f) (Val #()))
    iapply (wp_wand (Φ := fun v => iprop(⌜v = #()⌝ ∗ err_ptr ↦ e ∗ key ↦*{dk} kb))) $$
      [err Hkp Hlgp Hkey]
    · iapply Hdf $$ [] err Hkp Hlgp Hkey
      iright; iexact Hfe
    iintro %vret ⟨%hvret, err, Hkey⟩
    subst hvret
    wp_auto
    iapply HΦ
    iframe Hkey
    rw [if_pos (Or.inr hkL)]
    isplitr
    · ipureintro; exact Hne
    iapply (boltTxDef_wtxW _ _ tx T hrw).2
    iexists K, r, c, X
    iframe; iframe #
    ipureintro; exact ⟨⟨hKB, hKN, hTc⟩, hok, hcur', hbase, hgens, hwr⟩
  rw [decide_eq_false (show ¬ (32768 : Int) < kb.length by unfold maxKeySize at hkL; omega)]
  wp_auto
  ihave %Hvl := ownSlice_len _ _ _ $$ Hval
  have hvZ : ¬ sint.Z (W64 2147483646) < sint.Z value.len := by
    obtain ⟨h1, h2⟩ := Hvl
    have hmv : sint.Z (W64 2147483646) = 2147483646 := by decide
    rw [hmv]
    simp only [sint.nat, sint.Z] at h1 h2 ⊢
    unfold bboltEntryMax at hbnd
    omega
  rw [decide_eq_false hvZ]
  wp_auto
  wp_apply hclone key kb dk $$ [Hkey] as %nk ⟨Hnk, Hnkc, Hkey⟩
  · iframe #; iexact Hkey
  imod ownSlice_persist nk _ _ $$ Hnk with #Hnk
  try wp_auto
  obtain ⟨B, hB⟩ := PubW.bktLoc_rec X hok n b hbl
  have hloc := PubW.bktLocalOK_of_wOK X hok b B hB
  have hpm := PubW.pmFresh_of_wOK X hok
  icases wtxW_cursor_acc K tx r true X b B hB $$ Hw with ⟨-, -, Hsk, %dt, Htx, Hwbc⟩
  wp_apply hcur K tx r true 1 b dt $$ [Hsk Htx] as %cu ⟨%stk, Hc, Hs, Hcap, Hsk, Htx⟩
  · iframe; iframe #
  ihave Hw := Hwbc $$ Hsk Htx
  try wp_auto
  wp_apply hseek K tx r true X b cu stk [] nk kb (KeyR.heap DFrac.discard) hloc hpm $$
    [Hw Hc Hs Hcap] as %k %vl %fl ⟨%stk', %els, %pids, Hw, Hc, Hs, Hcap, -, %Hrt, Hkv⟩
  · iframe; unfold keyR; iexact Hnk
  try wp_auto
  obtain ⟨Hp, Hr⟩ := Hrt
  obtain ⟨p, ws, ⟨j, hpj⟩, hL, hle⟩ := WOpen.lPath_leaf X b B hB hloc els pids Hp
  have hI := WOpen.lPath_posI X b B hB hloc els pids Hp j p hpj
  have hroot : b ≠ X.rl := Write.bktLoc_ne_root X hwr n b hbl
  have hplain := leaf_plain_nonroot X b B hok hB hroot p hI ws hL
  have hand : ∀ f : w32, f &&& W32 1 = W32 0 ↔ ¬ isBktFlag f := by
    intro f; unfold isBktFlag; simp
  have hkne : kb ≠ [] := fun h => hk0 (by rw [h]; rfl)
  rw [hle]
  wp_bind (If (If _ _ _) _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ wtxW (GF := GF) K tx r true X))) $$
    [Hw flags Hkv]
  · cases hw : ws[wsIdx ws kb]? with
    | none =>
      icases Hkv with %Hnil
      obtain ⟨rfl, rfl, rfl⟩ := Hnil
      wp_apply hEq nk slice.nil DFrac.discard DFrac.discard kb [] $$ [] as ⟨-, -⟩
      · iframe #; iapply ownSlice_nil
      rw [decide_eq_false hkne]
      wp_auto
      iframe
      ipureintro; rfl
    | some w =>
      icases Hkv with ⟨%Hkw, #Hks, #Hvs⟩
      have hwm : w ∈ ws := List.mem_of_getElem? hw
      obtain ⟨hlks, hlvs⟩ := WOpen.leaf_live X b B hB hloc p hI ws hL w hwm
      icases wtxW_cells_acc K tx r true X $$ Hw with ⟨%Hbase, Hcells, Hwbc⟩
      icases viewCells_src_acc wq X.v Hbase k _ w.key
        (WOpen.leafSrc_live X b B hB hloc _ hlks) $$ [Hcells] with ⟨%dk', Hkk, Hcb⟩
      · iframe; iframe #
      wp_apply hEq nk k DFrac.discard dk' kb w.key $$ [Hkk] as ⟨-, Hkk⟩
      · iframe; iframe #
      ihave Hcells := Hcb $$ Hkk
      ihave Hw := Hwbc $$ Hcells
      by_cases hk : kb = w.key
      · rw [decide_eq_true hk]
        wp_auto
        have hb : fl &&& W32 1 = W32 0 := by rw [Hkw.2]; exact (hand _).2 (hplain w hwm)
        rw [decide_eq_true hb]
        wp_auto
        iframe
        ipureintro; rfl
      · rw [decide_eq_false hk]
        wp_auto
        iframe
        ipureintro; rfl
  iintro %v ⟨%hv, Hw⟩
  subst hv
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
  icases wtxW_open K tx r true X3 $$ Hw with ⟨-, -, -, Hh, Hcv, Hsk, Hclose⟩
  ihave %Hok3 := wtxHeap_heapOK tx (DFrac.own 1) X3 $$ Hh
  have Htx3 : B3.bv.tx' = tx := Hok3.2.2.1 b B3 HB3
  icases wtxHeap_setNode_acc tx (DFrac.own 1) X3 b B3 l rl HB3 Hrl $$ Hh
    with ⟨Hno, Hbo, Hf, Hrf, Hback⟩
  rw [decide_eq_true hlive3]
  unfold txFields
  icases Hf with ⟨Hf1, Hf2, Hmeta, Hpages, Hf5, Hf6, Hmv, Hpm, Hbufs⟩
  have hpg3 : 0 < X3.t.mv.pgid'.toNat := by have := hok3.1.2.2.1; omega
  wp_apply hput X3.v l b rl tx X3.t.t.meta' X3.t.mv DFrac.discard (DFrac.own 1) wq nk nk value kb kb vb
      (Src.own DFrac.discard) (Src.own DFrac.discard) (Src.own DFrac.discard)
      (W64 0) (W32 0) hnc.1 hnc.2.1 hnc.2.2.2.1 hnc.2.2.2.2.2.1 (by simpa using hpg3)
      (by have := hk0; omega) (by have := hk0; omega) (by intro h; cases h)
      (by intro h; cases h) (by intro h; cases h) Hbase3
    $$ [Hno Hcv Hmeta Hmv] as ⟨%sl, %ins', Hno, Hcv, -, Hmeta, Hmv⟩
  · iframe; iframe #; unfold srcOwn; iframe #
  try wp_auto
  icases (objOwn_live_node _ _ _ _ _).1 $$ Hno with ⟨Hn5, Hins5, Hcap5, Hws5, Hch5, Hchcap5, Hkey5⟩
  ihave %Hinsl := BigSepL2.bigSepL2_length $$ Hws5
  ihave Hno := (objOwn_live_node _ l (DFrac.own 1) b _).2
    $$ [Hn5 Hins5 Hcap5 Hws5 Hch5 Hchcap5 Hkey5]
  · iframe
  have hpar : (rl.withEnts sl ins' (wsPutAt rl.ws kb (putEnt kb vb))).nv.parent' ≠ l :=
    Hok3.2.2.2.1 b B3 l rl HB3 Hrl
  ihave Hh := Hback $$ %(rl.withEnts sl ins' (wsPutAt rl.ws kb (putEnt kb vb))) %hpar [Hno] [Hbo]
    [Hf1 Hf2 Hmeta Hpages Hf5 Hf6 Hmv Hpm Hbufs] Hrf
  · rw [show putEnt kb vb = ⟨W32 0, W64 0, kb, vb, Src.own DFrac.discard, Src.own DFrac.discard⟩
      from rfl]
    iexact Hno
  · iexact Hbo
  · iframe
  ihave Hw := Hclose $$ %(X3.setNode b l (rl.withEnts sl ins' (wsPutAt rl.ws kb (putEnt kb vb))))
    [] Hh Hcv Hsk
  · ipureintro; rw [setNode_eq X3 b l B3 _ HB3]; exact ⟨rfl, rfl, rfl⟩
  have hpp := putPost T X X3 n b l B3 rl kb vb sl ins' hok hcur' hgens hwr hbl Hmg hok3 Hok3.2.1
    HB3 Hrl hlf (by have := hk0; omega) hbnd (by simpa [putEnt, NRec.withEnts] using Hinsl)
  obtain ⟨hok4, hd4, hg4, hwr4, hk4⟩ := hpp
  have hT' : T.setBkt n (m.insert kb vb) =
      TxView.ofC (c.1, c.2.1, c.2.2.1.insert n (m.insert kb vb), c.2.2.2) := by
    rw [hTc]; rfl
  have hsh : ∀ extra, txShape (GF := GF) r.n.pg X extra ⊢
      txShape r.n.pg (X3.setNode b l (rl.withEnts sl ins' (wsPutAt rl.ws kb (putEnt kb vb)))) extra :=
    fun extra => (txShape_matGrow _ X X3 b extra hloc Hmg).trans
      (txShape_putAt _ X3 b l B3 rl sl ins' kb (putEnt kb vb) extra HB3 Hrl
        (by rw [Hll]; exact entNoTok_plain _ _ _ (by simp [putEnt, isBktFlag])))
  have hv4 := hk4.v
  imod boltTxDef_wclose K tx r c _ X _ (T.setBkt n (m.insert kb vb)) ⊤ (by simp) hT' hk4 hsh
    ⟨hok4, hrw, by rw [hd4, Hm]; rfl, by rw [hv4]; exact hbase, hg4, hwr4⟩ $$
    [Hv Hw Hst] with Ht
  · rw [hKB, hv4]; iframe; iframe #
  wp_bind (App (Val #f) (Val #()))
  iapply (wp_wand (Φ := fun v => iprop(⌜v = #()⌝ ∗ err_ptr ↦ GoInterface.nil ∗ key ↦*{dk} kb))) $$
    [err Hkp Hlgp Hkey]
  · iapply Hdf $$ [] err Hkp Hlgp Hkey
    ileft; ipureintro; rfl
  iintro %vret ⟨%hvret, err, Hkey⟩
  subst hvret
  wp_auto
  iapply HΦ
  iframe Hkey
  rw [if_neg (by intro h; rcases h with h | h <;> contradiction)]
  isplitr
  · ipureintro; rfl
  rw [hKB, hKN]
  iexact Ht

end putwp
end Write

end bbolt
end EtcdGrove
end Perennial
