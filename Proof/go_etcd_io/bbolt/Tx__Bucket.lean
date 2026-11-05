/-
The proof of `Spec/go_etcd_io/bbolt/Tx__Bucket.lean` (U6g, `notes/bbolt-proof-plan.md`).
A reader (`wp_reader`): half of its `rdTxK` beside half of its root bucket (`rdTxK_root_split`),
`tx.root.Bucket(name)` by `Bucket.Bucket_r.spec` (the name caller-owned); a miss is no bucket of
the view's data (`rd_root_lookup_none`), a hit is one (`rd_root_lookup_some`) whose handle is the
opened child, over `RdHandleMint` (the handle's registry fragment; OPEN, reported). A writer
(`wp_writer`): OPEN, `Bucket.Bucket_w.spec` takes the name as `srcOwn` (persistent) and gives no
handle fragment.
-/
module

public import Spec.go_etcd_io.bbolt.Tx__Bucket
public import Proof.go_etcd_io.bbolt.Bucket__Bucket_r
public import Proof.go_etcd_io.bbolt.Read.Pub
public import Proof.go_etcd_io.bbolt.Read.GetFacts
public import Proof.go_etcd_io.bbolt.Commit.CheckSplit
public import Spec.go_etcd_io.bbolt.Bucket__Bucket_w
public import Proof.go_etcd_io.bbolt.Read.PubWBktFl
public import Proof.go_etcd_io.bbolt.Write.Retarget
public import Proof.go_etcd_io.bbolt.Inv.ShapeOpsOpen
public import Proof.go_etcd_io.bbolt.Inv.ShapeOpsGens
import all Spec.go_etcd_io.bbolt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem Tx.Bucket.wp_reader [HasExt osFsExt] (hmint : RdHandleMint (GF := GF))
    (hBr : Bucket.Bucket_r.spec (GF := GF) (hG := hG))
    (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (name : GoSlice) (n : GoString) (dq : DFrac)
    (hro : T.rw = false) :
  {{ boltTx (GF := GF) tx γ q T ∗ name ↦*{dq} n ∗ ⌜T.rw = true → q = 1⌝ }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"Bucket")) (Val #name))
  {{ (b : Loc), RET #b; boltTx tx γ q T ∗ name ↦*{dq} n ∗
      ((⌜T.cur.lookup n = none ∧ b = Loc.null⌝) ∨
       (⌜T.cur.lookup n ≠ none ∧ b ≠ Loc.null⌝ ∗ boltBkt tx γ b n (T.gen n))) }} := by
  wp_start as ⟨Ht, Hname, -⟩
  unfold boltTx boltBkt at *
  ihave Ht := (boltTx_rdTx _ _ tx q T hro).1 $$ Ht
  icases Ht with ⟨%db, Hr, #Hdb⟩
  ihave Hr := (rdTx_rdTxK _ _ tx .loan q T).1 $$ Hr
  icases Hr with ⟨%K, %v, %HK, Hk⟩
  obtain ⟨KB, KN, Kdb, Kp, Ksp, Kt0⟩ := K
  obtain ⟨hKB, hKN⟩ := HK
  simp only at hKB hKN
  subst hKB hKN
  icases (persistent_entails_left (rdTxK_view _ tx .loan q T v)) $$ Hk with ⟨Hk, %Hvw⟩
  obtain ⟨hT, hvwf⟩ := Hvw
  icases rdTxK_cur_acc _ tx .loan q T v $$ Hk with ⟨%r, #Hcore, #Hreg, #Hvo, %Hro, Hst, Hkb⟩
  ihave Hk := Hkb $$ Hst
  icases rdTxK_root_split _ tx .loan q T v $$ Hk with ⟨%ibp, %pp, Hk, Hrb, Hback⟩
  wp_auto
  rw [show tx.[Tx, go!"root"] = txRoot (GF := GF) tx from rfl]
  wp_apply hBr _ tx .loan q.half T v (txRoot (GF := GF) tx) (DFrac.own q.half) (rootVal v) ibp pp
    name (KeyR.heap dq) n (Or.inl rfl) $$ [Hk Hrb Hname] as %c ⟨Hk, Hrb, Hname, Hres⟩
  · unfold keyR; iframe
  ihave Hk := Hback $$ Hk Hrb
  simp only [keyR]
  icases Hres with (⟨%hc0, %hnn⟩ | ⟨%cv, ⟨%hcn, %hbe⟩, #Hcb⟩)
  · iapply HΦ
    isplitl [Hk]
    · iapply (boltTx_rdTx _ _ tx q T hro).2
      iexists db; iframe #
      iapply (rdTx_rdTxK _ _ tx .loan q T).2
      iexists _, v; iframe; ipureintro; exact ⟨rfl, rfl⟩
    iframe Hname
    ileft; ipureintro
    exact ⟨by rw [hT]; exact rd_root_lookup_none v hvwf n hnn, hc0⟩
  · ihave Hh := hmint _ _ db tx c r n Hro $$ [Hdb Hreg]
    · iframe #
    iapply HΦ
    isplitl [Hk]
    · iapply (boltTx_rdTx _ _ tx q T hro).2
      iexists db; iframe #
      iapply (rdTx_rdTxK _ _ tx .loan q T).2
      iexists _, v; iframe; ipureintro; exact ⟨rfl, rfl⟩
    iframe Hname
    iright
    isplitr
    · ipureintro
      exact ⟨by rw [hT]; exact rd_root_lookup_some v hvwf n cv hbe, hcn⟩
    unfold boltBktDef
    iexists r
    iframe #
    have hg : T.gen n = 0 := by rw [hT]; rfl
    rw [hg]
    iframe #
    iframe Hh
    isplitr
    · unfold rBkt; icases Hcb with ⟨%ibp', %pp', #HIB, #Htx, -⟩; iexact Htx
    simp only [Hro, Bool.false_eq_true, ite_false]
    iexists v, cv
    iframe #
    ipureintro; exact hbe

/-- **A writer's `Tx.Bucket`** (all of the transaction, U6x): over `wtxW` (`boltTxDef_wtxW`),
`tx.root.Bucket(name)` by `Bucket.Bucket_w.spec` on the root bucket (the name caller-owned, the
cached child's handle at `T.gen n` by `gensOK`); a miss is no bucket of the data
(`wtxData_none_of`), a cached child leaves the records as they are, and an open closes the new
records back (`boltTxDef_wclose`: `txShape_bktOpened`, `gensOK_bktOpened`, `wrFacts_bktOpened`,
and `flViewU_bktOpened_root'`, `Read/PubWBktFl`). -/
theorem Tx.Bucket.wp_writer [HasExt osFsExt]
    (hBw : Bucket.Bucket_w.spec (GF := GF) (hG := hG))
    (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (name : GoSlice) (n : GoString) (dq : DFrac)
    (hrw : T.rw = true) :
  {{ boltTx (GF := GF) tx γ q T ∗ name ↦*{dq} n ∗ ⌜T.rw = true → q = 1⌝ }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"Bucket")) (Val #name))
  {{ (b : Loc), RET #b; boltTx tx γ q T ∗ name ↦*{dq} n ∗
      ((⌜T.cur.lookup n = none ∧ b = Loc.null⌝) ∨
       (⌜T.cur.lookup n ≠ none ∧ b ≠ Loc.null⌝ ∗ boltBkt tx γ b n (T.gen n))) }} := by
  wp_start as ⟨Ht, Hname, %Hq⟩
  have hq := Hq hrw
  subst hq
  unfold boltTx boltBkt at *
  ihave Ht := (boltTxDef_wtxW _ _ tx T hrw).1 $$ Ht
  icases Ht with ⟨%K, %r, %c, %X, %HK, #Hfull, #Hvo, Hv, Hw, Hst, %Hf⟩
  obtain ⟨hKB, hKN, hTc⟩ := HK
  obtain ⟨hok, hcur', hbase, hgens, hwr⟩ := Hf
  icases wtxW_heapOK' K tx r true X $$ Hw with ⟨Hw, %Hhok⟩
  obtain ⟨R, hR⟩ : ∃ R, X.t.bs !! X.rl = some R := Option.isSome_iff_exists.1 hok.1.2.2.2.2.1
  have hloc := PubW.bktLocalOK_of_wOK X hok X.rl R hR
  have hpm := PubW.pmFresh_of_wOK X hok
  have hwrt : X.t.t.writable' = true := hok.1.1
  have hhg : ∀ c', R.bm !! n = some c' → X.handles !! c' = some (n, T.gen n) :=
    fun c' h => hgens.2 n c' (by unfold bktLoc; rw [hR]; exact h)
  have hrl : X.rl = txRoot (GF := GF) tx := Hhok.1
  wp_auto
  rw [show tx.[Tx, go!"root"] = txRoot (GF := GF) tx from rfl, ← hrl]
  iapply wp_fupd
  wp_apply hBw K tx r true X X.rl R name n (KeyR.heap dq) (T.gen n) hR hloc hpm hwrt hhg $$
    [Hw Hname] as %b ⟨%X', Hw, Hname, Hcf, %Hpost⟩
  · unfold keyR; iframe
  simp only [keyR]
  have hdT : T.cur = wtxData X := hcur'
  rcases Hpost with ⟨hb0, hXX, hnone⟩ | ⟨hbn, hcase, hok'⟩
  · -- a miss
    subst X'
    imodintro
    iapply HΦ
    iframe Hname
    isplitl [Hv Hw Hst]
    · iapply (boltTxDef_wtxW _ _ tx T hrw).2
      iexists K, r, c, X
      iframe; iframe #
      ipureintro; exact ⟨⟨hKB, hKN, hTc⟩, hok, hcur', hbase, hgens, hwr⟩
    ileft; ipureintro
    exact ⟨by rw [hdT]; exact PubW.wtxData_none_of X n hnone, hb0⟩
  · icases Hcf with (%hb0 | #Hcf)
    · exact absurd hb0 hbn
    obtain ⟨hokX', hdX'⟩ := hok' hok
    -- the child's record and its `tx` field
    have hbX' : ∃ C, X'.t.bs !! b = some C := by
      rcases hcase with ⟨hbm, hXX⟩ | hop
      · subst X'
        exact Option.isSome_iff_exists.1 ((hok.1.2.2.2.2.2 X.rl R hR).2 n b hbm)
      · obtain ⟨B, C, w, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hX'⟩ := hop
        exact ⟨C, by rw [hX']; simp⟩
    obtain ⟨C, hC⟩ := hbX'
    have hrl' : X'.rl = X.rl := by
      rcases hcase with ⟨-, hXX⟩ | hop
      · subst X'
        rfl
      · obtain ⟨B, C, w, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hX'⟩ := hop
        rw [hX']
    have hbrl : b ≠ X.rl := by
      rcases hcase with ⟨hbm, hXX⟩ | hop
      · subst X'
        exact hwr.2.2 R hR n b hbm
      · obtain ⟨B, C', w, hB, -, -, -, -, -, hcf, -, -, -, -, -, -, -, -, -⟩ := hop
        intro e
        rw [e] at hcf
        have := bobjs_bkt X.t X.rl R hR
        rw [Option.isNone_iff_eq_none] at hcf; rw [hcf] at this; cases this
    icases wtxW_heapOK' K tx r true X' $$ Hw with ⟨Hw, %Hhok'⟩
    ihave Hw : wtxWQ (GF := GF) K tx r true 1 X' $$ [Hw]
    · rw [wtxWQ_one]; iexact Hw
    icases wtxWQ_child_tx K tx r true 1 X' b C hC (hrl' ▸ hbrl) Hhok' $$ Hw with ⟨Hw, #Hbtx⟩
    have hbl' : bktLoc X' n = some b := by
      rcases hcase with ⟨hbm, hXX⟩ | hop
      · subst X'
        unfold bktLoc; rw [hR]; exact hbm
      · obtain ⟨B, C', w, hB, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hX'⟩ := hop
        unfold bktLoc; rw [hX']
        simp [GMap.lookup_insert_eq_iff, hbrl]
    have hsome : T.cur.lookup n ≠ none := by
      rw [hdT, ← hdX']
      exact PubW.wtxData_some_of X' hokX' n b hbl'
    icases wtxWQ_reg_rw K tx r true 1 X' $$ Hw with ⟨Hw, #Hreg, %Hrw⟩
    ihave Hw : wtxW (GF := GF) K tx r true X' $$ [Hw]
    · rw [← wtxWQ_one]; iexact Hw
    ihave #Hbkt : boltBktDef (GF := GF) (bnsOf γ.gs) tx b n (T.gen n) $$ []
    · unfold boltBktDef
      iexists r
      rw [← hKB]
      iframe #
      unfold handleFrag
      simp only [Hrw, ite_true]
      iframe #
    rcases hcase with ⟨-, hXX⟩ | hop
    · subst X'
      imodintro
      iapply HΦ
      iframe Hname
      isplitl [Hv Hw Hst]
      · iapply (boltTxDef_wtxW _ _ tx T hrw).2
        iexists K, r, c, X
        iframe; iframe #
        ipureintro; exact ⟨⟨hKB, hKN, hTc⟩, hok, hcur', hbase, hgens, hwr⟩
      iright
      iframe #
      ipureintro; exact ⟨hsome, hbn⟩
    · have hk : XclKeep X X' := by
        obtain ⟨B, C', w, hB, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hX'⟩ := id hop
        exact ⟨by rw [hX'], by rw [hX'],
          fun fl h => PubW.flViewU_bktOpened_root' X X' b n (T.gen n) fl hok hokX' hop h⟩
      have hvX : X'.v = X.v := hk.v
      have hgens' : gensOK T X' :=
        gensOK_bktOpened T X X' X.rl b n (T.gen n) hop hok.2.2.2.2.1 (Nat.le_refl _) (fun _ => rfl)
          hgens
      have hwr' : wrFacts X' :=
        PubW.wrFacts_bktOpened X X' X.rl b n (T.gen n) hop hok.2.2.2.2.2.1.1
          (by rw [hR]; rfl) hwr
      imod boltTxDef_wclose K tx r c c X X' T ⊤ (by simp) hTc hk
        (fun extra => txShape_bktOpened r.n.pg X X' X.rl b n (T.gen n) extra hokX' hop)
        ⟨hokX', hrw, by rw [hdT, hdX'], by rw [hvX]; exact hbase, hgens', hwr'⟩ $$
        [Hv Hw Hst] with Ht
      · rw [hKB, hvX]; iframe; iframe #
      imodintro
      iapply HΦ
      rw [hKB, hKN]
      iframe Ht Hname
      iright
      iframe #
      ipureintro; exact ⟨hsome, hbn⟩

theorem Tx.Bucket.wp_proof (hBr : ∀ [HasExt osFsExt], Bucket.Bucket_r.spec (GF := GF) (hG := hG))
    (hBw : ∀ [HasExt osFsExt], Bucket.Bucket_w.spec (GF := GF) (hG := hG)) :
    Tx.Bucket.spec (GF := GF) (hG := hG) := by
  intro _ tx γ q T name n dq
  by_cases hrw : T.rw = true
  · exact Tx.Bucket.wp_writer hBw tx γ q T name n dq hrw
  · exact Tx.Bucket.wp_reader rdHandleMint_holds hBr tx γ q T name n dq (Bool.eq_false_iff.2 hrw)

end proof

end bbolt
end EtcdGrove
end Perennial
