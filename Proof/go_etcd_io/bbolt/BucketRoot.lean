/-
A read transaction's root bucket (`&tx.root`), as the bucket API sees it: from `ownReadTx`
(`DBPred.lean`), the root bucket's `bktR` (`BucketRead.lean`) at some fraction, and the
transaction's statistics, with a way back (`ownReadTx_root`), at `structFieldRef Tx go!"root" txl`.

The view (`rootView`) is the reader's pages, its high-water mark, and the meta's root (not 0:
the root bucket is never inline). The pure facts it needs are the reader's (`readerOK`, in
`ownDB`): its tree well-formed, its pages inside the mapping (`readerViewOK`).
-/
module

public import Proof.go_etcd_io.bbolt.BucketRead
public import Proof.go_etcd_io.bbolt.DBPred
public import Proof.go_etcd_io.bbolt.DBBegin

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section root
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

/-- The root bucket's view, of the transaction `t` (at `txl`) with the meta `mv`. -/
def rootView (txl data : Loc) (ps : Nat) (r : Reader) (t : Tx) (mv : internal.common.Meta) :
    BktView :=
  { data := data, ps := W64 ps, pages := r.pages, hwm := r.hwm, root := mv.root'.root',
    ip := data, ipg := [], tx := txl, bkt := t.root', txv := t, seq := mv.root'.sequence' }

/-- What the root bucket's view is of the reader `r`. -/
def rootViewOK (txl data : Loc) (ps : Nat) (r : Reader) (V : BktView) : Prop :=
  V.tx = txl ∧ V.data = data ∧ V.ps = W64 ps ∧ V.pages = r.pages ∧ V.hwm = r.hwm ∧
  uint.nat V.root = r.root ∧ V.root ≠ W64 0 ∧ V.txv.writable' = false ∧
  V.bkt.buckets' = map.nil

/-- The reader's facts the root bucket's view needs (from `readerOK`, `dbOK`). -/
def readerViewOK (r : Reader) (data : Loc) (ps : Nat) : Prop :=
  treeWF r.pages r.hwm r.root ∧ r.root ≠ 0 ∧ data.locCar ≠ 0 ∧ ps < 2 ^ 64 ∧
  ∀ id pg, r.pages !! id = some pg → id * ps < 281474976710655

/-- The database's facts give an open reader's (`dbOK`, in `ownDB`). -/
theorem readerViewOK_of (σ : DBState) (v0 v1 : internal.common.Meta) (k : Nat) (r : Reader)
    (h : dbOK σ v0 v1) (hk : σ.readers !! k = some r) : readerViewOK r σ.data σ.ps := by
  obtain ⟨hps80, hps32, -, hsz, hcar, -, -, -, -, hrd, hmvcc, -⟩ := h
  obtain ⟨hwf, -, hin⟩ := hrd k r hk
  refine ⟨hwf, ?_, hcar, by omega, fun id pg hpg => ?_⟩
  · cases hwf with
    | page root pg hlt hlk hid hpt =>
      have hc : coversSlot r.pages r.root := ⟨r.root, pg, hlk, Nat.le_refl _, by omega⟩
      have := ((hmvcc k r hk).2 r.root hc).1
      omega
  · have h1 := (hin id pg hpg).2
    have h2 : id + 1 ≤ σ.nslots := by unfold pageSpan at h1; omega
    have h3 : σ.nslots * σ.ps ≤ min σ.sz σ.bs.length := by
      unfold DBState.nslots; exact Nat.div_mul_le_self _ _
    have h4 : (id + 1) * σ.ps ≤ σ.nslots * σ.ps := Nat.mul_le_mul_right _ h2
    have h5 : min σ.sz σ.bs.length ≤ σ.sz := Nat.min_le_left _ _
    rw [Nat.add_mul] at h4
    omega

/-- The fraction of a reader's resources the root bucket's view takes. -/
def rootQ (r : Reader) : Qp := (qmin r.q halfQ).half

theorem rootQ_lt (r : Reader) : rootQ r < r.q := by
  have h1 := qmin_le_left r.q halfQ
  have h2 := half_lt (qmin r.q halfQ)
  unfold rootQ; simp only [Qp.le_iff, Qp.lt_iff] at *; grind

theorem rootQ_two (r : Reader) : rootQ r + rootQ r < 1 := by
  have h1 := qmin_le_right r.q halfQ
  have e := Qp.half_add_half (qmin r.q halfQ)
  have hv : halfQ.val = 1 / 2 := by unfold halfQ; rw [Qp.val_half]; rfl
  unfold rootQ; rw [e]
  simp only [Qp.le_iff, Qp.lt_iff] at h1 ⊢
  rw [hv] at h1
  have : (1 : Qp).val = 1 := rfl
  rw [this]; grind

theorem uint_nat_W64 (n : Nat) (h : n < 2 ^ 64) : uint.nat (W64 (n : Int)) = n := by
  unfold uint.nat; word

/-- The root bucket of a read transaction, out of `ownReadTx` (and back). -/
theorem ownReadTx_root (dbl : Loc) (γ : DBNames) (txl : Loc) (k : Nat) (r : Reader) (data : Loc)
    (ps : Nat) (managed : Bool) (Hr : readerViewOK r data ps) (Hdbl : dbl ≠ null) :
    ownReadTx (GF := GF) dbl γ txl k r data ps managed ⊢
      ∃ V q, ⌜rootViewOK txl data ps r V⌝ ∗ bktR (GF := GF) (structFieldRef Tx go!"root" txl) V q ∗ txStats (GF := GF) txl ∗
        (bktR (structFieldRef Tx go!"root" txl) V q -∗ txStats txl -∗ ownReadTx dbl γ txl k r data ps managed) := by
  obtain ⟨Hwf, Hr0, Hd, Hps, Hbd⟩ := Hr
  unfold ownReadTx
  iintro ⟨%t, %mv, Htx, %Ht, Hmeta, Hroot, Hrdata, Hrps, Hpages, Hrl, Hkey⟩
  have Ht0 := Ht
  obtain ⟨Htdb, Htw, Htp, Htm, Htrtx, Htb, Htn, Htpg, Htrn, Htxid, Hrr, Hpgid⟩ := Ht0
  have Hupd : uint.nat (W64 (ps : Int)) = ps := uint_nat_W64 ps Hps
  have Hroot0 : mv.root'.root' ≠ W64 0 := by
    intro h; rw [h] at Hrr; exact Hr0 (by rw [← Hrr]; rfl)
  let q := rootQ r
  obtain ⟨a, Ha⟩ := Qp.lt_iff_exists_add.1 (rootQ_lt r)
  have Hq1 : q < 1 := by
    have := rootQ_two r; simp only [Qp.lt_iff, Qp.val_add] at *; have := q.2; grind
  obtain ⟨b, Hb⟩ := Qp.lt_iff_exists_add.1 Hq1
  have Hqb : q < b := by
    have := rootQ_two r
    have e := congrArg Subtype.val Hb
    simp only [Qp.lt_iff, Qp.val_add] at *; have := q.2; grind
  obtain ⟨c, Hc⟩ := Qp.lt_iff_exists_add.1 Hqb
  icases (Tx_split_stats _ _ _).1 $$ Htx with ⟨Hstats, Hrest⟩
  icases (Tx_rest_stats_split' _ _ q b 1 Hb.symm).1 $$ Hrest with ⟨Hrq, Hrb⟩
  icases (Tx_rest_stats_root _ _ _).1 $$ Hrb with ⟨Hrootf, Hrr2⟩
  icases (pt_split' _ _ q c b Hc.symm).1 $$ Hrootf with ⟨Hrootq, Hrootc⟩
  icases (pt_split' _ _ q b 1 Hb.symm).1 $$ Hroot with ⟨Hibq, Hibb⟩
  icases (pt_split' _ _ q a r.q Ha.symm).1 $$ Hrdata with ⟨Hdq, Hda⟩
  icases (pt_split' _ _ q a r.q Ha.symm).1 $$ Hrps with ⟨Hpsq, Hpsa⟩
  icases (pagesView_split' _ _ _ q a r.q Ha.symm).1 $$ Hpages with ⟨Hpgq, Hpga⟩
  iexists rootView txl data ps r t mv, q
  isplitr
  · ipureintro
    exact ⟨rfl, rfl, rfl, rfl, rfl, Hrr, Hroot0, Htw, Htb⟩
  isplitl [Hrootq Hibq Hrq Hdq Hpsq Hpgq]
  · unfold bktR
    isplitl [Hrootq Hibq Hrq Hdq Hpsq]
    · unfold bktCtx
      iexists t.root', mv.root', t, dbl
      rw [Htrtx]
      iframe
      ipureintro
      exact ⟨rfl, Htn, Htrn, Htdb, Htp, fun h => absurd h Hroot0, Hdbl, rfl, rfl, rfl, rfl⟩
    isplitl [Hpgq]
    · unfold bktPages
      simp only [rootView, Hroot0, ↓reduceIte, Hupd]
      iexact Hpgq
    simp only [rootView, Hroot0, ↓reduceIte]
    isplitr
    · itrivial
    ipureintro
    refine ⟨⟨Hd, Hd, fun id pg h => ?_⟩, ?_⟩
    · simp only at h ⊢; rw [Hupd]; exact Hbd id pg h
    · unfold BktView.treeOK; simp only [Hroot0, ↓reduceIte]; rw [Hrr]; exact Hwf
  isplitl [Hstats]
  · unfold txStats; iexists t.stats'; iexact Hstats
  iintro HR Hst
  isimp only [bktR, bktCtx, bktPages] at HR
  icases HR with ⟨⟨%bv', %ib', %t', %dbl', Hbk', Hib', Ht', Hd', Hps', %Hcx'⟩, Hpg', -, -⟩
  obtain ⟨Hr', -, -, Hdb', -, -, -, -, Hbv', Ht'', Hsq'⟩ := Hcx'
  simp only [rootView] at Hr' Hbv' Ht'' Hsq'
  have Hib' : ib' = mv.root' := by
    cases ib'; cases h : mv.root'; rw [h] at Hr' Hsq'; simp only at Hr' Hsq'; rw [Hr', Hsq']
  subst Hbv' Ht'' Hib' Hdb'
  simp only [rootView, Hroot0, ↓reduceIte, Hupd]
  ihave Hrootf := (pt_split' _ _ q c b Hc.symm).2 $$ [Hbk' Hrootc]
  · iframe
  ihave Hrb := (Tx_rest_stats_root _ _ _).2 $$ [Hrootf Hrr2]
  · iframe
  rw [Htrtx]
  ihave Hrest := (Tx_rest_stats_split' _ _ q b 1 Hb.symm).2 $$ [Ht' Hrb]
  · iframe
  ihave Hroot := (pt_split' _ _ q b 1 Hb.symm).2 $$ [Hib' Hibb]
  · iframe
  rw [Htdb]
  ihave Hrdata := (pt_split' _ _ q a r.q Ha.symm).2 $$ [Hd' Hda]
  · iframe
  ihave Hrps := (pt_split' _ _ q a r.q Ha.symm).2 $$ [Hps' Hpsa]
  · iframe
  ihave Hpages := (pagesView_split' _ _ _ q a r.q Ha.symm).2 $$ [Hpg' Hpga]
  · iframe
  unfold txStats
  icases Hst with ⟨%s, Hst⟩
  ihave Htx := (Tx_split_stats txl (DFrac.own 1) { t' with stats' := s }).2 $$ [Hst Hrest]
  · iframe Hst; iapply Tx_rest_stats_with; iexact Hrest
  iexists { t' with stats' := s }, mv
  iframe
  ipureintro
  exact Ht

end root

end bbolt
end EtcdGrove
end Perennial
