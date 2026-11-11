/-
The proof of `Spec/go_etcd_io/bbolt/Cursor__search_r.lean` (U6, `notes/bbolt-proof-plan.md`): by
induction on the page's height (`pageHts` of the view), `search` reads the page (`pageNode_r`),
pushes it, and either searches the leaf (`nsearch_p`) or the branch (`searchPage`, inlined: the
element routing the key by `sort.Search` with its evaluated indices, then `search` below).
-/
module

public import Spec.go_etcd_io.bbolt.Cursor__search_r
public import Spec.go_etcd_io.bbolt.Bucket__pageNode_r
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsLeafPage
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsBranchPage
public import Spec.go_etcd_io.bbolt.internal.common.Page__BranchPageElements
public import Spec.go_etcd_io.bbolt.internal.common.Page__Count
public import Spec.go_etcd_io.bbolt.internal.common.branchPageElement__Key
public import Spec.go_etcd_io.bbolt.internal.common.branchPageElement__Pgid
public import Perennial.Spec.bytes.Compare
public import Proof.go_etcd_io.bbolt.Read.SearchEv
public import Proof.go_etcd_io.bbolt.Read.Search
public import Proof.go_etcd_io.bbolt.Read.TreeFacts
public import Proof.go_etcd_io.bbolt.Read.Route

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section facts
variable [GooseExts]

/-- The search predicate of `searchPage`: branch key `i` is not below `kb`. -/
def spPred (pg : List w8) (kb : List w8) (i : Int) : Bool :=
  decide (¬ go.GoStringLt (branchKey pg i.toNat) kb)

/-- `searchPage`'s exact-match flag: some evaluated key is `kb`. -/
def spExact (pg : List w8) (kb : List w8) (L : List Int) : Bool :=
  decide (∃ j ∈ L, branchKey pg j.toNat = kb)


/-- **`searchPage`'s index routes the key**: the index `sort.Search` returned, less one unless the
search saw an exact match, is the branch element routing `kb`. -/
theorem sp_route (pg kb : List w8) (L : List Int) (idx : Int) (hc0 : 0 < pageCount pg)
    (hsorted : ∀ i j, i < j → j < pageCount pg → go.GoStringLt (branchKey pg i) (branchKey pg j))
    (H0 : 0 ≤ idx) (Hfound : idx < pageCount pg → spPred pg kb idx = true)
    (Hoob : (∀ i : Int, 0 ≤ i ∧ i < (pageCount pg : Int) → spPred pg kb i = false) →
      idx = pageCount pg)
    (Hgt : ∀ k : Int, 0 ≤ k ∧ k < idx → spPred pg kb k = false)
    (Hev : idx < pageCount pg → idx ∈ L) (hL : ∀ j ∈ L, 0 ≤ j ∧ j < (pageCount pg : Int)) :
    let ri := if spExact pg kb L = true then idx else if 0 < idx then idx - 1 else idx
    branchRoute pg kb ri.toNat ∧ 0 ≤ ri ∧ ri < pageCount pg := by
  intro ri
  have hle : idx ≤ pageCount pg := by
    rcases Int.lt_or_le (pageCount pg : Int) idx with hc | hc
    · have := Hoob (fun k hk => Hgt k ⟨hk.1, by omega⟩); omega
    · exact hc
  simp only [spPred, decide_eq_true_eq, decide_eq_false_iff_not, Classical.not_not] at Hfound Hgt
  by_cases hex : spExact pg kb L = true
  · simp only [ri, hex, ↓reduceIte]
    simp only [spExact, decide_eq_true_eq] at hex
    obtain ⟨j, hj, hjk⟩ := hex
    obtain ⟨hj0, hjn⟩ := hL j hj
    have hji : ¬ j < idx := fun h => go.goStringLt_irrefl kb (hjk ▸ Hgt j ⟨hj0, h⟩)
    have hidx : idx < pageCount pg := by omega
    have hfi := Hfound hidx
    have hjeq : j = idx := by
      rcases Int.lt_or_le idx j with h | h
      · exfalso; apply hfi; rw [← hjk]
        exact hsorted idx.toNat j.toNat (by omega) (by omega)
      · omega
    subst hjeq
    refine ⟨⟨by omega, Or.inr (by rw [hjk]; exact go.goStringLt_irrefl _), fun h1 => ?_⟩, H0, hidx⟩
    rw [← hjk]; exact hsorted j.toNat (j.toNat + 1) (by omega) h1
  · simp only [ri, hex, Bool.false_eq_true, ↓reduceIte]
    by_cases hlt : idx < pageCount pg
    · have hin := Hev hlt
      have hne : branchKey pg idx.toNat ≠ kb := by
        intro h; apply hex; simp only [spExact, decide_eq_true_eq]; exact ⟨idx, hin, h⟩
      have hgt : go.GoStringLt kb (branchKey pg idx.toNat) := by
        rcases Classical.em (go.GoStringLt kb (branchKey pg idx.toNat)) with h | h
        · exact h
        · exact absurd (go.goStringLt_eq_of_not_lt (Hfound hlt) h) hne
      by_cases h0 : 0 < idx
      · rw [if_pos h0]
        have hb := Hgt (idx - 1) ⟨by omega, by omega⟩
        refine ⟨⟨by omega, Or.inr (go.goStringLt_asymm hb), fun h1 => ?_⟩, by omega, by omega⟩
        rw [show (idx - 1).toNat + 1 = idx.toNat by omega]; exact hgt
      · rw [if_neg h0]
        have hi0 : idx = 0 := by omega
        refine ⟨⟨by omega, Or.inl (by omega), fun h1 => ?_⟩, H0, hlt⟩
        subst hi0
        exact go.goStringLt_trans hgt (hsorted 0 1 (by omega) (by simpa using h1))
    · have hin : idx = pageCount pg := by omega
      rw [if_pos (by omega)]
      have hb := Hgt (idx - 1) ⟨by omega, by omega⟩
      refine ⟨⟨by omega, Or.inr (go.goStringLt_asymm hb), fun h1 => by omega⟩, by omega, by omega⟩

end facts

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `search`, by recursion on the height bound `n` of the position. -/
theorem search_r_rec
    (hpn : Bucket.pageNode_r.spec (GF := GF) (hG := hG))
    (hns : Cursor.nsearch_p.spec (GF := GF) (hG := hG))
    (hIL : internal.common.Page.IsLeafPage.spec (GF := GF) (hG := hG))
    (hIB : internal.common.Page.IsBranchPage.spec (GF := GF) (hG := hG))
    (hBE : internal.common.Page.BranchPageElements.spec (GF := GF) (hG := hG))
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG))
    (hBK : internal.common.branchPageElement.Key.spec (GF := GF) (hG := hG))
    (hBP : internal.common.branchPageElement.Pgid.spec (GF := GF) (hG := hG))
    (hS : Read.sort.SearchEv.spec (GF := GF) (hG := hG))
    (hC : bytes.Compare.spec (GF := GF) (hG := hG)) (pht : Nat → Nat) :
    ∀ (n : Nat) (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) (b : Loc) (dq : DFrac)
      (bv : List w8) (ibp pp c : Loc) (stk : GoSlice) (els : List elemRef) (pid : w64)
      (key : GoSlice) (kr : KeyR) (kb : List w8),
    pageHts v.pages pht → pagesStrict v.pages →
    (inBucketRoot bv = 0 ∨ pht pid.toNat ≤ n) →
    16 ≤ bv.length → rTree v bv pid.toNat →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ rdTxK (GF := GF) K tx src q T v ∗
        rBktP v tx b dq bv ibp pp ∗ c ↦ Cursor.mk b stk ∗ stk ↦* els ∗
        ownSliceCap elemRef stk (DFrac.own 1) ∗ keyR v key kr kb }}
      (App (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"search")) (Val #key)) (Val #pid))
    {{ RET #(); ∃ (stk' : GoSlice) (path : List elemRef), rdTxK K tx src q T v ∗
        rBktP v tx b dq bv ibp pp ∗ c ↦ Cursor.mk b stk' ∗ stk' ↦* (els ++ path) ∗
        ownSliceCap elemRef stk' (DFrac.own 1) ∗ keyR v key kr kb ∗
        ⌜rRoute v bv pp kb pid.toNat path⌝ }} := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro K tx src q T v b dq bv ibp pp c stk els pid key kr kb hpht hstrict hn hbv htree
  wp_start as ⟨Hk, Hb, Hc, Hs, Hcap, Hkey⟩
  obtain ⟨l, pg, hpa, h16, hpg⟩ := rTree_page v bv pp pid.toNat htree
  wp_auto
  wp_apply hpn K tx src q T v b dq bv ibp pp pid l pg hbv hpa $$ [Hk Hb] as ⟨Hk, Hb⟩
  · iframe
  icases rd_page_bounds K tx src q T v b dq bv ibp pp pid.toNat l pg hpa
    (by intro e; simp [e] at h16) $$ [Hk Hb] with ⟨⟨Hk, Hb⟩, %Hlb⟩
  · iframe
  have hlnn : l ≠ null := by intro e; subst e; simp [null] at Hlb
  rw [show decide (l = null) = false from decide_eq_false hlnn]
  have hfl12 : pageFlags pg = branchPageFlag ∨ pageFlags pg = leafPageFlag := by
    rcases hpg with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  icases rd_hdr_acc K tx src q T v b dq bv ibp pp pid.toNat l pg hpa h16 $$ [Hk Hb]
    with ⟨%dqh, Hh, Hhb⟩
  · iframe
  obtain ⟨hd, hH⟩ : ∃ hd, pageHdr pg = hd := ⟨_, rfl⟩
  have hfz : pageFlags pg = hd.flags'.toNat := by unfold pageFlags; rw [hH]
  rw [hH]
  wp_auto
  wp_apply hIB l hd dqh $$ [Hh] as Hh
  · iexact Hh
  rcases hpg with ⟨hlf, hlwf⟩ | ⟨hbr, hi, hpgv, hwm, hbwf, hch⟩
  · -- a leaf
    have hf2 : hd.flags' = W16 2 := by
      apply BitVec.eq_of_toNat_eq; rw [← hfz, hlf]; rfl
    rw [hf2]
    wp_auto
    wp_apply hIL l hd dqh $$ [Hh] as Hh
    · iexact Hh
    rw [hf2]
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_slice_append $$ [$Hs $Hcap $Hsl] as %s1 ⟨Hs, Hcap, -⟩
    try wp_auto
    wp_method_call; wp_call
    wp_auto
    wp_apply hIL l hd dqh $$ [Hh] as Hh
    · iexact Hh
    rw [hf2]
    wp_auto
    ihave Hkb := Hhb $$ Hh
    icases Hkb with ⟨Hk, Hb⟩
    icases rd_page_key_acc K tx src q T v b dq bv ibp pp pid.toNat l pg hpa key kr kb
      $$ [Hk Hb Hkey] with ⟨%dqp, %dk, Hp, Hkey, Hpb⟩
    · iframe
    wp_apply hns c b s1 els ⟨l, null, W64 0⟩ dqp pg key dk kb rfl hlf hlwf
      $$ [Hc Hs Hp Hkey] as ⟨Hc, Hs, Hp, Hkey⟩
    · iframe
    ihave Hkb := Hpb $$ Hp Hkey
    icases Hkb with ⟨Hk, Hb, Hkey⟩
    iapply HΦ
    iexists s1, [⟨l, null, W64 (pageSeekIdx pg kb : Int)⟩]
    iframe
    ipureintro
    exact ⟨pg, hpa, rfl, hlf, rfl⟩
  · -- a branch: `searchPage` (inlined), then `search` below
    have hf1 : hd.flags' = W16 1 := by
      apply BitVec.eq_of_toNat_eq; rw [← hfz, hbr]; rfl
    rw [hf1]
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_slice_append $$ [$Hs $Hcap $Hsl] as %s1 ⟨Hs, Hcap, -⟩
    try wp_auto
    wp_method_call; wp_call
    wp_auto
    wp_apply hIL l hd dqh $$ [Hh] as Hh
    · iexact Hh
    rw [show decide (hd.flags' = W16 2) = false by rw [hf1]; decide]
    wp_auto
    wp_method_call; wp_call
    wp_auto
    obtain ⟨hc0, -, hcnt, helems, hsorted⟩ := hbwf
    have hgood := (hstrict.1 pid.toNat pg hpgv).2 hbr
    have hcz : uint.Z hd.count' = (pageCount pg : Int) := by unfold pageCount; rw [hH]
    have hcnt16 : pageCount pg < 2 ^ 16 := by unfold pageCount; exact BitVec.isLt _
    wp_apply hBE l hd dqh Hlb.1 (by unfold elemOff at hcnt; rw [hcz]; omega) $$ [Hh] as Hh
    · iexact Hh
    have hcnz : hd.count' ≠ W16 0 := by
      intro h
      have : (pageCount pg : Int) = 0 := by rw [← hcz, h]; rfl
      omega
    rw [if_neg hcnz]
    wp_apply hCnt l hd dqh $$ [Hh] as Hh
    · iexact Hh
    ihave Hkb := Hhb $$ Hh
    icases Hkb with ⟨Hk, Hb⟩
    have hn' : sint.Z (W64 (uint.Z hd.count')) = (pageCount pg : Int) := by rw [hcz]; word
    wp_apply hS (W64 (uint.Z hd.count')) _ (spPred pg kb)
      (fun L => iprop(rdTxK K tx src q T v ∗ rBktP v tx b dq bv ibp pp ∗ key_ptr ↦ key ∗
        inodes_ptr ↦ slice.mk (l +ₗ 16) (W64 (uint.Z hd.count')) (W64 (uint.Z hd.count')) ∗
        exact_ptr ↦ spExact pg kb L ∗ keyR v key kr kb ∗
        ⌜∀ j ∈ L, 0 ≤ j ∧ j < (pageCount pg : Int)⌝))
      $$ [Hk Hb key inodes exact Hkey]
    · iframe
      isplitl []
      · ipureintro; word
      isplitl []
      · unfold Read.predImplementsL
        iintro %L %i
        wp_start as ⟨⟨Hk, Hb, Hkp, Hin, Hex, Hkey, %HL⟩, %Hbi⟩
        rw [hn'] at Hbi
        wp_auto
        rw [if_pos ⟨Hbi.1, by rw [hn']; exact Hbi.2⟩]
        obtain ⟨k, hk⟩ : ∃ k : Nat, sint.Z i = (k : Int) := ⟨(sint.Z i).toNat, by omega⟩
        have hkc : k < pageCount pg := by omega
        have hloc : sliceIndexRef branchPageElement (sint.Z i)
            (slice.mk (l +ₗ 16) (W64 (uint.Z hd.count')) (W64 (uint.Z hd.count'))) =
            l +ₗ ((elemOff k : Nat) : Int) := by
          rw [sliceIndexRef_plain branchPageElement.ty branchPageElement.layout _ i
            (by simp [Loc.add]; omega) Hbi.1]
          simp only [sint.nat, hk, Int.toNat_natCast, loc_add_assoc, elemOff]
          congr 1; push_cast; omega
        rw [hloc]
        obtain ⟨he1, he2, -⟩ := helems k hkc
        icases rd_elem_acc (V := branchPageElement) K tx src q T v b dq bv ibp pp pid.toNat l pg
          hpa k (by unfold elemOff at hcnt ⊢; omega) $$ [Hk Hb] with ⟨%dqe, Hel, Helb⟩
        · iframe
        rw [show (decode (bytesAt pg (elemOff k) 16) : branchPageElement) = branchElem pg k from rfl]
        obtain ⟨be, hbe⟩ : ∃ be, branchElem pg k = be := ⟨_, rfl⟩
        have hpos : uint.Z be.pos' = (branchPos pg k : Int) := by unfold branchPos; rw [hbe]
        have hks : uint.Z be.ksize' = (branchKsize pg k : Int) := by unfold branchKsize; rw [hbe]
        rw [hbe]
        wp_apply hBK (l +ₗ ((elemOff k : Nat) : Int)) be dqe (by simp [Loc.add]; omega)
          (by simp only [Loc.add]; rw [hpos, hks]; omega) $$ [Hel] as Hel
        · iexact Hel
        ihave Hkb := Helb $$ Hel
        icases Hkb with ⟨Hk, Hb⟩
        icases rd_slice_key_acc K tx src q T v b dq bv ibp pp pid.toNat l pg hpa
          (elemOff k + branchPos pg k) (branchKsize pg k) (by omega)
          (by unfold maxAllocSize at he2; omega) (hgood k hkc) key kr kb $$ [Hk Hb Hkey]
          with ⟨%dqk, %dk, Hks, Hkey, Hksb⟩
        · iframe
        have hkloc : (l +ₗ ((elemOff k : Nat) : Int)) +ₗ uint.Z be.pos' =
            l +ₗ ((elemOff k + branchPos pg k : Nat) : Int) := by
          rw [loc_add_assoc, hpos]; push_cast; rfl
        rw [hkloc, hks]
        wp_apply hC $$ [Hks Hkey] as ⟨Hks, Hkey⟩
        · iframe
        ihave Hkb := Hksb $$ Hks Hkey
        icases Hkb with ⟨Hk, Hb, Hkey⟩
        rw [show bytesAt pg (elemOff k + branchPos pg k) (branchKsize pg k) = branchKey pg k from rfl]
        have hcr0 : bytes.compareResult (branchKey pg k) kb = W64 0 ↔ branchKey pg k = kb := by
          unfold bytes.compareResult
          constructor
          · intro h; split at h
            · cases h
            · split at h
              · assumption
              · cases h
          · intro h; subst h; simp [go.goStringLt_irrefl]
        have hcrm : bytes.compareResult (branchKey pg k) kb = W64 (-1) ↔
            go.GoStringLt (branchKey pg k) kb := by
          unfold bytes.compareResult
          constructor
          · intro h; split at h
            · assumption
            · split at h <;> cases h
          · intro h; simp [h]
        wp_if_destruct
        · try wp_auto
          iapply HΦ
          iframe
          isplitl
          · have : spExact pg kb (sint.Z i :: L) = true := by
              unfold spExact; simp only [decide_eq_true_eq]
              exact ⟨sint.Z i, List.mem_cons_self .., by rw [hk]; simpa using hcr0.1 Hif⟩
            rw [this]; iframe
            ipureintro; intro j hj
            rcases List.mem_cons.mp hj with rfl | hj
            · omega
            · exact HL j hj
          ipureintro
          unfold spPred
          rw [hk]; simp only [Int.toNat_natCast]
          by_cases hlt : go.GoStringLt (branchKey pg k) kb
          · exact absurd (hcr0.1 Hif ▸ hlt) (go.goStringLt_irrefl _)
          · simp [hlt, show ¬ bytes.compareResult (branchKey pg k) kb = W64 (-1) from fun h => hlt (hcrm.1 h)]
        · try wp_auto
          iapply HΦ
          iframe
          isplitl
          · have : spExact pg kb (sint.Z i :: L) = spExact pg kb L := by
              unfold spExact
              congr 1
              apply propext
              constructor
              · rintro ⟨j, hj, hjk⟩
                rcases List.mem_cons.mp hj with rfl | hj
                · exfalso; apply Hif; apply hcr0.2; rw [hk] at hjk; simpa using hjk
                · exact ⟨j, hj, hjk⟩
              · rintro ⟨j, hj, hjk⟩; exact ⟨j, List.mem_cons_of_mem _ hj, hjk⟩
            rw [this]; iframe
            ipureintro; intro j hj
            rcases List.mem_cons.mp hj with rfl | hj
            · omega
            · exact HL j hj
          ipureintro
          unfold spPred
          rw [hk]; simp only [Int.toNat_natCast]
          by_cases hlt : go.GoStringLt (branchKey pg k) kb
          · simp [hlt, hcrm.2 hlt]
          · simp [hlt, show ¬ bytes.compareResult (branchKey pg k) kb = W64 (-1) from fun h => hlt (hcrm.1 h)]
      ipureintro; rw [hn']
      refine ⟨fun j hj => by simp at hj, ?_⟩
      intro x y hxy hx
      obtain ⟨h0, hxy, hyn⟩ := hxy
      simp only [spPred, decide_eq_true_eq] at hx ⊢
      intro hy
      apply hx
      exact go.goStringLt_trans (hsorted x.toNat y.toNat (by omega) (by omega)) hy
    iintro %idx ⟨%L, ⟨Hk, Hb, Hkp, Hin, Hex, Hkey, %HL⟩, %H0, %Hfound, %Hoob, %Hgt, %Hev⟩
    rw [hn'] at Hfound Hoob Hev
    have hR := sp_route pg kb L (sint.Z idx) hc0 hsorted H0 Hfound Hoob Hgt Hev HL
    have hidx63 : sint.Z idx ≤ 2 ^ 16 := by
      rcases Int.lt_or_le (pageCount pg : Int) (sint.Z idx) with hc | hc
      · have := Hoob (fun k hk => Hgt k ⟨hk.1, by omega⟩); omega
      · omega
    cases hex : spExact pg kb L
    all_goals simp only [hex, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte] at hR ⊢
    · wp_auto
      wp_if_destruct
      · rw [if_pos (by word)] at hR
        have hv : sint.Z (idx - W64 1) = sint.Z idx - 1 := by word
        rw [← hv] at hR
        try wp_auto
        generalize idx - W64 1 = ri at hR ⊢
        ihave %Hsl := ownSlice_len _ _ _ $$ Hs
        have hsidx : sint.Z (s1.len - W64 1) = (els.length : Int) := by
          simp only [List.length_append, List.length_singleton] at Hsl; word
        rw [if_pos (by rw [hsidx]; word)]
        icases ownSlice_elem_acc (sint.Z (s1.len - W64 1)) (⟨l, null, W64 0⟩ : elemRef) _ _
          (els ++ [⟨l, null, W64 0⟩]) (by omega) (by rw [hsidx]; simp) $$ Hs with ⟨He, Hsback⟩
        rw [hsidx]
        wp_auto
        ihave Hs := Hsback $$ He
        simp only [show ∀ (a x : elemRef), (els ++ [a]).set (↑els.length : Int).toNat x = els ++ [x]
          from fun a x => by simp]
        rw [if_pos ⟨hR.2.1, by rw [hn']; exact hR.2.2⟩]
        obtain ⟨k, hk⟩ : ∃ k : Nat, sint.Z ri = (k : Int) := ⟨(sint.Z ri).toNat, by omega⟩
        have hkc : k < pageCount pg := by omega
        have hloc : sliceIndexRef branchPageElement (sint.Z ri)
            (slice.mk (l +ₗ 16) (W64 (uint.Z hd.count')) (W64 (uint.Z hd.count'))) =
            l +ₗ ((elemOff k : Nat) : Int) := by
          rw [sliceIndexRef_plain branchPageElement.ty branchPageElement.layout _ ri
            (by simp [Loc.add]; omega) hR.2.1]
          simp only [sint.nat, hk, Int.toNat_natCast, loc_add_assoc, elemOff]
          congr 1; push_cast; omega
        rw [hloc]
        icases rd_elem_acc (V := branchPageElement) K tx src q T v b dq bv ibp pp pid.toNat l pg
          hpa k (by unfold elemOff at hcnt ⊢; omega) $$ [Hk Hb] with ⟨%dqe, Hel, Helb⟩
        · iframe
        rw [show (decode (bytesAt pg (elemOff k) 16) : branchPageElement) = branchElem pg k from rfl]
        obtain ⟨be2, hbe2⟩ : ∃ be, branchElem pg k = be := ⟨_, rfl⟩
        rw [hbe2]
        wp_apply hBP (l +ₗ ((elemOff k : Nat) : Int)) be2 dqe $$ [Hel] as Hel
        · iexact Hel
        ihave Hkb := Helb $$ Hel
        icases Hkb with ⟨Hk, Hb⟩
        have hchild : be2.pgid'.toNat = branchPgid pg k := by unfold branchPgid; rw [hbe2]
        have hht := (hpht pid.toNat pg hpgv).2 hbr k hkc
        have hpn' : pht pid.toNat ≤ n := by rcases hn with h | h; exact absurd h hi; exact h
        have hnpos : 0 < n := by omega
        wp_apply (ih (n - 1) (by omega) K tx src q T v
          b dq bv ibp pp c s1 (els ++ [({ page' := l, node' := null, index' := ri } : elemRef)])
          be2.pgid' key kr kb hpht hstrict
          (Or.inr (by rw [hchild]; omega)) hbv (by rw [hchild]; exact hch k hkc))
          $$ [Hk Hb Hc Hs Hcap Hkey] as ⟨%stk'', %path', Hk, Hb, Hc, Hs, Hcap, Hkey, %Hrt⟩
        · iframe
        iapply HΦ
        iexists stk'', (({ page' := l, node' := null, index' := ri } : elemRef) :: path')
        rw [List.append_assoc]
        iframe
        ipureintro
        cases path' with
        | nil => exact absurd Hrt (by simp [rRoute])
        | cons e2 es =>
          have hri : ri.toNat = k := by have := hR.2.1; word
          have hsk : (sint.Z ri).toNat = k := by omega
          refine ⟨pg, hpa, rfl, hbr, ?_, ?_⟩
          · rw [hri]; rw [hsk] at hR; exact hR.1
          · rw [hri, ← hchild]; exact Hrt
      · rw [if_neg (by word)] at hR
        try wp_auto
        generalize idx = ri at hR ⊢
        ihave %Hsl := ownSlice_len _ _ _ $$ Hs
        have hsidx : sint.Z (s1.len - W64 1) = (els.length : Int) := by
          simp only [List.length_append, List.length_singleton] at Hsl; word
        rw [if_pos (by rw [hsidx]; word)]
        icases ownSlice_elem_acc (sint.Z (s1.len - W64 1)) (⟨l, null, W64 0⟩ : elemRef) _ _
          (els ++ [⟨l, null, W64 0⟩]) (by omega) (by rw [hsidx]; simp) $$ Hs with ⟨He, Hsback⟩
        rw [hsidx]
        wp_auto
        ihave Hs := Hsback $$ He
        simp only [show ∀ (a x : elemRef), (els ++ [a]).set (↑els.length : Int).toNat x = els ++ [x]
            from fun a x => by simp]
        rw [if_pos ⟨hR.2.1, by rw [hn']; exact hR.2.2⟩]
        obtain ⟨k, hk⟩ : ∃ k : Nat, sint.Z ri = (k : Int) := ⟨(sint.Z ri).toNat, by omega⟩
        have hkc : k < pageCount pg := by omega
        have hloc : sliceIndexRef branchPageElement (sint.Z ri)
            (slice.mk (l +ₗ 16) (W64 (uint.Z hd.count')) (W64 (uint.Z hd.count'))) =
            l +ₗ ((elemOff k : Nat) : Int) := by
          rw [sliceIndexRef_plain branchPageElement.ty branchPageElement.layout _ ri
            (by simp [Loc.add]; omega) hR.2.1]
          simp only [sint.nat, hk, Int.toNat_natCast, loc_add_assoc, elemOff]
          congr 1; push_cast; omega
        rw [hloc]
        icases rd_elem_acc (V := branchPageElement) K tx src q T v b dq bv ibp pp pid.toNat l pg
          hpa k (by unfold elemOff at hcnt ⊢; omega) $$ [Hk Hb] with ⟨%dqe, Hel, Helb⟩
        · iframe
        rw [show (decode (bytesAt pg (elemOff k) 16) : branchPageElement) = branchElem pg k from rfl]
        obtain ⟨be2, hbe2⟩ : ∃ be, branchElem pg k = be := ⟨_, rfl⟩
        rw [hbe2]
        wp_apply hBP (l +ₗ ((elemOff k : Nat) : Int)) be2 dqe $$ [Hel] as Hel
        · iexact Hel
        ihave Hkb := Helb $$ Hel
        icases Hkb with ⟨Hk, Hb⟩
        have hchild : be2.pgid'.toNat = branchPgid pg k := by unfold branchPgid; rw [hbe2]
        have hht := (hpht pid.toNat pg hpgv).2 hbr k hkc
        have hpn' : pht pid.toNat ≤ n := by rcases hn with h | h; exact absurd h hi; exact h
        have hnpos : 0 < n := by omega
        wp_apply (ih (n - 1) (by omega) K tx src q T v
          b dq bv ibp pp c s1 (els ++ [({ page' := l, node' := null, index' := ri } : elemRef)])
            be2.pgid' key kr kb hpht hstrict
          (Or.inr (by rw [hchild]; omega)) hbv (by rw [hchild]; exact hch k hkc))
          $$ [Hk Hb Hc Hs Hcap Hkey] as ⟨%stk'', %path', Hk, Hb, Hc, Hs, Hcap, Hkey, %Hrt⟩
        · iframe
        iapply HΦ
        iexists stk'', (({ page' := l, node' := null, index' := ri } : elemRef) :: path')
        rw [List.append_assoc]
        iframe
        ipureintro
        cases path' with
        | nil => exact absurd Hrt (by simp [rRoute])
        | cons e2 es =>
          have hri : ri.toNat = k := by have := hR.2.1; word
          have hsk : (sint.Z ri).toNat = k := by omega
          refine ⟨pg, hpa, rfl, hbr, ?_, ?_⟩
          · rw [hri]; rw [hsk] at hR; exact hR.1
          · rw [hri, ← hchild]; exact Hrt
    · wp_auto
      generalize idx = ri at hR ⊢
      ihave %Hsl := ownSlice_len _ _ _ $$ Hs
      have hsidx : sint.Z (s1.len - W64 1) = (els.length : Int) := by
        simp only [List.length_append, List.length_singleton] at Hsl; word
      rw [if_pos (by rw [hsidx]; word)]
      icases ownSlice_elem_acc (sint.Z (s1.len - W64 1)) (⟨l, null, W64 0⟩ : elemRef) _ _
        (els ++ [⟨l, null, W64 0⟩]) (by omega) (by rw [hsidx]; simp) $$ Hs with ⟨He, Hsback⟩
      rw [hsidx]
      wp_auto
      ihave Hs := Hsback $$ He
      simp only [show ∀ (a x : elemRef), (els ++ [a]).set (↑els.length : Int).toNat x = els ++ [x]
          from fun a x => by simp]
      rw [if_pos ⟨hR.2.1, by rw [hn']; exact hR.2.2⟩]
      obtain ⟨k, hk⟩ : ∃ k : Nat, sint.Z ri = (k : Int) := ⟨(sint.Z ri).toNat, by omega⟩
      have hkc : k < pageCount pg := by omega
      have hloc : sliceIndexRef branchPageElement (sint.Z ri)
          (slice.mk (l +ₗ 16) (W64 (uint.Z hd.count')) (W64 (uint.Z hd.count'))) =
          l +ₗ ((elemOff k : Nat) : Int) := by
        rw [sliceIndexRef_plain branchPageElement.ty branchPageElement.layout _ ri
          (by simp [Loc.add]; omega) hR.2.1]
        simp only [sint.nat, hk, Int.toNat_natCast, loc_add_assoc, elemOff]
        congr 1; push_cast; omega
      rw [hloc]
      icases rd_elem_acc (V := branchPageElement) K tx src q T v b dq bv ibp pp pid.toNat l pg
        hpa k (by unfold elemOff at hcnt ⊢; omega) $$ [Hk Hb] with ⟨%dqe, Hel, Helb⟩
      · iframe
      rw [show (decode (bytesAt pg (elemOff k) 16) : branchPageElement) = branchElem pg k from rfl]
      obtain ⟨be2, hbe2⟩ : ∃ be, branchElem pg k = be := ⟨_, rfl⟩
      rw [hbe2]
      wp_apply hBP (l +ₗ ((elemOff k : Nat) : Int)) be2 dqe $$ [Hel] as Hel
      · iexact Hel
      ihave Hkb := Helb $$ Hel
      icases Hkb with ⟨Hk, Hb⟩
      have hchild : be2.pgid'.toNat = branchPgid pg k := by unfold branchPgid; rw [hbe2]
      have hht := (hpht pid.toNat pg hpgv).2 hbr k hkc
      have hpn' : pht pid.toNat ≤ n := by rcases hn with h | h; exact absurd h hi; exact h
      have hnpos : 0 < n := by omega
      wp_apply (ih (n - 1) (by omega) K tx src q T v
        b dq bv ibp pp c s1 (els ++ [({ page' := l, node' := null, index' := ri } : elemRef)])
          be2.pgid' key kr kb hpht hstrict
        (Or.inr (by rw [hchild]; omega)) hbv (by rw [hchild]; exact hch k hkc))
        $$ [Hk Hb Hc Hs Hcap Hkey] as ⟨%stk'', %path', Hk, Hb, Hc, Hs, Hcap, Hkey, %Hrt⟩
      · iframe
      iapply HΦ
      iexists stk'', (({ page' := l, node' := null, index' := ri } : elemRef) :: path')
      rw [List.append_assoc]
      iframe
      ipureintro
      cases path' with
      | nil => exact absurd Hrt (by simp [rRoute])
      | cons e2 es =>
        have hri : ri.toNat = k := by have := hR.2.1; word
        have hsk : (sint.Z ri).toNat = k := by omega
        refine ⟨pg, hpa, rfl, hbr, ?_, ?_⟩
        · rw [hri]; rw [hsk] at hR; exact hR.1
        · rw [hri, ← hchild]; exact Hrt

theorem Cursor.search_r.wp_proof
    (hpn : Bucket.pageNode_r.spec (GF := GF) (hG := hG))
    (hns : Cursor.nsearch_p.spec (GF := GF) (hG := hG))
    (hIL : internal.common.Page.IsLeafPage.spec (GF := GF) (hG := hG))
    (hIB : internal.common.Page.IsBranchPage.spec (GF := GF) (hG := hG))
    (hBE : internal.common.Page.BranchPageElements.spec (GF := GF) (hG := hG))
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG))
    (hBK : internal.common.branchPageElement.Key.spec (GF := GF) (hG := hG))
    (hBP : internal.common.branchPageElement.Pgid.spec (GF := GF) (hG := hG))
    (hS : Read.sort.SearchEv.spec (GF := GF) (hG := hG))
    (hC : bytes.Compare.spec (GF := GF) (hG := hG)) :
    Cursor.search_r.spec (GF := GF) (hG := hG) := by
  intro K tx src q T v b dq bv ibp pp c stk els pid key kr kb hbv htree
  iintro %Φ ⟨#Hpkg, Hk, Hrest⟩ HΦ
  icases (persistent_entails_left (rdTxK_view K tx src q T v)) $$ Hk with ⟨Hk, %Hvw⟩
  obtain ⟨-, C, hok, hvC⟩ := Hvw
  have hpv : v.pages = C.pages := by rw [← hvC]; rfl
  obtain ⟨-, hstr, -, pht, hpht⟩ := hok.1
  rw [← hpv] at hstr hpht
  iapply (search_r_rec hpn hns hIL hIB hBE hCnt hBK hBP hS hC pht (pht pid.toNat) K tx src q T v
    b dq bv ibp pp c stk els pid key kr kb hpht hstr (Or.inr (Nat.le_refl _)) hbv htree)
    $$ [Hk Hrest] HΦ
  iframe; iframe #

end proof

end bbolt
end EtcdGrove
end Perennial
