/- Lean-first (no Rocq counterpart). The writer's lemmas for `Commit` and `commit`: the client
halves of mapped cells as bytes and as a typed meta; `pickMeta`'s choice is `curMeta`; the meta
cells taken out of the mapping's invariant (`out`) and put back; the meta pages' state failed;
`rwR`'s open branch as `writerSt`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__commit
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.MapInv

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

section pure
variable [GooseExts]

/-- `pickMeta`'s choice between the meta pages' metas is `curMeta`. -/
theorem pick_cur (mp : List w8) (a b : Loc) (h : metaValid (fileMeta mp 0) ∨ metaValid (fileMeta mp 1))
    (_ha : a ≠ null) (_hb : b ≠ null) :
    (pickMetaRes a (fileMeta mp 0) b (fileMeta mp 1) = a ∧ curMeta mp = fileMeta mp 0) ∨
    (pickMetaRes a (fileMeta mp 0) b (fileMeta mp 1) = b ∧ curMeta mp = fileMeta mp 1) := by
  unfold pickMetaRes pickValid curMeta
  dsimp only
  by_cases h1 : uint.Z (fileMeta mp 0).txid' < uint.Z (fileMeta mp 1).txid'
  · simp only [h1, ite_true]
    by_cases h2 : metaValid (fileMeta mp 1)
    · simp [h2]
    · have h0 : metaValid (fileMeta mp 0) := h.resolve_right h2
      simp [h2, h0]
  · simp only [h1, ite_false]
    by_cases h2 : metaValid (fileMeta mp 0)
    · simp [h2]
    · have h0 : metaValid (fileMeta mp 1) := h.resolve_left h2
      simp [h2, h0]

/-- A valid meta of the meta pages has a txid at most the current meta's. -/
theorem curMeta_max (mp : List w8) (j : Nat) (hj : j < 2) (hv : metaValid (fileMeta mp j)) :
    (fileMeta mp j).txid'.toNat ≤ (curMeta mp).txid'.toNat := by
  unfold curMeta
  dsimp only
  have hj' : j = 0 ∨ j = 1 := by omega
  rcases hj' with rfl | rfl
  · by_cases h1 : uint.Z (fileMeta mp 0).txid' < uint.Z (fileMeta mp 1).txid'
    · simp only [h1, ite_true]; split <;> simp only [uint.Z] at h1 <;> omega
    · simp only [h1, ite_false, hv, ite_true]; omega
  · by_cases h1 : uint.Z (fileMeta mp 0).txid' < uint.Z (fileMeta mp 1).txid'
    · simp only [h1, ite_true, hv]; omega
    · simp only [h1, ite_false]; split <;> simp only [uint.Z] at h1 <;> omega

/-- The meta pages `xs` with page `i` replaced by `PB`. -/
def setPage (xs : List w8) (i : Nat) (PB : List w8) : List w8 :=
  xs.take (4096 * i) ++ PB ++ xs.drop (4096 * (i + 1))

theorem setPage_length (xs : List w8) (i : Nat) (PB : List w8) (hl : xs.length = 8192) (hi : i < 2)
    (hPB : PB.length = 4096) : (setPage xs i PB).length = 8192 := by
  unfold setPage; simp only [List.length_append, List.length_take, List.length_drop, hPB, hl]; omega

theorem fileMeta_setPage_same (xs : List w8) (i : Nat) (PB : List w8) (hl : xs.length = 8192)
    (hi : i < 2) (hPB : PB.length = 4096) : fileMeta (setPage xs i PB) i = pageMeta PB := by
  unfold fileMeta setPage
  rw [List.append_assoc, List.drop_left' (by simp; omega)]
  rw [← pageMeta_take _ 4096 (by omega), List.take_append_of_le_length (by omega),
    List.take_of_length_le (by omega)]

theorem fileMeta_setPage_other (xs : List w8) (i j : Nat) (PB : List w8) (hl : xs.length = 8192)
    (hi : i < 2) (hj : j < 2) (hij : i ≠ j) (hPB : PB.length = 4096) :
    fileMeta (setPage xs i PB) j = fileMeta xs j := by
  have : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by omega
  rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · unfold fileMeta setPage
    simp only [Nat.mul_zero, List.take_zero, List.nil_append, Nat.zero_add, Nat.mul_one]
    rw [List.drop_left' (by omega)]
  · unfold fileMeta setPage
    simp only [Nat.mul_zero, List.drop_zero, Nat.mul_one]
    rw [← pageMeta_take _ 4096 (by omega), List.append_assoc,
      List.take_append_of_le_length (by simp; omega), List.take_take, pageMeta_take _ _ (by omega)]

/-- The meta pages after `commit` writes the meta `M` (valid, at the next txid) to page `i`: `M` is
current. -/
theorem curMeta_commit (xs : List w8) (M : Meta) (i : Nat) (PB : List w8) (h : metaPagesOk xs)
    (hM : metaValid M) (ht : M.txid'.toNat = (curMeta xs).txid'.toNat + 1) (hi : i < 2)
    (hPB : PB.length = 4096) (hPM : pageMeta PB = M) :
    curMeta (setPage xs i PB) = M := by
  have hl := h.1
  have hmax := curMeta_max xs
  have hs := fileMeta_setPage_same xs i PB hl hi hPB
  rw [hPM] at hs
  have : i = 0 ∨ i = 1 := by omega
  unfold curMeta
  dsimp only
  rcases this with rfl | rfl
  · have ho := fileMeta_setPage_other xs 0 1 PB hl hi (by omega) (by omega) hPB
    rw [hs, ho]
    by_cases hv : metaValid (fileMeta xs 1)
    · have := hmax 1 (by omega) hv
      have hn : ¬ uint.Z M.txid' < uint.Z (fileMeta xs 1).txid' := by simp only [uint.Z]; omega
      simp [hn, hM]
    · split <;> simp_all
  · have ho := fileMeta_setPage_other xs 1 0 PB hl hi (by omega) (by omega) hPB
    rw [hs, ho]
    by_cases hv : metaValid (fileMeta xs 0)
    · have := hmax 0 (by omega) hv
      have hn : uint.Z (fileMeta xs 0).txid' < uint.Z M.txid' := by simp only [uint.Z]; omega
      simp [hn, hM]
    · split <;> simp_all

theorem curMeta_valid (mp : List w8) (h : metaValid (fileMeta mp 0) ∨ metaValid (fileMeta mp 1)) :
    metaValid (curMeta mp) := by
  unfold curMeta; dsimp only
  split
  · split
    · assumption
    · exact h.resolve_right ‹_›
  · split
    · assumption
    · exact h.resolve_left ‹_›

/-- The meta `commit` writes after `mv`, checksummed. -/
def commitOf (mv : Meta) : Meta :=
  { nextMeta mv with checksum' := metaSum (nextMeta mv) }

theorem commitOf_facts (mv : Meta) (hv : metaValid mv) (ht : mv.txid'.toNat + 1 < 2 ^ 64)
    (hp : mv.pgid'.toNat + 1 < 2 ^ 64) :
    metaValid (commitOf mv) ∧ (commitOf mv).txid'.toNat = mv.txid'.toNat + 1 ∧
      (commitOf mv).pgid'.toNat = mv.pgid'.toNat + 1 ∧ (commitOf mv).root'.root' = mv.pgid' := by
  refine ⟨metaValid_withSum _ hv.1 hv.2.1, ?_, ?_, rfl⟩
  · simp only [commitOf, nextMeta, BitVec.toNat_add]
    show (mv.txid'.toNat + 1) % 2 ^ 64 = _
    omega
  · simp only [commitOf, nextMeta, BitVec.toNat_add]
    show (mv.pgid'.toNat + 1) % 2 ^ 64 = _
    omega

/-- The meta `commit` writes after the current meta of `xs`. -/
abbrev commitMeta (xs : List w8) : Meta := commitOf (curMeta xs)

/-- After `commit` writes `commitMeta` to page `i`, the meta pages are an open database's, at the
next txid, one page on, the root at the old high water mark. -/
theorem metaPagesOk_commit (xs : List w8) (i : Nat) (PB : List w8) (h : metaPagesOk xs)
    (ht : (curMeta xs).txid'.toNat + 1 < 2 ^ 64) (hb : (curPgid xs + 2) * 4096 ≤ 2 ^ 30)
    (hi : i < 2) (hPB : PB.length = 4096) (hPM : pageMeta PB = commitMeta xs) :
    metaPagesOk (setPage xs i PB) ∧ curMeta (setPage xs i PB) = commitMeta xs ∧
      curRoot (setPage xs i PB) = curPgid xs ∧ curPgid (setPage xs i PB) = curPgid xs + 1 ∧
      (curMeta (setPage xs i PB)).txid'.toNat = (curMeta xs).txid'.toNat + 1 := by
  obtain ⟨hl, hv, hr2, hrp, hbd⟩ := h
  have hcv := curMeta_valid xs hv
  obtain ⟨hM, htx, hpg, hrt⟩ := commitOf_facts (curMeta xs) hcv ht
    (by unfold curPgid at hb; omega)
  unfold commitMeta at hPM ⊢
  have hc := curMeta_commit xs (commitOf (curMeta xs)) i PB ⟨hl, hv, hr2, hrp, hbd⟩ hM htx hi hPB hPM
  have hcr : curRoot (setPage xs i PB) = curPgid xs := by
    unfold curRoot curPgid; rw [hc, hrt]
  have hcp : curPgid (setPage xs i PB) = curPgid xs + 1 := by
    unfold curPgid; rw [hc]; exact hpg
  refine ⟨?_, hc, hcr, hcp, by rw [hc]; exact htx⟩
  refine ⟨setPage_length xs i PB hl hi hPB, ?_, ?_, ?_, ?_⟩
  rotate_left
  · rw [hcr]; exact Nat.le_trans hr2 (Nat.le_of_lt hrp)
  · rw [hcr, hcp]; exact Nat.lt_succ_self _
  · rw [hcp]; exact hb
  have hs := fileMeta_setPage_same xs i PB hl hi hPB
  rw [hPM] at hs
  have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl
  · left; rw [hs]; exact hM
  · right; rw [hs]; exact hM

end pure

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

/-- The client halves of 64 mapped cells, as half a typed meta. -/
theorem cellsB_meta (base : Loc) (lo : Nat) (B : List w8) (hB : B.length = 64)
    (hl : 0 < (base +ₗ ((lo : Nat) : Int)).addr) :
    cellsB (GF := GF) base lo B ⊣⊢
      (base +ₗ ((lo : Nat) : Int)) ↦{DFrac.own (1 : Qp).half} (decode B : Meta) := by
  refine (cellsB_bytes base B lo).trans ?_
  have := typedPointsto_bytes (GF := GF) (base +ₗ ((lo : Nat) : Int)) (decode B : Meta)
    (DFrac.own (1 : Qp).half) hl
  rw [ByteEncoding.encode_decode B hB] at this
  exact this.symm

/-- The meta cells, out of the mapping's invariant (the writer holds both mutexes, and its half
of the invariant's token, so the invariant is open), holding the metas. -/
theorem metas_out (γ : DBNames) (p : GoString) (base : Loc) (len : Nat) (γm : GName)
    (mp : List w8) (hwm : Nat) :
    mapInv (GF := GF) γ p base len γm ∗ ghostVar γm (1 : Qp).half () ∗
      ghostVar γ.cur (1 : Qp).half.half (mp, false, hwm) ∗
      ghostVar γ.out (1 : Qp).half.half false ∗ ghostVar γ.out (1 : Qp).half.half false ⊢
      |={⊤}=> ghostVar γm (1 : Qp).half () ∗ ghostVar γ.cur (1 : Qp).half.half (mp, false, hwm) ∗
        ghostVar γ.out (1 : Qp).half.half true ∗ ghostVar γ.out (1 : Qp).half.half true ∗
        cellsB (GF := GF) base 16 ((mp.drop 16).take 64) ∗
        cellsB (GF := GF) base 4112 ((mp.drop 4112).take 64) := by
  iintro ⟨#Hinv, Htok, Hcur, Ho1, Ho2⟩
  unfold mapInv
  icases Hinv with ⟨%_, %γl, #Hinv⟩
  imod inv_acc (by simp) $$ Hinv with ⟨Hi, Hclose⟩
  icases Hi with (>Hc | >Htok2)
  rotate_left
  · icombine Htok Htok2 gives % ⟨Hbad, _⟩
    exfalso
    have h : 0 < ((1 : Qp).half).val := ((1 : Qp).half).2
    simp only [Qp.le_iff, Qp.val_add, Qp.val_one] at Hbad
    grind
  unfold mapLend
  icases Hc with ⟨%mp2, %fl2, %hwm2, %K, Hcur2, %Hl, Ha, %HK, Hpages, Hmo⟩
  icombine Hcur Hcur2 gives % ⟨_, Heq⟩
  cases Heq
  ihave Ho := (ghostVar_split_half γ.out (1 : Qp).half false).2 $$ [Ho1 Ho2]
  · iframe
  icases Hmo with (⟨Hout, -⟩ | ⟨Hout, %mc, %Hmc, Hml⟩)
  · icombine Ho Hout gives % ⟨_, Hbad⟩; cases Hbad
  unfold metaLent metaBytes
  icases Hml with (⟨Hk, Hc0, Hc1⟩ | ⟨Hod, -, -, -⟩)
  rotate_left
  · ihave Ho := (ghostVar_fractional γ.out false).fractional _ _ |>.2 $$ [Ho Hod]
    · iframe
    icombine Ho Hout gives % ⟨Hbad, _⟩
    exfalso
    simp only [Qp.le_iff, Qp.val_add, Qp.val_one, Qp.val_half] at Hbad
    grind
  obtain ⟨Hml, Hmc⟩ := Hmc
  have hmc := Hmc rfl
  imod ghostVar_update_halves true γ.out false false $$ Ho Hout with ⟨Ho, Hout⟩
  icases (ghostVar_split_half γ.out (1 : Qp).half true).1 $$ Ho with ⟨Ho1, Ho2⟩
  imod Hclose $$ [Hcur2 Ha Hpages Hout Hk] with _
  · inext; ileft
    iexists mp, false, hwm, K
    iframe
    isplitr; · ipureintro; exact Hl
    isplitr; · ipureintro; exact HK
    ileft; iframe Hout
    iexists mc; iexact Hk
  imodintro
  iframe
  have hl1 : ((mp.drop 16).take 64).length = 64 := by
    have := congrArg List.length hmc; simp at this ⊢; omega
  have h1 : mc.take 64 = (mp.drop 16).take 64 := by
    rw [hmc]; exact List.take_left' hl1
  have h2 : mc.drop 64 = (mp.drop 4112).take 64 := by
    rw [hmc]; exact List.drop_left' hl1
  rw [h1] at *; rw [h2] at *
  isplitl [Hc0]
  · iapply (cellsB_bytes base _ 16).2; iexact Hc0
  · iapply (cellsB_bytes base _ 4112).2; iexact Hc1

/-- The meta cells back into the mapping's invariant, holding the metas of `mp` unless failed. -/
theorem metas_in (γ : DBNames) (p : GoString) (base : Loc) (len : Nat) (γm : GName)
    (mp : List w8) (fl : Bool) (hwm : Nat) (mc : List w8) (hmc : mc.length = 128)
    (hmp : fl = false → mc = (mp.drop 16).take 64 ++ (mp.drop 4112).take 64) :
    mapInv (GF := GF) γ p base len γm ∗ ghostVar γm (1 : Qp).half () ∗
      ghostVar γ.cur (1 : Qp).half.half (mp, fl, hwm) ∗
      ghostVar γ.out (1 : Qp).half.half true ∗ ghostVar γ.out (1 : Qp).half.half true ∗
      cellsB (GF := GF) base 16 (mc.take 64) ∗ cellsB (GF := GF) base 4112 (mc.drop 64) ⊢
      |={⊤}=> ghostVar γm (1 : Qp).half () ∗ ghostVar γ.cur (1 : Qp).half.half (mp, fl, hwm) ∗
        ghostVar γ.out (1 : Qp).half.half false ∗ ghostVar γ.out (1 : Qp).half.half false := by
  iintro ⟨#Hinv, Htok, Hcur, Ho1, Ho2, Hc0, Hc1⟩
  unfold mapInv
  icases Hinv with ⟨%_, %γl, #Hinv⟩
  imod inv_acc (by simp) $$ Hinv with ⟨Hi, Hclose⟩
  icases Hi with (>Hc | >Htok2)
  rotate_left
  · icombine Htok Htok2 gives % ⟨Hbad, _⟩
    exfalso
    have h : 0 < ((1 : Qp).half).val := ((1 : Qp).half).2
    simp only [Qp.le_iff, Qp.val_add, Qp.val_one] at Hbad
    grind
  unfold mapLend
  icases Hc with ⟨%mp2, %fl2, %hwm2, %K, Hcur2, %Hl, Ha, %HK, Hpages, Hmo⟩
  icombine Hcur Hcur2 gives % ⟨_, Heq⟩
  cases Heq
  ihave Ho := (ghostVar_split_half γ.out (1 : Qp).half true).2 $$ [Ho1 Ho2]
  · iframe
  icases Hmo with (⟨Hout, %mc2, Hk⟩ | ⟨Hout, %mc2, -, -⟩)
  rotate_left
  · icombine Ho Hout gives % ⟨_, Hbad⟩; cases Hbad
  imod ghostVar_update_halves false γ.out true true $$ Ho Hout with ⟨Ho, Hout⟩
  icases (ghostVar_split_half γ.out (1 : Qp).half false).1 $$ Ho with ⟨Ho1, Ho2⟩
  imod ghost_map_update (V := List w8) mc $$ Ha Hk with ⟨Ha, Hk⟩
  imod Hclose $$ [Hcur2 Ha Hpages Hout Hk Hc0 Hc1] with _
  · inext; ileft
    iexists mp, fl, hwm, K.insert 0 mc
    iframe
    isplitr; · ipureintro; exact Hl
    isplitr
    · ipureintro; intro k hk hh
      show (K.insert 0 mc) !! k = none
      rw [GMap.lookup_insert_ne _ _ (by omega)]; exact HK k hk hh
    iright; iframe Hout
    iexists mc
    isplitr; · ipureintro; exact ⟨hmc, hmp⟩
    unfold metaLent metaBytes
    ileft; iframe Hk
    isplitl [Hc0]
    · iapply (cellsB_bytes base _ 16).1; iexact Hc0
    · iapply (cellsB_bytes base _ 4112).1; iexact Hc1
  imodintro
  iframe

/-- The meta pages' state, failed: `cur`'s three parts, the invariant's in the invariant. -/
theorem fail_cur_inv (γ : DBNames) (p : GoString) (base : Loc) (len : Nat) (γm : GName)
    (mp : List w8) (hwm : Nat) :
    mapInv (GF := GF) γ p base len γm ∗ ghostVar γm (1 : Qp).half () ∗
      ghostVar γ.cur (1 : Qp).half.half (mp, false, hwm) ∗
      ghostVar γ.cur (1 : Qp).half (mp, false, hwm) ⊢
      |={⊤}=> ghostVar γm (1 : Qp).half () ∗ ghostVar γ.cur (1 : Qp).half.half (mp, true, hwm) ∗
        ghostVar γ.cur (1 : Qp).half (mp, true, hwm) := by
  iintro ⟨#Hinv, Htok, Hcur, Hcm⟩
  unfold mapInv
  icases Hinv with ⟨%_, %γl, #Hinv⟩
  imod inv_acc (by simp) $$ Hinv with ⟨Hi, Hclose⟩
  icases Hi with (>Hc | >Htok2)
  rotate_left
  · icombine Htok Htok2 gives % ⟨Hbad, _⟩
    exfalso
    have h : 0 < ((1 : Qp).half).val := ((1 : Qp).half).2
    simp only [Qp.le_iff, Qp.val_add, Qp.val_one] at Hbad
    grind
  unfold mapLend
  icases Hc with ⟨%mp2, %fl2, %hwm2, %K, Hcur2, %Hl, Ha, %HK, Hpages, Hmo⟩
  icombine Hcur Hcur2 gives % ⟨_, Heq⟩
  cases Heq
  ihave Hc := (ghostVar_split_half γ.cur (1 : Qp).half (mp, false, hwm)).2 $$ [Hcur Hcur2]
  · iframe
  imod ghostVar_update_halves (mp, true, hwm) γ.cur _ _ $$ Hc Hcm with ⟨Hc, Hcm⟩
  icases (ghostVar_split_half γ.cur (1 : Qp).half (mp, true, hwm)).1 $$ Hc with ⟨Hcur, Hcur2⟩
  imod Hclose $$ [Hcur2 Ha Hpages Hmo] with _
  · inext; ileft
    iexists mp, true, hwm, K
    iframe
    isplitr; · ipureintro; exact Hl
    isplitr; · ipureintro; exact HK
    icases Hmo with (Hout | ⟨Hout, %mc, %Hmc, Hml⟩)
    · ileft; iexact Hout
    · iright; iframe Hout; iexists mc; iframe Hml; ipureintro; exact ⟨Hmc.1, fun h => by cases h⟩
  imodintro
  iframe

/-- The meta pages' state, failed, without a mapping: `cur`'s third part is the writer's. -/
theorem fail_cur (γ : DBNames) (mp : List w8) (hwm : Nat) :
    ghostVar (GF := GF) γ.cur (1 : Qp).half.half (mp, false, hwm) ∗
      ghostVar γ.cur (1 : Qp).half.half (mp, false, hwm) ∗
      ghostVar γ.cur (1 : Qp).half (mp, false, hwm) ⊢
      |={⊤}=> ghostVar γ.cur (1 : Qp).half.half (mp, true, hwm) ∗
        ghostVar γ.cur (1 : Qp).half.half (mp, true, hwm) ∗
        ghostVar γ.cur (1 : Qp).half (mp, true, hwm) := by
  iintro ⟨H1, H2, Hm⟩
  ihave Hc := (ghostVar_split_half γ.cur (1 : Qp).half (mp, false, hwm)).2 $$ [H1 H2]
  · iframe
  imod ghostVar_update_halves (mp, true, hwm) γ.cur _ _ $$ Hc Hm with ⟨Hc, Hm⟩
  icases (ghostVar_split_half γ.cur (1 : Qp).half (mp, true, hwm)).1 $$ Hc with ⟨H1, H2⟩
  imodintro
  iframe

theorem mcellsAny_single (b : Loc) (l lo hi : Nat) (hlo : lo ≤ hi) (hhi : hi ≤ l) :
    mcellsAny (GF := GF) {[b := l]} lo hi ⊣⊢ cellsAny (GF := GF) b lo (hi - lo) := by
  unfold mcellsAny cellsAny
  refine BigSepM.bigSepM_singleton.trans ?_
  rw [Nat.min_eq_left hhi, Nat.min_eq_left (by omega : lo ≤ l)]
  exact .rfl

theorem mcells_single (b : Loc) (l lo hi : Nat) (vf : Nat → val) (hlo : lo ≤ hi) (hhi : hi ≤ l) :
    mcells (GF := GF) {[b := l]} lo hi vf ⊣⊢ cellsR (GF := GF) b lo (hi - lo) vf := by
  unfold mcells
  refine BigSepM.bigSepM_singleton.trans ?_
  rw [Nat.min_eq_left hhi, Nat.min_eq_left (by omega : lo ≤ l)]
  exact .rfl

theorem osBytes_app (p : GoString) (off : Nat) (dq : DFrac) (xs ys : List (w8 × Bool)) :
    osBytes (GF := GF) p off dq (xs ++ ys) ⊣⊢
      osBytes (GF := GF) p off dq xs ∗ osBytes (GF := GF) p (off + xs.length) dq ys := by
  unfold osBytes; exact bytesG_append _ _ _ _ _ _

/-- `rwR`'s open branch, from the writer's part. -/
theorem rwR_of_writerSt (γ : DBNames) (db f : Loc) (fd : w64) (p : GoString) (mp : List w8)
    (fl : Bool) (hwm : Nat) (st : MapSt) (m : OsMeta) (hok : fl = false → m.ok = true) :
    writerSt (GF := GF) γ db f fd p mp fl hwm st m ∗
      (match st with | none => dbFailed (GF := GF) γ | some _ => emp) ⊢
      rwR (GF := GF) γ db f fd p := by
  unfold writerSt rwR
  iintro ⟨⟨Hcur, Hmap, Hout, Hflds, Hw, Hcls, Hst⟩, Hf⟩
  ileft
  iexists mp, fl, hwm, st, m
  iframe
  isplitr
  · ipureintro; exact hok
  rcases st with _ | ⟨base, len, γm⟩
  · dsimp only; iframe
  · dsimp only; iexact Hst

end lemmas

end bboltfs
end EtcdGrove
end Perennial
