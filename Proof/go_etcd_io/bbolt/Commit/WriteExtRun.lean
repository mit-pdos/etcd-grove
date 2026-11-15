/-
`tx.write()` with the dirty pages anywhere in the mapping (`Tx.write_ext`, maintainer 12's item 3 of
`notes/bbolt-proof-plan.md`; U10w): `Tx.write.wp_proof`'s loops with the target slots held relative
to the file's current size (`Commit/WriteExtDefs`): the waiting pages' slots and the tail's slots
outside the old file form a pool (`slotAnyZ` at the current size); a page's write takes its own
slots from the pool as one run, and, when it starts past the file's end, the cells of the gap from
the other waiting slots (`gap_acc`), which get the gap's zero bytes back. The size stays the old one
or ends on a page boundary between pages (the page loop's last fact; within a page, the old size or
the end of what the page's chunks wrote), which gives the success post's last two facts.
-/
module

public import Proof.go_etcd_io.bbolt.Commit.WriteExtDefs
public import Proof.go_etcd_io.bbolt.Tx__write
public import Spec.go_etcd_io.bbolt.Tx__write_ext

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

set_option linter.unusedSectionVars false

section pure
variable [GooseExts]

theorem ext_split (L : List (w64 × Loc × List w8)) (j : Nat) (c : w64 × Loc × List w8)
    (hc : L[j]? = some c) :
    L.flatMap extE = (L.take j).flatMap extE ++ (extE c ++ (L.drop (j + 1)).flatMap extE) := by
  conv => lhs; rw [← List.take_append_drop j L, wr_drop_cons _ _ _ hc]
  simp only [List.flatMap_append, List.flatMap_cons]

/-- **The gap's slots are waiting**: a slot outside the file (of size `sz`) below the page `c`
(the `j`-th) is a later page's or the tail's. -/
theorem ext_cover (L : List (w64 × Loc × List w8)) (j : Nat) (c : w64 × Loc × List w8)
    (hc : L[j]? = some c) (bufs : GMap w64 (List w8)) (T : List Nat) (sz0 sz lim : Nat)
    (hLext : (L.flatMap extE).Perm (bufSlots bufs))
    (htail : ∀ s, s < lim → sz0 < 4096 * (s + 1) → s ∈ bufSlots bufs ∨ s ∈ T)
    (hdone : ∀ e ∈ L.take j, 4096 * (e.1.toNat + (1 + pageOverflow e.2.2)) ≤ sz)
    (hle : sz0 ≤ sz) (s : Nat) (hs1 : sz < 4096 * (s + 1)) (hs2 : s < c.1.toNat)
    (hlim : c.1.toNat ≤ lim) :
    s ∈ (L.drop (j + 1)).flatMap extE ++ tOut T sz0 := by
  rcases htail s (by omega) (by omega) with hb | ht
  · obtain ⟨e, he, hse⟩ := List.mem_flatMap.1 (hLext.mem_iff.2 hb)
    have hsplit : L = L.take j ++ c :: L.drop (j + 1) := by
      rw [← wr_drop_cons _ _ _ hc, List.take_append_drop]
    rw [hsplit] at he
    unfold extE at hse
    have hr := List.mem_range'_1.1 hse
    rcases List.mem_append.1 he with h | h
    · have := hdone e h; omega
    · rcases List.mem_cons.1 h with h | h
      · subst h; omega
      · exact List.mem_append_left _ (List.mem_flatMap.2 ⟨e, h, by unfold extE; exact hse⟩)
  · exact List.mem_append_right _ (List.mem_filter.2 ⟨ht, by simp only [decide_eq_true_eq,
      Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Nat.not_le]; omega⟩)

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The remaining length after a chunk, as a word (stated apart: `word` inside the write loop's
context, with its byte lists, ran out of memory). -/
theorem wr_rem_sub (a w cs : Nat) (h : w + cs ≤ a) :
    W64 ((a - w : Nat) : Int) - W64 ((cs : Nat) : Int) = W64 ((a - (w + cs) : Nat) : Int) := by
  rw [show ((a - (w + cs) : Nat) : Int) = ((a - w : Nat) : Int) - ((cs : Nat) : Int) by omega]
  word

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
/-- **`tx.write()` with the pages anywhere in the mapping** (`Tx.write_ext.spec`; see the file
header). -/
theorem Tx.write_ext_gen (hLogger : DB.Logger.spec (GF := GF) (hG := hG))
    (hSort : sort.«Sort».anyLessSpec (GF := GF) (hG := hG))
    (hOv : internal.common.Page.Overflow.spec (GF := GF) (hG := hG))
    (hId : internal.common.Page.Id.spec (GF := GF) (hG := hG))
    (hUBS : internal.common.UnsafeByteSlice.spec (GF := GF) (hG := hG))
    (hWriteAt : os.File.WriteAt.specExt (GF := GF) (hG := hG))
    (hSync : fdatasync.spec (GF := GF) (hG := hG))
    (hInc : TxStats.IncWrite.spec (GF := GF) (hG := hG)) :
    Tx.write_ext.spec (GF := GF) (hG := hG) := by
  intro K tx r sm q dq pml pm bufs T wb f fd om b l dqf dqw hdom hok hsz hl hmaps hnd hT htail hwb
    hstr
  wp_start as ⟨#Hcore, #Hreg, Hst, Hdb, Hpg, Hpm, Hbufs, Hf, Hwa, Hfo, Hfd, Hm, Hslots⟩
  ihave #Hcore' : isBoltCoreP K.B K.N K.db K.p K.sp K.t0 $$ []
  · unfold BC.core; iexact Hcore
  unfold isBoltCoreP
  icases Hcore' with ⟨#Hdbl, #Ht0, %Ht0, #Hpkg, #Hos, #Hfix, #Hml, #Hmm, #Hsl, #Hpi, #Hti⟩
  iunfold dbFixed at Hfix
  icases Hfix with ⟨#Hps, #Hsp, ⟨%lg, #Hlg, #Hlgok⟩, -, -, -, ⟨%ns, #Hns⟩, -, -, -, -, -, -, -, -, -,
    -, ⟨%pf, #HisPool, -⟩, -⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hpkc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  ihave #Hpks : isPkgInit (PROP := IProp GF) pkg_id.sort $$ []
  · iPkgInit
  wp_auto
  iunfold dbLogger at Hlgok
  wp_apply hLogger K.db lg Ht0.2.1 $$ []
  · iframe #
  wp_apply (wp_map_len_lt (K := w64) (V := Loc) pml pm (DFrac.own 1)) $$ [Hpm] as ⟨Hpm, %Hpms⟩
  · iexact Hpm
  wp_apply (wp_slice_make3 (V := Loc) (W64 0) (W64 (pm.size : Int)) ⟨by word, by word⟩)
    as %sl0 ⟨Hsl0, Hcap0, -⟩
  try wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (K := w64) (V := Loc)
    (fun (keys : List w64) (i : Int) => iprop(∃ (sl : GoSlice) (L : List (w64 × Loc × List w8))
      (pv : Loc),
      "Hpgs" ∷ pages_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* L.map (·.2.1) ∗
      "Hcap" ∷ ownSliceCap Loc sl (DFrac.own 1) ∗ "Hpv" ∷ p_ptr ↦ pv ∗
      "%HL" ∷ ⌜0 ≤ i ∧ L.map Prod.fst = keys.take i.toNat ∧ ∀ e ∈ L, bufs !! e.1 = some e.2.2⌝ ∗
      "HLh" ∷ ([∗list] e ∈ L, e.2.1 ↦ pageHdr e.2.2) ∗
      "HLr" ∷ ([∗list] e ∈ L, pgBufR e) ∗
      "Hrest" ∷ ([∗list] k ∈ keys.drop i.toNat, ∃ pl, ⌜pm !! k = some pl⌝ ∗
        ∃ bs, ⌜bufs !! k = some bs⌝ ∗ bytesPointsto pl (DFrac.own 1) bs)))
    _ _ _ pml pm _ $$ Hpm
  iintro %keys ⟨%Hkset, %Hklen, %Hknd⟩
  have hkb : ∀ k, k ∈ keys ↔ (bufs !! k).isSome := fun k => (Hkset k).trans (by rw [hdom k])
  ihave Hb := wr_bigSepM_keys (fun k pl => iprop(∃ bs, ⌜bufs !! k = some bs⌝ ∗
    bytesPointsto (GF := GF) pl (DFrac.own 1) bs)) keys pm Hknd Hkset $$ Hbufs
  isplitl [pages Hsl0 Hcap0 p Hb]
  · iexists sl0, [], _
    simp only [Int.toNat_zero, List.drop_zero, List.take_zero, List.map_nil, List.replicate,
      show sint.nat (W64 0) = 0 from rfl]
    iframe
    isplitr
    · ipureintro; simp
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    iapply BigSepL.bigSepL_nil.2; iempintro
  isplitr
  · imodintro
    iintro %i %key %v ⟨%Hkey, %Hv⟩ HP
    iNamed HP
    obtain ⟨Hi0, HLk, HLm⟩ := HL
    try wp_auto
    rw [wr_drop_cons _ _ _ Hkey]
    icases BigSepL.bigSepL_cons.1 $$ Hrest with ⟨Hk, Hrest⟩
    icases wr_entryB pm bufs _ hok key v Hv $$ Hk with ⟨%bs, %Hbs, Hh, Hr⟩
    wp_apply wp_slice_literal (V := Loc) [v]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    try wp_auto
    wp_apply wp_slice_append $$ [$Hsl $Hcap $Hsl2] as %sl' ⟨Hsl, Hcap, -⟩
    try wp_auto
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists sl', L ++ [(key, v, bs)], v
    have Hi : (i + 1).toNat = i.toNat + 1 := by omega
    rw [Hi]
    simp only [List.map_append, List.map_cons, List.map_nil]
    iframe Hpgs Hcap Hsl Hrest Hpv
    isplitr
    · ipureintro
      refine ⟨by omega, ?_, fun e he => ?_⟩
      · rw [HLk, List.take_add_one, Hkey]; rfl
      · rcases List.mem_append.1 he with he | he
        · exact HLm e he
        · rw [List.mem_singleton] at he; subst he; exact Hbs
    isplitl [HLh Hh]
    · iapply BigSepL.bigSepL_snoc.2; iframe
    · iapply BigSepL.bigSepL_snoc.2; iframe
  iintro HP Hpm
  iNamed HP
  obtain ⟨-, HLk, HLm⟩ := HL
  rw [show (GMap.size pm : Int).toNat = keys.length by omega, List.take_length] at HLk
  rw [show (GMap.size pm : Int).toNat = keys.length by omega, List.drop_length]
  iclear Hrest
  have hlim : l / 4096 < 2 ^ 52 := by omega
  have hLlen : L.length ≤ l / 4096 := by
    have := wr_keys_le keys (l / 4096) Hknd (fun k hk => by
      obtain ⟨pg, hpg⟩ := Option.isSome_iff_exists.1 ((hkb k).1 hk)
      have := (hok k pg hpg).2.2.2
      omega)
    rw [← HLk, List.length_map] at this
    exact this
  try wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := Loc) Pgid.ty Page.ty.PointerType) as %pl' Hpl'
  try wp_auto
  ihave #Hsorter := pages_sorter (E := w64 × Loc × List w8) sl (fun e => e.2.1)
    (fun e => pageHdr e.2.2) $$ Hpkc
  wp_apply (hSort (w64 × Loc × List w8) (interface.mk Pages.ty #sl)
    (pagesR sl (fun e => e.2.1) (fun e => pageHdr e.2.2)) L) $$ [Hsl HLh] as %L' ⟨HR, %Hperm⟩
  · iframe #
    unfold pagesR
    iframe
    ipureintro; omega
  unfold pagesR
  icases HR with ⟨Hsl, HLh⟩
  ihave HLr := (BigSepL.bigSepL_perm (Φ := fun e => pgBufR (GF := GF) e) Hperm).1 $$ HLr
  have HL'k : (L'.map Prod.fst).Perm (bufs.toList.map Prod.fst) := by
    refine (Hperm.map Prod.fst).symm.trans ?_
    rw [HLk]
    exact keys_perm bufs keys Hknd hkb
  have HL'm : ∀ e ∈ L', bufs !! e.1 = some e.2.2 := fun e he => HLm e (Hperm.mem_iff.2 he)
  have HL'len : L'.length ≤ l / 4096 := by rw [← Hperm.length_eq]; exact hLlen
  clear HLk HLm Hperm
  have hlenL : ∀ e ∈ L', e.2.2.length = 4096 * (1 + pageOverflow e.2.2) :=
    fun e he => (hok e.1 e.2.2 (HL'm e he)).2.1
  -- the target slots: the pages' (in `L'`'s order) and the tail's outside the old file, relative
  -- to the file's size; the tail's inside it, untouched
  have hLext : (L'.flatMap extE).Perm (bufSlots bufs) := by
    have e : L'.flatMap extE = (L'.map Prod.fst).flatMap (extB bufs) := by
      rw [List.flatMap_map]
      apply wr_flatMap_congr
      intro e he
      unfold extE extB
      rw [HL'm e he]; rfl
    rw [e]
    exact bufSlots_perm bufs _ HL'k
  have hndB : (bufSlots bufs).Nodup := (List.nodup_append.1 hnd).1
  have hndA : (L'.flatMap extE ++ tOut T om.size).Nodup := by
    have h1 : (L'.flatMap extE ++ tOut T om.size).Perm (bufSlots bufs ++ tOut T om.size) :=
      hLext.append_right _
    refine h1.nodup_iff.2 ?_
    exact hnd.sublist (List.Sublist.append_left (List.filter_sublist) _)
  icases (wrSlotsSz_app (GF := GF) b K.p (bufSlots bufs) T wb om.size).1 $$ Hslots with ⟨HsB, HsT⟩
  ihave HsT := wrSlotsSz_perm b K.p T _ wb om.size (tInOut_perm T om.size) $$ HsT
  icases (wrSlotsSz_app (GF := GF) b K.p (tIn T om.size) (tOut T om.size) wb om.size).1 $$ HsT
    with ⟨HTin, HTout⟩
  ihave HTout := wrSlotsSz_toZ b K.p _ wb om.size
    (fun s hs => hwb s (List.mem_append_right _ (List.mem_filter.1 hs).1))
    (fun s hs => hstr s (List.mem_append_right _ (List.mem_filter.1 hs).1)) $$ HTout
  ihave HsB := wrSlotsSz_toZ b K.p _ wb om.size
    (fun s hs => hwb s (List.mem_append_left _ hs))
    (fun s hs => hstr s (List.mem_append_left _ hs)) $$ HsB
  ihave HsB := (BigSepL.bigSepL_perm hLext).2 $$ HsB
  ihave Hpool0 : [∗list] s ∈ L'.flatMap extE ++ tOut T om.size, slotAnyZ (GF := GF) b K.p om.size s
    $$ [HsB HTout]
  · iapply BigSepL.bigSepL_append.2; iframe
  try wp_auto
  ihave IH : (∃ (j : w64) (pv : Loc) (om' : OsMeta),
      "i" ∷ i_ptr ↦ j ∗ "p" ∷ p_ptr ↦ pv ∗ "Hst" ∷ statsTok r sm q ∗
      "Hm" ∷ osMeta K.p.ino (DFrac.own 1) om' ∗
      "Hdone" ∷ ([∗list] e ∈ L'.take (sint.nat j), pgDone b K.p e) ∗
      "Htodo" ∷ ([∗list] e ∈ L'.drop (sint.nat j), pgBufR e) ∗
      "Hpool" ∷ ([∗list] s ∈ (L'.drop (sint.nat j)).flatMap extE ++ tOut T om.size,
        slotAnyZ b K.p om'.size s) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ L'.length ∧ om'.maps = om.maps ∧ om.size ≤ om'.size ∧
        om'.size ≤ max om.size (4096 * (l / 4096)) ∧ (∀ e ∈ L'.take (sint.nat j),
          4096 * (e.1.toNat + (1 + pageOverflow e.2.2)) ≤ om'.size) ∧
        (om'.size = om.size ∨ om'.size % 4096 = 0)⌝ : IProp GF)
    $$ [i p Hst Hm HLr Hpool0]
  · iexists W64 0, _, om
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.drop_zero]
    simp only [named]
    iframe
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    ipureintro
    refine ⟨by decide, by omega, trivial, Nat.le_refl _, Nat.le_max_left _ _, fun e he => by simp at he,
      Or.inl trivial⟩
  wp_for IH
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  rw [List.length_map] at Hsll
  wp_if_destruct
  · have Hlt : sint.Z j < sint.Z sl.len := by
      first | simpa using Hif | simpa using GoGlobalContext.intoVal_inj_bool Hif
    clear Hif
    obtain ⟨Hj0, Hjl, Hjm, Hjs1, Hjs2, Hjd, Hjz⟩ := Hj
    have Hjn : sint.nat j < L'.length := by have := Hsll.1; word
    obtain ⟨c, Hc⟩ : ∃ c, L'[sint.nat j]? = some c := ⟨_, List.getElem?_eq_getElem Hjn⟩
    have Hcm : c ∈ L' := List.mem_of_getElem? Hc
    have Hget : (L'.map (fun e => e.2.1))[(sint.Z j).toNat]? = some c.2.1 := by
      rw [List.getElem?_map, show (sint.Z j).toNat = sint.nat j from rfl, Hc]; rfl
    try rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len
      from ⟨Hj0, Hlt⟩))]
    wp_apply wp_load_slice_index _ (sint.Z j) _ _ c.2.1 Hj0 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hget
    try wp_auto
    icases BigSepL.bigSepL_mem_acc Hcm $$ HLh with ⟨Hh, HLhb⟩
    wp_apply hOv c.2.1 (pageHdr c.2.2) (DFrac.own 1) $$ [$Hpkc $Hh] as Hh
    try wp_auto
    wp_apply hId c.2.1 (pageHdr c.2.2) (DFrac.own 1) $$ [$Hpkc $Hh] as Hh
    try wp_auto
    -- the page's values
    obtain ⟨hcid, hclen, hc2, hcin⟩ := hok c.1 c.2.2 (HL'm c Hcm)
    have hov : pageOverflow c.2.2 < 2 ^ 32 := by
      unfold pageOverflow; exact BitVec.isLt _
    have e1 : (decode (List.drop 2 (List.drop 2 (List.drop 8 (bytesAt c.2.2 0 16)))) : w32) =
        (pageHdr c.2.2).overflow' := rfl
    have e2 : (decode (List.take 8 (bytesAt c.2.2 0 16)) : w64) = (pageHdr c.2.2).id' := rfl
    have hremv : (W64 (uint.Z (pageHdr c.2.2).overflow') + W64 1) * W64 4096 =
        W64 ((c.2.2.length - 0 : Nat) : Int) := by
      rw [hclen]; unfold pageOverflow at hov ⊢; word
    have hoffv : (pageHdr c.2.2).id' * W64 4096 = W64 ((4096 * c.1.toNat + 0 : Nat) : Int) := by
      unfold pageId at hcid
      have : c.1.toNat < 2 ^ 52 := by omega
      rw [← hcid] at this ⊢; word
    rw [e1, e2, hremv, hoffv, show (zero_val w64 : w64) = W64 ((0 : Nat) : Int) from rfl]
    -- the page's buffer and its slots as one run; the other waiting slots, the pool
    have hsplitL := ext_split L' (sint.nat j) c Hc
    have hndU : ((L'.take (sint.nat j)).flatMap extE ++
        (extE c ++ ((L'.drop (sint.nat j + 1)).flatMap extE ++ tOut T om.size))).Nodup := by
      have := hndA; rw [hsplitL] at this; simpa only [List.append_assoc] using this
    have hndU' : ((L'.drop (sint.nat j + 1)).flatMap extE ++ tOut T om.size).Nodup :=
      (List.nodup_append.1 (List.nodup_append.1 hndU).2.1).2.1
    have hdisC : ∀ s ∈ (L'.drop (sint.nat j + 1)).flatMap extE ++ tOut T om.size,
        s < c.1.toNat ∨ c.1.toNat + (1 + pageOverflow c.2.2) ≤ s := by
      intro s hs
      have hn := (List.nodup_append.1 (List.nodup_append.1 hndU).2.1).2.2
      have : s ∉ extE c := fun h => hn s h s hs rfl
      unfold extE at this
      rw [List.mem_range'_1] at this
      omega
    rw [wr_drop_cons _ _ _ Hc]
    rw [List.flatMap_cons, List.append_assoc]
    icases BigSepL.bigSepL_cons.1 $$ Htodo with ⟨Hcr, Htodo⟩
    icases BigSepL.bigSepL_append.1 $$ Hpool with ⟨Hpc, Hpool⟩
    icases rest_runZ b K.p om'.size c (by omega) $$ [Hh Hcr Hpc] with ⟨%Hcp, Hpb, Hro, Hrc⟩
    · iframe
    rw [← hclen]
    have hcne : c.2.2 ≠ [] := List.ne_nil_of_length_pos (by omega)
    icases Read.bytesPointsto_bounds _ _ _ hcne $$ Hpb with ⟨Hpb, %Hcb⟩
    ihave Hd1 : osBytes (GF := GF) K.p.ino (4096 * c.1.toNat) (DFrac.own 1) [] $$ []
    · iapply (osBytes_nil' (GF := GF) K.p _ _).2; iempintro
    ihave Hd2 : bytesPointsto (GF := GF) (b +ₗ ((4096 * c.1.toNat : Nat) : Int))
        (DFrac.own (1 : Qp).half) (c.2.2.take 0) $$ []
    · rw [List.take_zero]; unfold bytesPointsto; iempintro
    ihave IH2 : (∃ (w : Nat) (ysd : List ByteG) (om2 : OsMeta),
        "rem" ∷ rem_ptr ↦ W64 ((c.2.2.length - w : Nat) : Int) ∗
        "offset" ∷ offset_ptr ↦ W64 ((4096 * c.1.toNat + w : Nat) : Int) ∗
        "written" ∷ written_ptr ↦ W64 ((w : Nat) : Int) ∗ "Hst" ∷ statsTok r sm q ∗
        "Hm" ∷ osMeta K.p.ino (DFrac.own 1) om2 ∗
        "Hd1" ∷ osBytes K.p.ino (4096 * c.1.toNat) (DFrac.own 1) ysd ∗
        "Hd2" ∷ bytesPointsto (b +ₗ ((4096 * c.1.toNat : Nat) : Int)) (DFrac.own (1 : Qp).half)
          (c.2.2.take w) ∗
        "Hro" ∷ oAnyZ K.p om2.size (4096 * c.1.toNat + w) (c.2.2.length - w) ∗
        "Hrc" ∷ cAny b (4096 * c.1.toNat + w) (c.2.2.length - w) ∗
        "Hpool" ∷ ([∗list] s ∈ (L'.drop (sint.nat j + 1)).flatMap extE ++ tOut T om.size,
          slotAnyZ b K.p om2.size s) ∗
        "%Hw" ∷ ⌜w < c.2.2.length ∧ ysd.map Prod.fst = c.2.2.take w ∧ om2.maps = om.maps ∧
          om'.size ≤ om2.size ∧ om2.size ≤ max om.size (4096 * (l / 4096)) ∧
          (0 < w → 4096 * c.1.toNat + w ≤ om2.size) ∧
          (om2.size = om'.size ∨ om2.size = 4096 * c.1.toNat + w)⌝ : IProp GF)
      $$ [rem offset written Hst Hm Hd1 Hd2 Hro Hrc Hpool]
    · iexists 0, [], om'
      simp only [named, Nat.sub_zero, Nat.add_zero]
      iframe
      ipureintro
      exact ⟨by omega, by simp, Hjm, Nat.le_refl _, Hjs2, fun h => absurd h (Nat.lt_irrefl 0),
        Or.inl trivial⟩
    wp_for IH2
    obtain ⟨Hwlt, Hysd, Hom2m, Hom2a, Hom2b, Hom2w, Hom2z⟩ := Hw
    obtain ⟨cs, Hcs⟩ : ∃ cs : Nat, cs = min (c.2.2.length - w) 2147483646 := ⟨_, rfl⟩
    have Hcs0 : 0 < cs := by omega
    have hcin' : 4096 * c.1.toNat + c.2.2.length ≤ l := by
      have := Nat.div_mul_le_self l 4096
      omega
    have hnw : c.2.2.length - w < 2 ^ 63 := by omega
    try simp only [_root_.decide_true, ↓reduceIte]
    try wp_auto
    wp_if_destruct
    focus
      have : 2147483646 < c.2.2.length - w := by
        have h := Hif; rw [show uint.Z (W64 2147483646) = 2147483646 from rfl] at h
        have : uint.Z (W64 ((c.2.2.length - w : Nat) : Int)) = ((c.2.2.length - w : Nat) : Int) := by
          word
        omega
      try wp_auto
      rw [show (W64 2147483646 : w64) = W64 ((cs : Nat) : Int) by rw [Hcs]; congr 1; omega]
    rotate_left
    focus
      have : ¬ 2147483646 < c.2.2.length - w := by
        intro h; apply Hif
        rw [show uint.Z (W64 2147483646) = 2147483646 from rfl]
        have : uint.Z (W64 ((c.2.2.length - w : Nat) : Int)) = ((c.2.2.length - w : Nat) : Int) := by
          word
        omega
      try wp_auto
      rw [show c.2.2.length - w = cs by omega]
      ihave rem : (rem_ptr ↦ W64 ((c.2.2.length - w : Nat) : Int) : IProp GF) $$ [rem]
      · rw [show c.2.2.length - w = cs by omega]; iexact rem
      ihave Hro : oAnyZ (GF := GF) K.p om2.size (4096 * c.1.toNat + w) (c.2.2.length - w) $$ [Hro]
      · rw [show c.2.2.length - w = cs by omega]; iexact Hro
      ihave Hrc : cAny (GF := GF) b (4096 * c.1.toNat + w) (c.2.2.length - w) $$ [Hrc]
      · rw [show c.2.2.length - w = cs by omega]; iexact Hrc
    all_goals
      have hsw : sint.Z (W64 ((w : Nat) : Int)) = (w : Int) := by word
      have hscs : sint.Z (W64 ((cs : Nat) : Int)) = (cs : Int) := by word
      wp_apply hUBS c.2.1 (W64 ((w : Nat) : Int)) (W64 0) (W64 ((cs : Nat) : Int))
        (by simp only [Loc.add, hsw]; omega) (by simp only [Loc.add, hsw, hscs]; omega)
        (by decide) (by rw [hscs]; simp)
      have Hsle : slice.mk (c.2.1 +ₗ sint.Z (W64 ((w : Nat) : Int)) +ₗ sint.Z (W64 0))
          (W64 ((cs : Nat) : Int) - W64 0) (W64 ((cs : Nat) : Int) - W64 0) =
          slice.mk (c.2.1 +ₗ ((w : Nat) : Int)) (W64 ((cs : Nat) : Int)) (W64 ((cs : Nat) : Int)) := by
        have hs0 : (W64 ((cs : Nat) : Int) - W64 0 : w64) = W64 ((cs : Nat) : Int) := by word
        rw [hsw, show sint.Z (W64 0) = 0 from rfl, loc_add_0, hs0]
      rw [Hsle]
      try wp_auto
      -- the chunk, its file bytes and its cells; the gap's cells from the pool
      icases chunk_acc c.2.1 c.2.2 w cs (by omega) Hcs0 (by omega) $$ Hpb with ⟨Hck, Hpbb⟩
      have eo := oAnyZ_app (GF := GF) K.p om2.size (4096 * c.1.toNat + w) cs (c.2.2.length - w - cs)
      have ec := cAny_app (GF := GF) b (4096 * c.1.toNat + w) cs (c.2.2.length - w - cs)
      rw [show cs + (c.2.2.length - w - cs) = c.2.2.length - w by omega] at eo ec
      icases eo.1 $$ Hro with ⟨Hro1, Hro2⟩
      icases ec.1 $$ Hrc with ⟨Hrc1, Hrc2⟩
      icases gap_acc b K.p _ om2.size (4096 * c.1.toNat + w) hndU'
        (fun h => by
          have : w = 0 := by
            refine Classical.byContradiction fun hw => ?_
            have := Hom2w (by omega); omega
          subst this; omega)
        (fun h s hs1 hs2 => by
          have : w = 0 := by
            refine Classical.byContradiction fun hw => ?_
            have := Hom2w (by omega); omega
          subst this
          exact ext_cover L' (sint.nat j) c Hc bufs T om.size om2.size (l / 4096) hLext htail
            (fun e he => by have := Hjd e he; omega) (by omega) s hs1 (by omega) (by omega))
        $$ Hpool with ⟨Hgc, Hgw⟩
      iunfold oAnyZ at Hro1
      iunfold oAny at Hro1
      icases Hro1 with ⟨%xs, Hxs, %Hxl⟩
      have hcl : (bytesAt c.2.2 w cs).length = cs := by
        unfold bytesAt; simp only [List.length_take, List.length_drop]; omega
      have htn : (W64 ((4096 * c.1.toNat + w : Nat) : Int)).toNat = 4096 * c.1.toNat + w := by
        have : 4096 * c.1.toNat + w < 2 ^ 63 := by omega
        word
      have hmc := mcells_single (GF := GF) b l (min (4096 * c.1.toNat + w) om2.size)
        (4096 * c.1.toNat + w + cs - min (4096 * c.1.toNat + w) om2.size) (by omega)
      rw [show min (4096 * c.1.toNat + w) om2.size +
        (4096 * c.1.toNat + w + cs - min (4096 * c.1.toNat + w) om2.size) =
          4096 * c.1.toNat + w + cs by omega] at hmc
      have hgc := cAny_app (GF := GF) b (min (4096 * c.1.toNat + w) om2.size)
        (4096 * c.1.toNat + w - min (4096 * c.1.toNat + w) om2.size) cs
      rw [show min (4096 * c.1.toNat + w) om2.size +
          (4096 * c.1.toNat + w - min (4096 * c.1.toNat + w) om2.size) = 4096 * c.1.toNat + w by omega,
        show 4096 * c.1.toNat + w - min (4096 * c.1.toNat + w) om2.size + cs =
          4096 * c.1.toNat + w + cs - min (4096 * c.1.toNat + w) om2.size by omega] at hgc
      ihave Hc : mcellsAny om2.maps (min (W64 ((4096 * c.1.toNat + w : Nat) : Int)).toNat om2.size)
          ((W64 ((4096 * c.1.toNat + w : Nat) : Int)).toNat + (bytesAt c.2.2 w cs).length)
          $$ [Hgc Hrc1]
      · rw [Hom2m, hmaps, htn, hcl]
        iapply hmc.2
        iapply hgc.2; iframe
      have h0 : 0 ≤ (W64 ((4096 * c.1.toNat + w : Nat) : Int)).toInt := by
        have : 4096 * c.1.toNat + w < 2 ^ 63 := by omega
        rw [BitVec.toInt_eq_toNat_cond]; split <;> omega
      wp_apply hWriteAt f fd K.p.path (DFrac.own 1) _ (bytesAt c.2.2 w cs) (DFrac.own 1)
        (W64 ((4096 * c.1.toNat + w : Nat) : Int)) (DFrac.own 1) ⟨K.p.ino, true, true⟩ om2 xs rfl h0
        (by rw [hcl, htn]; omega) (by rw [hcl]; omega) (by rw [hcl, htn]; omega)
        $$ [Hfo Hck Hfd Hm Hxs Hc] as %nn %err ⟨Hfo, Hck, Hfd, %jj, %aa, %ys, %Hjj, Hm, Hys, Hc, Herr⟩
      · iframe #
        rw [htn, ← fileOwn_eq]
        iframe
      obtain ⟨hjja, hale, -, hysp, -, hres⟩ := Hjj
      have hjjle : jj ≤ (bytesAt c.2.2 w cs).length := Nat.le_trans hjja hale
      rw [htn] at hysp ⊢
      rw [hcl] at hjjle
      have hm3 : (pwPost om2 (4096 * c.1.toNat + w) aa jj).size =
            pwSize om2.size (4096 * c.1.toNat + w) jj ∧
          (pwPost om2 (4096 * c.1.toNat + w) aa jj).maps = om2.maps :=
        ⟨rfl, by simp only [pwPost, announce_maps]⟩
      generalize pwPost om2 (4096 * c.1.toNat + w) aa jj = om3 at hm3 ⊢
      have hyl : ys.length = min (4096 * c.1.toNat + w + cs)
          (pwSize om2.size (4096 * c.1.toNat + w) jj) - min (4096 * c.1.toNat + w) om2.size := by
        have := congrArg List.length hysp
        simp only [List.length_map] at this
        rw [this, pwValsG_length, hcl]
      have hsz3 := pwSize_le om2.size (4096 * c.1.toNat + w) jj cs hjjle
      have hsz3' := pwSize_ge' om2.size (4096 * c.1.toNat + w) jj
      generalize Hsz3 : pwSize om2.size (4096 * c.1.toNat + w) jj = sz3 at hyl hsz3 hsz3' hm3 ⊢
      -- the cells back: the gap's and the chunk's
      ihave Hc : cAny (GF := GF) b (min (4096 * c.1.toNat + w) om2.size)
          (4096 * c.1.toNat + w + cs - min (4096 * c.1.toNat + w) om2.size) $$ [Hc]
      · rw [Hom2m, hmaps, hcl] at *
        iapply hmc.1; iexact Hc
      icases hgc.1 $$ Hc with ⟨Hgc, Hrc1⟩
      -- the bytes back: the gap's, then the chunk's
      have es := osBytes_take_drop (GF := GF) K.p.ino (min (4096 * c.1.toNat + w) om2.size)
        (DFrac.own 1) ys (min (4096 * c.1.toNat + w) sz3 - min (4096 * c.1.toNat + w) om2.size)
        (by omega)
      rw [show min (4096 * c.1.toNat + w) om2.size + (min (4096 * c.1.toNat + w) sz3 -
        min (4096 * c.1.toNat + w) om2.size) = min (4096 * c.1.toNat + w) sz3 by omega] at es
      icases es.1 $$ Hys with ⟨Hyg, Hyc⟩
      ispecialize Hgw $$ %sz3 %(ys.take (min (4096 * c.1.toNat + w) sz3 -
        min (4096 * c.1.toNat + w) om2.size))
      ihave Hpool := Hgw $$ [] Hyg Hgc
      · ipureintro; refine ⟨hsz3', ?_⟩; simp only [List.length_take]; omega
      ihave Hpool := poolZ_resize b K.p _ _ sz3 (fun s hs => by
        have := hdisC s hs
        have := Hom2w
        omega) $$ Hpool
      ihave Hro2 : oAnyZ (GF := GF) K.p sz3 (4096 * c.1.toNat + w + cs) (c.2.2.length - w - cs)
        $$ [Hro2]
      · iapply oAnyZ_congr K.p om2.size sz3 _ _ (by omega); iexact Hro2
      have hysl2 : (ys.drop (min (4096 * c.1.toNat + w) sz3 - min (4096 * c.1.toNat + w) om2.size)).length =
          min (4096 * c.1.toNat + w + cs) sz3 - min (4096 * c.1.toNat + w) sz3 := by
        simp only [List.length_drop]; omega
      cases err with
      | ok ei =>
        have hyd : ysd.length = w := by
          have := congrArg List.length Hysd; simp only [List.length_map, List.length_take] at this
          omega
        cases lg with
        | nil => unfold boltLogger; iexfalso; iexact Hlgok
        | ok li =>
        simp only [fmtErrorOkOrNil]
        icases Herr with #Herr
        try wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl3 ⟨Hsl3, -⟩
        try wp_auto
        wp_apply wp_boltLog li _ _ [W8 100, W8 118] _
          [interface.mkOk go.int64 #(W64 ((4096 * c.1.toNat + w : Nat) : Int)), GoInterface.ok ei]
          _ iprop(True) _ (by decide) (by decide) rfl $$ Hlgok [Hsl3] [] [] as Hsl3 -
        · simp only [show sint.nat (W64 (0 + 1)) = 1 from rfl, List.set_cons_succ,
            List.set_cons_zero]
          iexact Hsl3
        · log_args_ok
        try wp_auto
        wp_for_post
        wp_for_post
        try wp_auto
        ihave Hyc : oAnyZ (GF := GF) K.p sz3 (4096 * c.1.toNat + w) cs $$ [Hyc]
        · unfold oAnyZ oAny; iexists _; iframe Hyc; ipureintro; exact hysl2
        ihave Hcur := cur_anyZ b K.p sz3 c.1.toNat (1 + pageOverflow c.2.2) w cs
          (c.2.2.length - w - cs) ysd (c.2.2.take w) hyd (by simp only [List.length_take]; omega)
          (by rcases Nat.eq_zero_or_pos w with h | h
              · exact Or.inr h
              · exact Or.inl (by have := Hom2w h; omega)) (by omega)
          $$ [Hd1 Hd2 Hyc Hrc1 Hro2 Hrc2]
        · iframe
        ihave Hdz : [∗list] e ∈ L'.take (sint.nat j), [∗list] s ∈ extE e,
            slotAnyZ (GF := GF) b K.p sz3 s $$ [Hdone]
        · iapply BigSepL.bigSepL_mono ?_ $$ Hdone
          intro i e he
          have hm := List.mem_of_getElem? he
          exact pgDone_Z b K.p sz3 e (hlenL e (List.mem_of_mem_take hm))
            (by have := Hjd e hm; omega)
        ihave Hall : [∗list] s ∈ L'.flatMap extE ++ tOut T om.size,
            slotAnyZ (GF := GF) b K.p sz3 s $$ [Hdz Hcur Hpool]
        · rw [hsplitL]
          simp only [List.append_assoc]
          iapply BigSepL.bigSepL_append.2
          isplitl [Hdz]
          · rw [BigSepL.bigSepL_flatMap]; iexact Hdz
          iapply BigSepL.bigSepL_append.2
          isplitl [Hcur]
          · unfold extE; iexact Hcur
          iexact Hpool
        icases errZ_final b K.p bufs _ T wb om.size sz3 hLext hnd (by omega) hwb $$ [Hall HTin]
          with ⟨%wb', ⟨%Hwb1, %Hwb2, %Hwb3⟩, Hwr⟩
        · iframe
        iapply HΦ
        rw [fileOwn_eq]
        iframe Hst Hdb Hf Hwa Hfo Hfd
        isplitl [Hpg Hpl']
        · iexists pl'; iframe
        iexists om3, wb'
        rw [hm3.1]
        iframe Hm
        isplitr
        · ipureintro
          exact ⟨by omega, by omega, hm3.2.trans Hom2m, Hwb1, Hwb2,
            fun s hs _ h2 => by rw [Hwb3 s hs]; omega⟩
        iright
        isplitr
        · ipureintro; exact fun h => nomatch h
        isplitr
        · iexact Herr
        iexact Hwr
      | nil =>
        have hjj : jj = (bytesAt c.2.2 w cs).length := by
          rcases hres with ⟨h1, -, -⟩ | ⟨-, h2⟩
          · exact h1
          · exact absurd rfl h2
        subst hjj
        have hsz3e : sz3 = max om2.size (4096 * c.1.toNat + w + cs) := by
          rw [← Hsz3, hcl]; unfold pwSize; rw [ite_eq_right (by omega)]
        have hmo : min (4096 * c.1.toNat + w) sz3 = 4096 * c.1.toNat + w := by omega
        have hys : (ys.drop (4096 * c.1.toNat + w - min (4096 * c.1.toNat + w) om2.size)).map
            Prod.fst = bytesAt c.2.2 w cs := by
          rw [List.map_drop, hysp]
          exact pwValsG_tail _ _ _ _ (by rw [hcl]; omega)
        rw [hmo] at hysl2 ⊢
        generalize Hys2 : ys.drop (4096 * c.1.toNat + w - min (4096 * c.1.toNat + w) om2.size) =
          ys2 at hys hysl2 ⊢
        have hyl2 : ys2.length = cs := by rw [hysl2]; omega
        try wp_auto
        iunfold cAny at Hrc1
        icases Hrc1 with ⟨%vf, Hc⟩
        ihave Hc : cellsR b (4096 * c.1.toNat + w) ys2.length vf $$ [Hc]
        · rw [hyl2]; iexact Hc
        have hbm : om3.maps !! b = some l := by
          rw [hm3.2, Hom2m, hmaps]; exact GMap.lookup_singleton_eq b l
        have hyl' : 4096 * c.1.toNat + w + ys2.length ≤ l := by rw [hyl2]; omega
        iapply cellsR_agree_bytes _ rfl K.p (DFrac.own 1) om3 b l hbm
          (DFrac.own 1) (by simp) _ ys2 (4096 * c.1.toNat + w) vf hyl' $$ Hos Hm Hyc Hc
        iintro Hm Hys Hc
        icases cellsR_bytes b (ys2.map Prod.fst) _ $$ [Hc] with Hc
        · simp only [List.length_map]; iexact Hc
        rw [hys]
        wp_apply hInc K tx r sm q (W64 1) $$ [Hst] as %_n Hst
        · iframe #; iframe
        try wp_auto
        have hyd : ysd.length = w := by
          have := congrArg List.length Hysd; simp only [List.length_map, List.length_take] at this
          omega
        ihave Hpb := Hpbb $$ Hck
        ihave Hd1 : osBytes (GF := GF) K.p.ino (4096 * c.1.toNat) (DFrac.own 1) (ysd ++ ys2) $$ [Hd1 Hys]
        · iapply (osBytes_take_drop (GF := GF) K.p.ino (4096 * c.1.toNat) (DFrac.own 1) (ysd ++ ys2)
            ysd.length (by simp)).2
          rw [List.take_left, List.drop_left, hyd]
          iframe
        have hfst : (ysd ++ ys2).map Prod.fst = c.2.2.take (w + cs) := by
          rw [List.map_append, Hysd, hys, List.take_add]; rfl
        ihave Hd2 : bytesPointsto (GF := GF) (b +ₗ ((4096 * c.1.toNat : Nat) : Int))
            (DFrac.own (1 : Qp).half) (c.2.2.take (w + cs)) $$ [Hd2 Hc]
        · iapply (bytes_cut b (4096 * c.1.toNat) _ (c.2.2.take (w + cs)) w
            (by simp only [List.length_take]; omega)).2
          rw [List.take_take, Nat.min_eq_left (by omega), List.drop_take,
            show w + cs - w = cs by omega]
          iframe
        have hremv2 : W64 ((c.2.2.length - w : Nat) : Int) - W64 ((cs : Nat) : Int) =
            W64 ((c.2.2.length - (w + cs) : Nat) : Int) :=
          wr_rem_sub c.2.2.length w cs (by omega)
        rw [hremv2]
        wp_if_destruct
        · -- the page is written
          have hend : w + cs = c.2.2.length := by
            have h := Hif
            have : c.2.2.length - (w + cs) < 2 ^ 63 := by omega
            have h2 : (c.2.2.length - (w + cs) : Nat) = 0 := by
              have := congrArg BitVec.toNat h; simp at this; omega
            omega
          rw [hend, List.take_length] at hfst
          rw [hend, List.take_length]
          icases run_pgDone b K.p c (ysd ++ ys2) hfst hclen Hcp $$ [Hpb Hd1 Hd2] with ⟨Hh, Hcd⟩
          · iframe
          ihave HLh := HLhb $$ Hh
          ihave Hdone : [∗list] e ∈ L'.take (sint.nat j) ++ [c], pgDone (GF := GF) b K.p e
            $$ [Hdone Hcd]
          · iapply BigSepL.bigSepL_snoc.2; iframe
          ihave Hdone : [∗list] e ∈ L'.take (sint.nat j + 1), pgDone (GF := GF) b K.p e $$ [Hdone]
          · rw [List.take_add_one, Hc, Option.toList_some]; iexact Hdone
          wp_for_post
          wp_for_post
          have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by
            have : sint.nat j < 2 ^ 62 := by omega
            word
          rw [fileOwn_eq]
          iframe
          iexists j + W64 1, c.2.1, om3
          rw [hj1, hm3.1]
          iframe
          ipureintro
          refine ⟨by word, by omega, hm3.2.trans Hom2m, by omega, by omega, ?_, by omega⟩
          intro e he
          rw [List.take_add_one, Hc, Option.toList_some] at he
          rcases List.mem_append.1 he with he | he
          · have := Hjd e he; omega
          · rw [List.mem_singleton] at he; subst he; omega
        · have hnend : w + cs < c.2.2.length := by
            have h := Hif
            refine Classical.byContradiction fun hc => h ?_
            rw [show c.2.2.length - (w + cs) = 0 by omega]; rfl
          try wp_auto
          have ho : W64 ((4096 * c.1.toNat + w : Nat) : Int) + W64 ((cs : Nat) : Int) =
              W64 ((4096 * c.1.toNat + (w + cs) : Nat) : Int) := by word
          have hw2 : W64 ((w : Nat) : Int) + W64 ((cs : Nat) : Int) = W64 ((w + cs : Nat) : Int) := by
            word
          rw [ho, hw2]
          ihave Hro2 : oAnyZ (GF := GF) K.p sz3 (4096 * c.1.toNat + (w + cs))
            (c.2.2.length - (w + cs)) $$ [Hro2]
          · rw [← Nat.add_assoc, ← Nat.sub_sub]; iexact Hro2
          ihave Hrc2 : cAny (GF := GF) b (4096 * c.1.toNat + (w + cs)) (c.2.2.length - (w + cs))
            $$ [Hrc2]
          · rw [← Nat.add_assoc, ← Nat.sub_sub]; iexact Hrc2
          wp_for_post
          rw [fileOwn_eq]
          iframe
          iexists w + cs, ysd ++ ys2, om3
          rw [hm3.1]
          iframe
          ipureintro
          exact ⟨hnend, hfst, hm3.2.trans Hom2m, by omega, by omega, fun _ => by omega, by omega⟩
  · have Hjl : sint.nat j = L'.length := by have := Hsll.1; word
    obtain ⟨-, -, Hom'm, Hom's1, Hom's2, Hjd, Hjz⟩ := Hj
    rw [Hjl, List.take_length, List.drop_length] at *
    rw [List.flatMap_nil, List.nil_append]
    iclear Htodo
    icases done_split b K.p L' $$ [HLh Hdone] with ⟨Hbufs, Hsd⟩
    · iframe
    try wp_auto
    have hlenB : ∀ id pg, bufs !! id = some pg → pg.length = 4096 * (1 + pageOverflow pg) :=
      fun id pg h => (hok id pg h).2.1
    cases ns
    focus
      -- `NoSync` off: the sync
      try wp_auto
      wp_apply hSync K.db f fd K.p K.p.ino om' dqf (DFrac.own 1) $$ [Hf Hfo Hfd Hm]
        as %e2 ⟨Hf, Hfo, Hfd, ⟨%m', Hm, %Hm'⟩, Hr⟩
      · iframe #; iframe
      icases Hr with (%He | ⟨%He, #Hfe⟩)
      rotate_left
      · cases e2 with
        | nil => exact absurd rfl He
        | ok e2 =>
        cases lg with
        | nil => unfold boltLogger; iexfalso; iexact Hlgok
        | ok li =>
        ihave %hgoos : ⌜goosLinux⌝ $$ []
        · iapply goosLinux_of_pkgInit $$ Hpkg
        ihave %hgoarch : ⌜goarchAmd64⌝ $$ []
        · iapply goarchAmd64_of_pkgInit $$ Hpkg
        unfold goosLinux at hgoos
        unfold goarchAmd64 at hgoarch
        try wp_auto
        try rw [hgoos, hgoarch]
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl3 ⟨Hsl3, -⟩
        try wp_auto
        wp_apply wp_boltLog li _ _ [W8 115, W8 115, W8 118] _
          [interface.mkOk go.string #(go!"linux"), interface.mkOk go.string #(go!"amd64"),
            GoInterface.ok e2] _ iprop(True) _
          (by decide) (by decide) rfl $$ Hlgok [Hsl3] [] [] as Hsl3 -
        · simp only [show sint.nat (W64 (0 + 1)) = 1 from rfl,
            show sint.nat (W64 (0 + 1 + 1)) = 2 from rfl, List.set_cons_succ, List.set_cons_zero]
          iexact Hsl3
        · log_args_ok
        try wp_auto
        ihave Hall := sd_any b K.p L' hlenL $$ Hsd
        ihave Hall := pagesAny_Z b K.p m'.size L' (fun e he => by have := Hjd e he; omega) $$ Hall
        ihave Hpool := poolZ_resize b K.p _ om'.size m'.size (fun s _ => by omega) $$ Hpool
        icases errZ_final b K.p bufs _ T wb om.size m'.size hLext hnd (by omega) hwb $$ [Hall Hpool HTin]
          with ⟨%wb', ⟨%Hwb1, %Hwb2, %Hwb3⟩, Hwr⟩
        · iframe
        try iapply HΦ
        iframe Hst Hdb Hf Hwa Hfo Hfd
        isplitl [Hpg Hpl']
        · iexists pl'; iframe
        iexists m', wb'
        iframe Hm
        isplitr
        · ipureintro
          exact ⟨by omega, by omega, Hm'.2.trans Hom'm, Hwb1, Hwb2,
            fun s hs _ h2 => by rw [Hwb3 s hs]; omega⟩
        iright
        isplitr
        · ipureintro; exact fun h => nomatch h
        isplitr
        · iexact Hfe
        iexact Hwr
      subst He
      try wp_auto
      ihave Hm : (∃ om'' : OsMeta, osMeta K.p.ino (DFrac.own 1) om'' ∗
          ⌜om''.size = om'.size ∧ om''.maps = om.maps⌝ : IProp GF) $$ [Hm]
      · iexists m'; iframe; ipureintro; exact ⟨Hm'.1, Hm'.2.trans Hom'm⟩
    rotate_left
    focus
      try wp_auto
      ihave Hm : (∃ om'' : OsMeta, osMeta K.p.ino (DFrac.own 1) om'' ∗
          ⌜om''.size = om'.size ∧ om''.maps = om.maps⌝ : IProp GF) $$ [Hm]
      · iexists om'; iframe; ipureintro; exact ⟨rfl, Hom'm⟩
    all_goals
      -- the one-page buffers back to the pool
      ihave IH3 : (∃ (j2 : w64) (pv : Loc), "i" ∷ i_ptr ↦ j2 ∗ "p" ∷ p_ptr ↦ pv ∗
          "Hbufs" ∷ ([∗list] e ∈ L'.drop (sint.nat j2), pgBuf e) ∗
          "%Hj2" ∷ ⌜0 ≤ sint.Z j2 ∧ sint.nat j2 ≤ L'.length⌝ : IProp GF) $$ [i p Hbufs]
      · iexists W64 0, _
        rw [show sint.nat (W64 0) = 0 from rfl, List.drop_zero]
        simp only [named]
        iframe
        ipureintro; exact ⟨by decide, by omega⟩
      wp_for IH3
      wp_if_destruct
      · have Hlt2 : sint.Z j2 < sint.Z sl.len := by
          first | simpa using Hif | simpa using GoGlobalContext.intoVal_inj_bool Hif
        clear Hif
        have Hjn2 : sint.nat j2 < L'.length := by have := Hsll.1; word
        obtain ⟨c2, Hc2⟩ : ∃ c, L'[sint.nat j2]? = some c := ⟨_, List.getElem?_eq_getElem Hjn2⟩
        have Hc2m : c2 ∈ L' := List.mem_of_getElem? Hc2
        have Hget2 : (L'.map (fun e => e.2.1))[(sint.Z j2).toNat]? = some c2.2.1 := by
          rw [List.getElem?_map, show (sint.Z j2).toNat = sint.nat j2 from rfl, Hc2]; rfl
        try rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z j2 ∧ sint.Z j2 < sint.Z sl.len
          from ⟨Hj2.1, Hlt2⟩))]
        wp_apply wp_load_slice_index _ (sint.Z j2) _ _ c2.2.1 Hj2.1 $$ [Hsl] as Hsl
        · iframe; ipureintro; exact Hget2
        try wp_auto
        rw [wr_drop_cons _ _ _ Hc2]
        icases BigSepL.bigSepL_cons.1 $$ Hbufs with ⟨Hc2b, Hbufs⟩
        iunfold pgBuf at Hc2b
        icases Hc2b with ⟨Hh2, %Hp2, Hr2⟩
        wp_apply hOv c2.2.1 (pageHdr c2.2.2) (DFrac.own 1) $$ [$Hpkc $Hh2] as Hh2
        try wp_auto
        have hj21 : sint.nat (j2 + W64 1) = sint.nat j2 + 1 := by
          have : sint.nat j2 < 2 ^ 62 := by omega
          word
        have hl2 := hlenL c2 Hc2m
        have e1' : (decode (List.drop 2 (List.drop 2 (List.drop 8 (bytesAt c2.2.2 0 16)))) : w32) =
            (pageHdr c2.2.2).overflow' := rfl
        rw [e1']
        by_cases hov : pageOverflow c2.2.2 = 0
        · have hz : (W64 (uint.Z (pageHdr c2.2.2).overflow') : w64) = W64 0 := by
            unfold pageOverflow at hov
            have h0 : (pageHdr c2.2.2).overflow' = 0 := BitVec.eq_of_toNat_eq (by simpa using hov)
            rw [h0]; rfl
          rw [decide_eq_true hz]
          try wp_auto
          have hl2' : c2.2.2.length = 4096 := by rw [hl2, hov]
          ihave Hpb := (page_split c2.2.1 c2.2.2 (by omega) Hp2).2 $$ [Hh2 Hr2]
          · iframe
          icases Read.bytesPointsto_bounds _ _ _ (List.ne_nil_of_length_pos (by omega)) $$ Hpb
            with ⟨Hpb, %Hb2⟩
          have h00 : sint.Z (W64 0) = 0 := rfl
          have h4096 : sint.Z (W64 4096) = 4096 := rfl
          wp_apply hUBS c2.2.1 (W64 0) (W64 0) (W64 4096)
            (by rw [h00, loc_add_0]; exact Hp2)
            (by rw [h00, loc_add_0, h4096]; have := Hb2.2; rw [hl2'] at this; push_cast at this; omega)
            (by decide) (by decide)
          have Hsle2 : slice.mk (c2.2.1 +ₗ sint.Z (W64 0) +ₗ sint.Z (W64 0)) (W64 4096 - W64 0)
              (W64 4096 - W64 0) =
              slice.mk c2.2.1 (W64 ((c2.2.2.length : Nat) : Int)) (W64 ((c2.2.2.length : Nat) : Int)) := by
            rw [h00, loc_add_0, loc_add_0, hl2']; rfl
          rw [Hsle2]
          ihave Hbuf := (Read.bytesPointsto_ownSlice c2.2.1 _ c2.2.2 Hp2 (by omega)).1 $$ Hpb
          try wp_auto
          rename_i iu
          irename : (iu ↦ (_ : w64) : IProp GF) => Hiu
          have Hpsl : sint.Z (W64 ((c2.2.2.length : Nat) : Int)) = c2.2.2.length := by
            rw [hl2']; rfl
          ihave IH4 : (∃ (k uv : w64), "Hk" ∷ i_ptr ↦ k ∗ "Hiu" ∷ iu ↦ uv ∗
              "Hbuf" ∷ slice.mk c2.2.1 (W64 ((c2.2.2.length : Nat) : Int))
                (W64 ((c2.2.2.length : Nat) : Int)) ↦*
                (List.replicate (sint.nat k) (W8 0) ++ c2.2.2.drop (sint.nat k)) ∗
              "%Hk2" ∷ ⌜0 ≤ sint.Z k ∧ sint.nat k ≤ c2.2.2.length⌝ : IProp GF) $$ [i Hiu Hbuf]
          · iexists W64 0, _
            rw [show sint.nat (W64 0) = 0 from rfl, List.replicate_zero, List.nil_append,
              List.drop_zero]
            simp only [named]
            iframe
            ipureintro; exact ⟨by decide, by omega⟩
          wp_for IH4
          by_cases hk : sint.Z k < sint.Z (W64 ((c2.2.2.length : Nat) : Int))
          · try rw [decide_eq_true hk]
            try simp only [_root_.decide_true, ↓reduceIte]
            have Hkn : sint.nat k < c2.2.2.length := by rw [Hpsl] at hk; word
            have Hbl2 : (List.replicate (sint.nat k) (W8 0) ++ c2.2.2.drop (sint.nat k)).length =
                c2.2.2.length := by simp; omega
            obtain ⟨bk, Hbk⟩ : ∃ bk, (List.replicate (sint.nat k) (W8 0) ++
                c2.2.2.drop (sint.nat k))[sint.nat k]? = some bk :=
              ⟨_, List.getElem?_eq_getElem (by rw [Hbl2]; exact Hkn)⟩
            have Hbd : (0 ≤ sint.Z k ∧ sint.Z k < sint.Z (W64 ((c2.2.2.length : Nat) : Int))) =
                True := eq_true ⟨Hk2.1, hk⟩
            try wp_auto
            try rw [ite_eq_left_of_eq_true _ _ Hbd]
            try (wp_apply wp_load_slice_index _ (sint.Z k) _ _ bk Hk2.1 $$ [Hbuf] as Hbuf
                 focus (iframe; ipureintro; exact Hbk))
            try wp_auto
            try rw [ite_eq_left_of_eq_true _ _ Hbd]
            wp_apply wp_store_slice_index _ (sint.Z k) _ (W8 0) $$ [Hbuf] as Hbuf
            · iframe; ipureintro; rw [Hbl2]; constructor <;> word
            rw [show (sint.Z k).toNat = sint.nat k from rfl, zero_step c2.2.2 _ Hkn]
            try wp_auto
            wp_for_post
            iframe
            iexists k + W64 1, _
            have Hk21 : sint.nat (k + W64 1) = sint.nat k + 1 := by
              have : sint.nat k < 2 ^ 62 := by omega
              word
            rw [Hk21]
            iframe
            ipureintro; exact ⟨by word, by omega⟩
          · try rw [decide_eq_false hk]
            try simp only [Bool.false_eq_true, ↓reduceIte, _root_.decide_false]
            have Hke : sint.nat k = c2.2.2.length := by rw [Hpsl] at hk; word
            rw [Hke, List.drop_length, List.append_nil, hl2']
            try wp_auto
            try rw [decide_eq_false (show ¬ ((#false : val) = #true) from
              fun h => Bool.false_ne_true (GoGlobalContext.intoVal_inj_bool h))]
            try simp only [Bool.false_eq_true, ↓reduceIte]
            try wp_auto
            try rw [if_pos (by decide)]
            try simp only [decide_true, ↓reduceIte]
            try wp_auto
            wp_apply sync.Pool.wp_Put _ pf (poolR _ _ iprop(True)) pageBuf _ $$ [Hbuf]
            · iframe #
              isplitr
              · iapply HisPool
              unfold pageBuf
              iexists _
              iframe
              ipureintro; rfl
            try wp_auto
            wp_for_post
            iframe
            iexists j2 + W64 1, c2.2.1
            rw [hj21]
            iframe
            ipureintro; exact ⟨by word, by omega⟩
        · have hnz : ¬ (W64 (uint.Z (pageHdr c2.2.2).overflow') : w64) = W64 0 := by
            unfold pageOverflow at hov
            intro h; apply hov
            have := (pageHdr c2.2.2).overflow'.isLt
            have h2 := congrArg BitVec.toNat h
            simp only [BitVec.toNat_ofInt] at h2
            simp only [uint.Z] at h2 ⊢
            omega
          rw [decide_eq_false hnz]
          try wp_auto
          wp_for_post
          iframe
          iexists j2 + W64 1, c2.2.1
          rw [hj21]
          iframe
          ipureintro; exact ⟨by word, by omega⟩
      · try wp_auto
        icases done_final b l K.p bufs L' HL'k HL'm hndB hlenB $$ Hsd with ⟨%wb'', %Hwb1, %Hwb2, Hso⟩
        icases Hm with ⟨%om'', Hm, %Hom''⟩
        icases okZ_final b l K.p bufs T wb wb'' om.size om'.size hnd Hom's1 hwb Hwb1
          $$ [Hso Hpool HTin] with ⟨%wb', ⟨%HA, %HB, %HC, %HD⟩, Hso, HT⟩
        · iframe
        try iapply HΦ
        iframe Hst Hdb Hf Hwa Hfo Hfd
        isplitl [Hpg Hpl']
        · iexists pl'; iframe
        iexists om'', wb'
        iframe Hm
        rw [Hom''.1]
        isplitr
        · ipureintro; exact ⟨Hom's1, Hom's2, Hom''.2, HA, HB, fun s hs _ h2 => by rw [HD s hs]; omega⟩
        ileft
        isplitr
        · ipureintro; rfl
        isplitr
        · ipureintro
          refine ⟨fun s hs => ?_, fun id pg hb j hj => ?_, fun s hs h1 h2 => ?_, Hjz⟩
          · obtain ⟨e, he, hse⟩ := List.mem_flatMap.1 (hLext.mem_iff.2 hs)
            have := Hjd e he
            unfold extE at hse
            have := List.mem_range'_1.1 hse
            omega
          · have hs : id.toNat + j ∈ bufSlots bufs := by
              unfold bufSlots
              exact List.mem_flatMap.2 ⟨(id, pg), (GMap.mem_toList _ _ _).2 hb, by simp; omega⟩
            rw [HC _ hs]; exact Hwb2 id pg hb j hj
          · rw [HD s hs]; omega
        iframe
end proof

end bbolt
end EtcdGrove
end Perennial
