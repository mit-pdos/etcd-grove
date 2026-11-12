/-
`tx.write()` with dirty pages past the end of the file (`Tx.write_ext`, maintainer 12's item 3 of
`notes/bbolt-proof-plan.md`; U10w): the target slots relative to the file's current size. A slot
"holding anything at size `sz`" (`slotAnyZ`) owns the page-cache bytes of its part inside the file
(`oAnyZ`: the whole slot inside, a prefix across the end, nothing past it) and the client halves of
all its cells. A write past the end (`WriteAt`) takes the cells of the gap between the file's end and
its offset from the other waiting slots (`gap_acc`) and gives them back with the gap's new bytes.
-/
module

public import Proof.go_etcd_io.bbolt.Commit.WriteLoop
public import Proof.go_etcd_io.bbolt.Inv.WSlots
public import Proof.go_etcd_io.bbolt.Commit.PwMeta

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

/-- After a whole `pwrite` of `data` at `off`, the range's bytes from `off` on are `data`. -/
theorem pwBytes_tail_fst (sz off : Nat) (data : List w8) (xs : List ByteG)
    (h : 0 < data.length) :
    ((pwBytes sz off data data.length xs).drop (off - min off sz)).map Prod.fst = data := by
  have hs : pwSize sz off data.length = max sz (off + data.length) := by
    unfold pwSize; rw [if_neg (by omega)]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_drop, pwBytes_length, hs]; omega
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_drop]
    rw [pwBytes_getElem]
    unfold pwByte
    rw [if_neg (by omega), if_pos (by omega), List.getD_eq_getElem?_getD,
      show min off sz + (off - min off sz + i) - off = i by omega, List.getElem?_eq_getElem h2]
    rfl

theorem pwSize_le (sz off k n : Nat) (hk : k ≤ n) : pwSize sz off k ≤ max sz (off + n) := by
  unfold pwSize; split <;> omega

theorem pwSize_ge' (sz off k : Nat) : sz ≤ pwSize sz off k := by
  unfold pwSize; split <;> omega

/-- The extent of a dirty page `(id, buffer, bytes)`. -/
def extE (e : w64 × Loc × List w8) : List Nat := List.range' e.1.toNat (1 + pageOverflow e.2.2)

end pure

section res
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- The page-cache bytes of `[lo, lo + n)` that lie inside a file of size `sz`, whole. -/
def oAnyZ (p : BFile) (sz lo n : Nat) : IProp GF :=
  oAny p (min lo sz) (min (lo + n) sz - min lo sz)

/-- A target slot holding anything at the file's size `sz`: its bytes inside the file, all its
cells' client halves. -/
def slotAnyZ (b : Loc) (p : BFile) (sz s : Nat) : IProp GF :=
  iprop(oAnyZ p sz (4096 * s) 4096 ∗ cAny b (4096 * s) 4096)

theorem oAnyZ_app (p : BFile) (sz lo n1 n2 : Nat) :
    oAnyZ (GF := GF) p sz lo (n1 + n2) ⊣⊢ oAnyZ p sz lo n1 ∗ oAnyZ p sz (lo + n1) n2 := by
  unfold oAnyZ
  have e := oAny_app (GF := GF) p (min lo sz) (min (lo + n1) sz - min lo sz)
    (min (lo + n1 + n2) sz - min (lo + n1) sz)
  rw [show min lo sz + (min (lo + n1) sz - min lo sz) = min (lo + n1) sz by omega,
    show min (lo + n1) sz - min lo sz + (min (lo + n1 + n2) sz - min (lo + n1) sz) =
      min (lo + (n1 + n2)) sz - min lo sz by omega] at e
  exact e

theorem oAnyZ_zero (p : BFile) (sz lo : Nat) : ⊢ oAnyZ (GF := GF) p sz lo 0 := by
  unfold oAnyZ
  rw [show min (lo + 0) sz - min lo sz = 0 by omega]
  exact oAny_zero p _

theorem oAnyZ_in (p : BFile) (sz lo n : Nat) (h : lo + n ≤ sz) :
    oAnyZ (GF := GF) p sz lo n ⊣⊢ oAny p lo n := by
  unfold oAnyZ
  rw [show min lo sz = lo by omega, show min (lo + n) sz - lo = n by omega]
  exact .rfl

theorem oAnyZ_of (p : BFile) (sz lo n : Nat) (h : lo + n ≤ sz ∨ n = 0) :
    oAny (GF := GF) p lo n ⊢ oAnyZ p sz lo n := by
  rcases h with h | h
  · exact (oAnyZ_in p sz lo n h).2
  · subst h
    iintro -
    iapply oAnyZ_zero

theorem oAnyZ_congr (p : BFile) (sz sz' lo n : Nat)
    (h : (min lo sz = min lo sz' ∧ min (lo + n) sz = min (lo + n) sz') ∨ (sz ≤ lo ∧ sz' ≤ lo)) :
    oAnyZ (GF := GF) p sz lo n ⊢ oAnyZ p sz' lo n := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · unfold oAnyZ; rw [h1, h2]
  · iintro -
    unfold oAnyZ
    rw [show min (lo + n) sz' - min lo sz' = 0 by omega]
    iapply oAny_zero

theorem slotAnyZ_congr (b : Loc) (p : BFile) (sz sz' s : Nat)
    (h : 4096 * (s + 1) ≤ min sz sz' ∨ (sz ≤ 4096 * s ∧ sz' ≤ 4096 * s) ∨ sz = sz') :
    slotAnyZ (GF := GF) b p sz s ⊢ slotAnyZ b p sz' s := by
  unfold slotAnyZ
  exact sep_mono (oAnyZ_congr p sz sz' _ _ (by omega)) .rfl

theorem poolZ_resize (b : Loc) (p : BFile) (U : List Nat) (sz sz' : Nat)
    (h : ∀ s ∈ U, 4096 * (s + 1) ≤ min sz sz' ∨ (sz ≤ 4096 * s ∧ sz' ≤ 4096 * s) ∨ sz = sz') :
    ([∗list] s ∈ U, slotAnyZ (GF := GF) b p sz s) ⊢ [∗list] s ∈ U, slotAnyZ b p sz' s := by
  apply BigSepL.bigSepL_mono
  intro k s hs
  exact slotAnyZ_congr b p sz sz' s (h s (List.mem_of_getElem? hs))

/-- A slot inside the file holding anything, at any larger size. -/
theorem slotAny_Z (b : Loc) (p : BFile) (sz s : Nat) (h : 4096 * (s + 1) ≤ sz) :
    slotAny (GF := GF) b p s ⊢ slotAnyZ b p sz s := by
  refine (slotAny_run b p s).1.trans ?_
  unfold slotAnyZ
  exact sep_mono (oAnyZ_in p sz _ _ (by omega)).2 .rfl

/-- **Slots holding anything at a size are a run.** -/
theorem slotsAnyZ_run (b : Loc) (p : BFile) (sz : Nat) : ∀ (c k : Nat),
    ([∗list] s ∈ List.range' k c, slotAnyZ (GF := GF) b p sz s) ⊣⊢
      oAnyZ p sz (4096 * k) (4096 * c) ∗ cAny b (4096 * k) (4096 * c)
  | 0, k => by
    simp only [List.range'_zero, Nat.mul_zero]
    constructor
    · iintro -
      isplitl
      · iapply oAnyZ_zero
      · iapply cAny_zero
    · iintro -; iapply BigSepL.bigSepL_nil.2; iempintro
  | c + 1, k => by
    have IH := slotsAnyZ_run b p sz c (k + 1)
    rw [show 4096 * (k + 1) = 4096 * k + 4096 by omega] at IH
    rw [List.range'_succ, show 4096 * (c + 1) = 4096 + 4096 * c by omega]
    have A := oAnyZ_app (GF := GF) p sz (4096 * k) 4096 (4096 * c)
    have C := cAny_app (GF := GF) b (4096 * k) 4096 (4096 * c)
    constructor
    · iintro H
      icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H2⟩
      icases IH.1 $$ H2 with ⟨Ho2, Hc2⟩
      unfold slotAnyZ
      icases H1 with ⟨Ho1, Hc1⟩
      isplitl [Ho1 Ho2]
      · iapply A.2; iframe
      · iapply C.2; iframe
    · iintro ⟨Ho, Hc⟩
      icases A.1 $$ Ho with ⟨Ho1, Ho2⟩
      icases C.1 $$ Hc with ⟨Hc1, Hc2⟩
      iapply BigSepL.bigSepL_cons.2
      isplitl [Ho1 Hc1]
      · unfold slotAnyZ; iframe
      · iapply IH.2; iframe

/-- **The gap's cells, lent by the waiting slots** for a write at `off` of a file of size `sz`:
the cells of `[min off sz, off)` (none unless the write starts past the end, at a slot boundary,
every slot of the gap being waiting); given back with the gap's bytes after the write (the file
then of size `sz3`), the slots are at the size `max sz (min off sz3)`. -/
theorem gap_acc (b : Loc) (p : BFile) (U : List Nat) (sz off : Nat) (hnd : U.Nodup)
    (hal : sz < off → off % 4096 = 0)
    (hcov : sz < off → ∀ s, sz < 4096 * (s + 1) → 4096 * s < off → s ∈ U) :
    ([∗list] s ∈ U, slotAnyZ (GF := GF) b p sz s) ⊢
      cAny b (min off sz) (off - min off sz) ∗
      ∀ (sz3 : Nat) (ys : List ByteG), ⌜sz ≤ sz3 ∧ ys.length = min off sz3 - min off sz⌝ -∗
        osBytes p.ino (min off sz) (DFrac.own 1) ys -∗ cAny b (min off sz) (off - min off sz) -∗
        [∗list] s ∈ U, slotAnyZ b p (max sz (min off sz3)) s := by
  by_cases hle : off ≤ sz
  · rw [show min off sz = off by omega, Nat.sub_self]
    iintro H
    isplitr
    · iapply cAny_zero
    iintro %sz3 %ys %hy -
    rw [show max sz (min off sz3) = sz by omega]
    iintro -
    iexact H
  have hal' := hal (by omega)
  obtain ⟨k, rfl⟩ : ∃ k, off = 4096 * k := ⟨off / 4096, by omega⟩
  have hcov' := hcov (by omega)
  let k0 := sz / 4096
  have hk0 : 4096 * k0 ≤ sz := by omega
  have hk0' : sz < 4096 * (k0 + 1) := by omega
  have hkk : k0 < k := by omega
  let R := List.range' k0 (k - k0)
  have hRnd : R.Nodup := List.nodup_range'
  have hRsub : ∀ s ∈ R, s ∈ U := by
    intro s hs
    have := List.mem_range'_1.1 hs
    exact hcov' s (by omega) (by omega)
  obtain ⟨R', hR', hR'U⟩ := List.subperm_of_subset hRnd hRsub
  obtain ⟨U', hU''⟩ := hR'U.exists_perm_append
  have hU' : U.Perm (R ++ U') := hU''.trans (hR'.append_right U')
  have hnd2 : (R ++ U').Nodup := hU'.nodup_iff.1 hnd
  have hU'R : ∀ s ∈ U', s ∉ R := fun s hs hr => (List.nodup_append.1 hnd2).2.2 s hr s hs rfl
  rw [show min (4096 * k) sz = sz by omega]
  have hrun := slotsAnyZ_run (GF := GF) b p sz (k - k0) k0
  have hA := oAnyZ_app (GF := GF) p sz (4096 * k0) (sz - 4096 * k0) (4096 * k - sz)
  have hC := cAny_app (GF := GF) b (4096 * k0) (sz - 4096 * k0) (4096 * k - sz)
  rw [show sz - 4096 * k0 + (4096 * k - sz) = 4096 * (k - k0) by omega,
    show 4096 * k0 + (sz - 4096 * k0) = sz by omega] at hA hC
  iintro H
  icases (BigSepL.bigSepL_perm hU').1 $$ H with H
  icases BigSepL.bigSepL_append.1 $$ H with ⟨HR, HU⟩
  icases hrun.1 $$ HR with ⟨Ho, Hc⟩
  icases hA.1 $$ Ho with ⟨Ho1, -⟩
  icases hC.1 $$ Hc with ⟨Hc1, Hc2⟩
  iframe Hc2
  iintro %sz3 %ys ⟨%h3, %hy⟩ Hy Hc2
  have hsz4 : max sz (min (4096 * k) sz3) = min (4096 * k) sz3 := by omega
  rw [hsz4]
  have hrun4 := slotsAnyZ_run (GF := GF) b p (min (4096 * k) sz3) (k - k0) k0
  have hA4 := oAnyZ_app (GF := GF) p (min (4096 * k) sz3) (4096 * k0) (sz - 4096 * k0)
    (4096 * k - sz)
  rw [show sz - 4096 * k0 + (4096 * k - sz) = 4096 * (k - k0) by omega,
    show 4096 * k0 + (sz - 4096 * k0) = sz by omega] at hA4
  iapply (BigSepL.bigSepL_perm hU').2
  iapply BigSepL.bigSepL_append.2
  isplitl [Ho1 Hc1 Hy Hc2]
  · iapply hrun4.2
    isplitl [Ho1 Hy]
    · iapply hA4.2
      isplitl [Ho1]
      · iapply (oAnyZ_congr p sz _ _ _ (by omega)); iexact Ho1
      · unfold oAnyZ oAny
        iexists ys
        rw [show min sz (min (4096 * k) sz3) = sz by omega]
        iframe Hy
        ipureintro; rw [hy]; omega
    · iapply hC.2; iframe
  · iapply poolZ_resize b p U' sz _ ?_ $$ HU
    intro s hs
    have := hU'R s hs
    simp only [R, List.mem_range'_1] at this
    omega

/-- **The target slots in the writer's form, holding anything at the file's size** (a slot across
the end must hold at least its part inside the file: `h2`, the spec's `hpart`). -/
theorem wrSlotsSz_toZ (b : Loc) (p : BFile) (S : List Nat) (wb : Nat → List w8) (sz : Nat)
    (h1 : ∀ s ∈ S, 4096 * (s + 1) ≤ sz → (wb s).length = 4096)
    (h2 : ∀ s ∈ S, 4096 * s < sz → sz < 4096 * (s + 1) → sz - 4096 * s ≤ (wb s).length) :
    wrSlotsSz (GF := GF) b p S wb sz ⊢ [∗list] s ∈ S, slotAnyZ b p sz s := by
  unfold wrSlotsSz wBytes
  refine BigSepL.bigSepL_sep_eqv.2.trans (BigSepL.bigSepL_mono ?_)
  intro k s hs
  have hm := List.mem_of_getElem? hs
  unfold slotAnyZ oAnyZ oAny cAny
  iintro ⟨Hb, Hc⟩
  iframe Hc
  by_cases hin : 4096 * (s + 1) ≤ sz
  · simp only [hin, ite_true]
    icases Hb with ⟨%xs, Hx, %hx⟩
    iexists xs
    rw [show min (4096 * s) sz = 4096 * s by omega]
    iframe Hx
    ipureintro
    rw [← List.length_map (f := Prod.fst), hx, h1 s hm hin]; omega
  · simp only [hin, ite_false]
    by_cases hst : 4096 * s < sz
    · simp only [hst, ite_true]
      icases Hb with ⟨%xs, Hx, %hx⟩
      iexists xs
      rw [show min (4096 * s) sz = 4096 * s by omega]
      iframe Hx
      ipureintro
      have := h2 s hm hst (by omega)
      rw [← List.length_map (f := Prod.fst), hx, List.length_take]; omega
    · simp only [hst, ite_false]
      iexists []
      isplitl
      · iapply (osBytes_nil' (GF := GF) p _ _).2; iempintro
      · ipureintro; simp only [List.length_nil]; omega

/-- **Slots holding anything at the file's size, in the writer's form**, each holding some 4096
bytes. -/
theorem Z_toWrSlotsSz (b : Loc) (p : BFile) (S : List Nat) (sz : Nat) (hnd : S.Nodup) :
    ([∗list] s ∈ S, slotAnyZ (GF := GF) b p sz s) ⊢
      ∃ f : Nat → List w8, ⌜∀ s ∈ S, (f s).length = 4096⌝ ∗ wrSlotsSz b p S f sz := by
  let Ψ : Nat → List w8 → IProp GF := fun s a => iprop(⌜a.length = 4096⌝ ∗
    ((if 4096 * (s + 1) ≤ sz then
      iprop(∃ xs : List ByteG, osBytes p.ino (4096 * s) (DFrac.own 1) xs ∗
        ⌜xs.map Prod.fst = a⌝)
    else if 4096 * s < sz then
      iprop(∃ xs : List ByteG, osBytes p.ino (4096 * s) (DFrac.own 1) xs ∗
        ⌜xs.map Prod.fst = a.take (sz - 4096 * s)⌝)
    else iprop(emp)) ∗ ∃ vf, cellsR b (4096 * s) 4096 vf))
  have e1 : ([∗list] s ∈ S, slotAnyZ (GF := GF) b p sz s) ⊢ [∗list] s ∈ S, ∃ a, Ψ s a := by
    apply BigSepL.bigSepL_mono
    intro k s _
    unfold slotAnyZ oAnyZ oAny cAny
    iintro ⟨⟨%xs, Hx, %hl⟩, Hc⟩
    by_cases hin : 4096 * (s + 1) ≤ sz
    · iexists xs.map Prod.fst
      simp only [Ψ, hin, ite_true]
      iframe Hc
      rw [show min (4096 * s) sz = 4096 * s by omega] at hl ⊢
      isplitr
      · ipureintro; rw [List.length_map, hl]; omega
      iexists xs; iframe Hx; ipureintro; rfl
    · by_cases hst : 4096 * s < sz
      · iexists xs.map Prod.fst ++ List.replicate (4096 - (sz - 4096 * s)) (0 : w8)
        simp only [Ψ, hin, hst, ite_true, ite_false]
        iframe Hc
        rw [show min (4096 * s) sz = 4096 * s by omega] at hl ⊢
        have hl' : xs.length = sz - 4096 * s := by rw [hl]; omega
        isplitr
        · ipureintro; simp only [List.length_append, List.length_map, List.length_replicate]; omega
        iexists xs; iframe Hx
        ipureintro
        rw [List.take_append_of_le_length (by simp only [List.length_map]; omega),
          List.take_of_length_le (by simp only [List.length_map]; omega)]
      · iexists List.replicate 4096 (0 : w8)
        simp only [Ψ, hin, hst, ite_false]
        iframe Hc
        ipureintro; exact List.length_replicate
  iintro H
  ihave H := e1 $$ H
  icases bigSepL_choose Ψ S hnd $$ H with ⟨%f, H⟩
  icases bigSepL_pure_out S (fun s => (f s).length = 4096) _ $$ H with ⟨%Hl, H⟩
  iexists f
  isplitr
  · ipureintro; exact Hl
  unfold wrSlotsSz wBytes
  iapply BigSepL.bigSepL_sep_eqv.1
  iexact H

theorem wrSlotsSz_perm (b : Loc) (p : BFile) (S S' : List Nat) (wb : Nat → List w8) (sz : Nat)
    (h : S.Perm S') : wrSlotsSz (GF := GF) b p S wb sz ⊢ wrSlotsSz b p S' wb sz := by
  unfold wrSlotsSz wBytes
  exact sep_mono (BigSepL.bigSepL_perm h).1 (BigSepL.bigSepL_perm h).1

/-- A dirty page's buffer past its header. -/
def pgBufR (e : w64 × Loc × List w8) : IProp GF :=
  iprop(⌜0 < e.2.1.addr⌝ ∗ bytesPointsto (e.2.1 +ₗ 16) (DFrac.own 1) (e.2.2.drop 16))

/-- **A dirty page's buffer, per key**: its header and the rest. -/
theorem wr_entryB (pm : GMap w64 Loc) (bufs : GMap w64 (List w8))
    (lim : Nat) (hok : bufsOK bufs lim) (key : w64) (v : Loc) (hv : pm !! key = some v) :
    (∃ pl, ⌜pm !! key = some pl⌝ ∗ ∃ bs, ⌜bufs !! key = some bs⌝ ∗
        bytesPointsto (GF := GF) pl (DFrac.own 1) bs) ⊢
    ∃ bs, ⌜bufs !! key = some bs⌝ ∗ v ↦ pageHdr bs ∗ pgBufR (key, v, bs) := by
  iintro ⟨%pl, %hpl, %bs, %hbs, Hb⟩
  rw [hv] at hpl; cases hpl
  have hl := (hok key bs hbs).2.1
  have hne : bs ≠ [] := List.ne_nil_of_length_pos (by omega)
  icases persistent_entails_left (bytesPointsto_pos _ _ _ hne) $$ Hb with ⟨Hb, %Hp⟩
  icases (page_split v bs (by omega) Hp).1 $$ Hb with ⟨Hh, Hr⟩
  iexists bs
  isplitr
  · ipureintro; exact hbs
  iframe Hh
  unfold pgBufR
  iframe
  ipureintro; exact Hp

/-- **A waiting page, with its header and its slots at the file's size, for its write**: its whole
buffer, and its slots as one run. -/
theorem rest_runZ (b : Loc) (p : BFile) (sz : Nat) (e : w64 × Loc × List w8)
    (h16 : 16 ≤ e.2.2.length) :
    e.2.1 ↦ pageHdr e.2.2 ∗ pgBufR (GF := GF) e ∗ ([∗list] s ∈ extE e, slotAnyZ b p sz s) ⊢
      ⌜0 < e.2.1.addr⌝ ∗ bytesPointsto e.2.1 (DFrac.own 1) e.2.2 ∗
        oAnyZ p sz (4096 * e.1.toNat) (4096 * (1 + pageOverflow e.2.2)) ∗
        cAny b (4096 * e.1.toNat) (4096 * (1 + pageOverflow e.2.2)) := by
  unfold pgBufR extE
  iintro ⟨Hh, ⟨%Hp, Hr⟩, Hs⟩
  isplitr
  · ipureintro; exact Hp
  isplitl [Hh Hr]
  · iapply (page_split e.2.1 e.2.2 h16 Hp).2; iframe
  iapply (slotsAnyZ_run b p sz _ _).1; iexact Hs

/-- A written page inside the file: its slots, holding anything at the file's size. -/
theorem pgDone_Z (b : Loc) (p : BFile) (sz : Nat) (e : w64 × Loc × List w8)
    (hl : e.2.2.length = 4096 * (1 + pageOverflow e.2.2))
    (hin : 4096 * (e.1.toNat + (1 + pageOverflow e.2.2)) ≤ sz) :
    pgDone (GF := GF) b p e ⊢ [∗list] s ∈ extE e, slotAnyZ b p sz s := by
  refine (pgDone_any b p e hl).trans ?_
  unfold extE
  apply BigSepL.bigSepL_mono
  intro k s hs
  have hm := List.mem_range'_1.1 (List.mem_of_getElem? hs)
  exact slotAny_Z b p sz s (by omega)

/-- **A page interrupted by a failed write**: its slots, holding anything at the file's size `sz`
(its written prefix inside the file). -/
theorem cur_anyZ (b : Loc) (p : BFile) (sz k c' w cs r : Nat) (ysd : List ByteG)
    (P : List w8) (hysd : ysd.length = w) (hP : P.length = w) (hw : 4096 * k + w ≤ sz ∨ w = 0)
    (htot : w + cs + r = 4096 * c') :
    osBytes (GF := GF) p.ino (4096 * k) (DFrac.own 1) ysd ∗
      bytesPointsto (b +ₗ ((4096 * k : Nat) : Int)) (DFrac.own (1 : Qp).half) P ∗
      oAnyZ p sz (4096 * k + w) cs ∗ cAny b (4096 * k + w) cs ∗
      oAnyZ p sz (4096 * k + w + cs) r ∗ cAny b (4096 * k + w + cs) r ⊢
      [∗list] s ∈ List.range' k c', slotAnyZ b p sz s := by
  iintro ⟨H1, H2, H3, H4, H5, H6⟩
  iapply (slotsAnyZ_run b p sz c' k).2
  rw [← htot, Nat.add_assoc w cs r]
  isplitl [H1 H3 H5]
  · iapply (oAnyZ_app p sz _ w _).2
    isplitl [H1]
    · iapply oAnyZ_of p sz _ _ hw
      unfold oAny; iexists ysd; iframe H1; ipureintro; exact hysd
    iapply (oAnyZ_app p sz _ cs _).2
    iframe
  · iapply (cAny_app b _ w _).2
    isplitl [H2]
    · ihave H2 := bytes_cellsR b P (4096 * k) $$ H2
      rw [hP]
      unfold cAny; iexists _; iexact H2
    iapply (cAny_app b _ cs _).2
    iframe

/-- Written pages inside the file, their slots holding anything at its size. -/
theorem pagesAny_Z (b : Loc) (p : BFile) (sz : Nat) (L : List (w64 × Loc × List w8))
    (hin : ∀ e ∈ L, 4096 * (e.1.toNat + (1 + pageOverflow e.2.2)) ≤ sz) :
    ([∗list] e ∈ L, [∗list] s ∈ List.range' e.1.toNat (1 + pageOverflow e.2.2),
        slotAny (GF := GF) b p s) ⊢ [∗list] s ∈ L.flatMap extE, slotAnyZ b p sz s := by
  rw [BigSepL.bigSepL_flatMap]
  apply BigSepL.bigSepL_mono
  intro i e he
  have h := hin e (List.mem_of_getElem? he)
  unfold extE
  apply BigSepL.bigSepL_mono
  intro k s hs
  have hm := List.mem_range'_1.1 (List.mem_of_getElem? hs)
  exact slotAny_Z b p sz s (by omega)

/-- The tail `T` split by the old file: the slots inside it (untouched) and the others. -/
abbrev tIn (T : List Nat) (sz0 : Nat) : List Nat := T.filter (fun s => decide (4096 * (s + 1) ≤ sz0))
abbrev tOut (T : List Nat) (sz0 : Nat) : List Nat :=
  T.filter (fun s => !decide (4096 * (s + 1) ≤ sz0))

theorem tInOut_perm (T : List Nat) (sz0 : Nat) : T.Perm (tIn T sz0 ++ tOut T sz0) :=
  (List.filter_append_perm _ T).symm

/-- **On an error**: every target slot (the pages' `A`, a permutation of `bufSlots`, the tail's
outside the old file) holding anything at the size `sz`, and the tail's slots inside the old file
untouched, are the spec's slots, each holding a whole page's bytes. -/
theorem errZ_final (b : Loc) (p : BFile) (bufs : GMap w64 (List w8)) (A T : List Nat)
    (wb : Nat → List w8) (sz0 sz : Nat) (hA : A.Perm (bufSlots bufs))
    (hnd : (bufSlots bufs ++ T).Nodup) (hle : sz0 ≤ sz)
    (hwb : ∀ s ∈ bufSlots bufs ++ T, 4096 * (s + 1) ≤ sz0 → (wb s).length = 4096) :
    ([∗list] s ∈ A ++ tOut T sz0, slotAnyZ (GF := GF) b p sz s) ∗ wrSlotsSz b p (tIn T sz0) wb sz0 ⊢
      ∃ wb' : Nat → List w8,
        ⌜(∀ s ∈ bufSlots bufs ++ T, 4096 * (s + 1) ≤ sz → (wb' s).length = 4096) ∧
          (∀ s ∈ T, 4096 * (s + 1) ≤ sz0 → wb' s = wb s) ∧
          ∀ s ∈ bufSlots bufs ++ T, (wb' s).length = 4096⌝ ∗
        wrSlotsSz b p (bufSlots bufs ++ T) wb' sz := by
  have hP : (A ++ tOut T sz0 ++ tIn T sz0).Perm (bufSlots bufs ++ T) := by
    rw [List.append_assoc]
    refine List.Perm.append hA ?_
    exact (List.perm_append_comm).trans (tInOut_perm T sz0).symm
  have hnd2 : (A ++ tOut T sz0 ++ tIn T sz0).Nodup := hP.nodup_iff.2 hnd
  have hndA : (A ++ tOut T sz0).Nodup := (List.nodup_append.1 hnd2).1
  have hdis : ∀ s ∈ tIn T sz0, s ∉ A ++ tOut T sz0 :=
    fun s hs hs' => (List.nodup_append.1 hnd2).2.2 s hs' s hs rfl
  iintro ⟨H, Hin⟩
  icases Z_toWrSlotsSz b p _ sz hndA $$ H with ⟨%f, %hf, H⟩
  iexists wbUpd (A ++ tOut T sz0) f wb
  have hall : ∀ s ∈ bufSlots bufs ++ T, (wbUpd (A ++ tOut T sz0) f wb s).length = 4096 := by
    intro s hs
    by_cases hm : s ∈ A ++ tOut T sz0
    · simp only [wbUpd, hm, ite_true]; exact hf s hm
    · simp only [wbUpd, hm, ite_false]
      have hs2 := hP.mem_iff.2 hs
      rcases List.mem_append.1 hs2 with h | h
      · exact absurd h hm
      · have h' := List.mem_filter.1 h
        exact hwb s (List.mem_append_right _ (h'.1)) (by simpa using h'.2)
  isplitr
  · ipureintro
    refine ⟨fun s hs _ => hall s hs, ?_, hall⟩
    · intro s hs hs'
      have hm : s ∈ tIn T sz0 := List.mem_filter.2 ⟨hs, by simpa using hs'⟩
      simp only [wbUpd, hdis s hm, ite_false]
  iapply wrSlotsSz_perm b p _ _ _ sz hP
  iapply (wrSlotsSz_app b p _ _ _ sz).2
  isplitl [H]
  · iapply wrSlotsSz_congr b p _ f _ sz (fun s hs => by simp only [wbUpd, hs, ite_true]) $$ H
  · iapply wrSlotsSz_congr b p _ wb _ sz (fun s hs => by simp only [wbUpd, hdis s hs, ite_false])
    iapply wrSlotsSz_grow b p _ wb sz0 sz hle (fun s hs => by
      have := (List.mem_filter.1 hs).2; simpa using this)
    iexact Hin

/-- `slotsOwn` only reads the bytes on its slots. -/
theorem slotsOwn_congrZ (ms : MapSt) (p : BFile) (S : List Nat) (bs bs' : Nat → List w8)
    (h : ∀ s ∈ S, bs s = bs' s) : slotsOwn (GF := GF) ms p S bs ⊢ slotsOwn ms p S bs' := by
  unfold slotsOwn
  apply BigSepL.bigSepL_mono
  intro k x hx
  have he := h _ (List.mem_of_getElem? hx)
  rcases ms with _ | ⟨base, _⟩ <;> simp only [he] <;> exact .rfl

/-- **On success**: the pages' slots (`slotsOwn`, holding `wb''`) and the tail: the tail's slots
outside the old file holding anything at the size `sz`, those inside untouched; every slot then
holds a whole page's bytes. -/
theorem okZ_final (b : Loc) (l : Nat) (p : BFile) (bufs : GMap w64 (List w8)) (T : List Nat)
    (wb wb'' : Nat → List w8) (sz0 sz : Nat) (hnd : (bufSlots bufs ++ T).Nodup) (hle : sz0 ≤ sz)
    (hwb : ∀ s ∈ bufSlots bufs ++ T, 4096 * (s + 1) ≤ sz0 → (wb s).length = 4096)
    (hwb'' : ∀ s ∈ bufSlots bufs, (wb'' s).length = 4096) :
    slotsOwn (GF := GF) (some (b, l) : MapSt) p (bufSlots bufs) wb'' ∗
      ([∗list] s ∈ tOut T sz0, slotAnyZ b p sz s) ∗ wrSlotsSz b p (tIn T sz0) wb sz0 ⊢
      ∃ wb' : Nat → List w8,
        ⌜(∀ s ∈ bufSlots bufs ++ T, 4096 * (s + 1) ≤ sz → (wb' s).length = 4096) ∧
          (∀ s ∈ T, 4096 * (s + 1) ≤ sz0 → wb' s = wb s) ∧ (∀ s ∈ bufSlots bufs, wb' s = wb'' s) ∧
          ∀ s ∈ bufSlots bufs ++ T, (wb' s).length = 4096⌝ ∗
        slotsOwn (some (b, l) : MapSt) p (bufSlots bufs) wb' ∗ wrSlotsSz b p T wb' sz := by
  have hdBT : ∀ s ∈ T, s ∉ bufSlots bufs := fun s hs hs' => (List.nodup_append.1 hnd).2.2 s hs' s hs rfl
  have hndT : T.Nodup := (List.nodup_append.1 hnd).2.1
  have hP := tInOut_perm T sz0
  have hnd2 : (tIn T sz0 ++ tOut T sz0).Nodup := hP.nodup_iff.1 hndT
  have hndO : (tOut T sz0).Nodup := (List.nodup_append.1 hnd2).2.1
  have hdis : ∀ s ∈ tIn T sz0, s ∉ tOut T sz0 :=
    fun s hs hs' => (List.nodup_append.1 hnd2).2.2 s hs s hs' rfl
  iintro ⟨Ho, H, Hin⟩
  icases Z_toWrSlotsSz b p _ sz hndO $$ H with ⟨%f, %hf, H⟩
  iexists wbUpd (bufSlots bufs) wb'' (wbUpd (tOut T sz0) f wb)
  have hall : ∀ s ∈ bufSlots bufs ++ T,
      (wbUpd (bufSlots bufs) wb'' (wbUpd (tOut T sz0) f wb) s).length = 4096 := by
      intro s hs
      by_cases hb : s ∈ bufSlots bufs
      · simp only [wbUpd, hb, ite_true]; exact hwb'' s hb
      · simp only [wbUpd, hb, ite_false]
        have hT : s ∈ T := by
          rcases List.mem_append.1 hs with h | h
          · exact absurd h hb
          · exact h
        by_cases ho : s ∈ tOut T sz0
        · simp only [ho, ite_true]; exact hf s ho
        · simp only [ho, ite_false]
          have hi : s ∈ tIn T sz0 := by
            rcases List.mem_append.1 (hP.mem_iff.1 hT) with h | h
            · exact h
            · exact absurd h ho
          exact hwb s hs (by have := (List.mem_filter.1 hi).2; simpa using this)
  isplitr
  · ipureintro
    refine ⟨fun s hs _ => hall s hs, ?_, fun s hs => by simp only [wbUpd, hs, ite_true], hall⟩
    · intro s hs hs'
      have hi : s ∈ tIn T sz0 := List.mem_filter.2 ⟨hs, by simpa using hs'⟩
      simp only [wbUpd, hdBT s hs, hdis s hi, ite_false]
  isplitl [Ho]
  · iapply slotsOwn_congrZ _ _ _ wb'' _ (fun s hs => by simp only [wbUpd, hs, ite_true]) $$ Ho
  iapply wrSlotsSz_perm b p _ _ _ sz hP.symm
  iapply (wrSlotsSz_app b p _ _ _ sz).2
  isplitl [Hin]
  · iapply wrSlotsSz_congr b p _ wb _ sz (fun s hs => by
      have hT := (List.mem_filter.1 hs).1
      simp only [wbUpd, hdBT s hT, hdis s hs, ite_false])
    iapply wrSlotsSz_grow b p _ wb sz0 sz hle (fun s hs => by
      have := (List.mem_filter.1 hs).2; simpa using this)
    iexact Hin
  · iapply wrSlotsSz_congr b p _ f _ sz (fun s hs => by
      have hT := (List.mem_filter.1 hs).1
      simp only [wbUpd, hdBT s hT, hs, ite_false, ite_true]) $$ H

end res

end bbolt
end EtcdGrove
end Perennial
