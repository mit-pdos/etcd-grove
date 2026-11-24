-- The copy for the part `KvNet/` of `WalTester/Proof/github_com/mit_pdos/etcd_grove/examples/lib/durable/Boot.lean` (etc/copy-part.py; rerun it, do not edit).
/- Lean-first (no Rocq counterpart).

# `examples/lib/durable` over `fsExt`: a generation's boot (W4c U2, `notes/wal-fsext-w4c-plan.md`)

`durBoot`: at a generation's start, from its tree's shared view (`osShared`: the shared invariant, a whole
claim on every name of the file's directory, nothing logged), from what the generation found at the file's
names (`durFound`: no file and the contents `none`, or a file whose start resources the generation holds,
its contents `v`; `durFoundTmp`: no temporary, or a file there held whole), the file's invariant, a handle,
the client's half of the state `⟨v, none⟩` and the crash token, under fresh ghost names. The directory is
a root (its spine `osPathS_root`).

`durBootOnly`: the same boot from a claim on only the file's two names (the file's and its temporary's),
for a directory that holds other files too.

`durBoot0`: the first boot, neither the file nor its temporary present (the WAL tester's `DurBoot0`).
A crash's boot takes `durFound`/`durFoundTmp` from the crash lemma (`Crash.lean`, `durInv_crash`).
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.lib.durable.Inv

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace DurFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs

/-! ## Pure facts -/

theorem entsOf_entry (m : Tree) (j : Ino) (b : GoString) : entsOf m j !! b = m.entry j b := by
  unfold entsOf Tree.entry
  cases m !! j <;> rfl

/-- A claim of a history with nothing logged: its names as the tree has them. -/
theorem namesOf_nil' {V : Hist} (hV : V.2 = []) (j : Ino) (N : NameSet) :
    namesOf V j N = ⟨restrictN N (entsOf V.now j), [], restrictN N (entsOf V.now j)⟩ := by
  have hnow : V.now = V.1 := by simp [Hist.now, Hist.ops, hV, replay]
  unfold namesOf
  simp [hV, hnow]

/-- A claim's name of a history with nothing logged. -/
theorem namesOf_nil_lookup {V : Hist} (hV : V.2 = []) (j : Ino) (b : GoString) :
    (namesOf V j (.only [b])).cur !! b = V.now.entry j b ∧
      (namesOf V j (.only [b])).boot !! b = V.now.entry j b ∧
      (namesOf V j (.only [b])).ents = [] := by
  rw [namesOf_nil' hV]
  have h := restrictN_lookup (.only [b]) (entsOf V.now j) b (by simp [NameSet.Mem])
  rw [entsOf_entry] at h
  exact ⟨h, h, rfl⟩

theorem namesOf_nil_valAfter {V : Hist} (hV : V.2 = []) (j : Ino) (b : GoString) (K : Nat → Prop) :
    (namesOf V j (.only [b])).valAfter j K b = V.now.entry j b := by
  obtain ⟨-, hb, he⟩ := namesOf_nil_lookup hV j b
  unfold NamesH.valAfter
  rw [he]
  simpa using hb

theorem namesOf_nil_next {V : Hist} (hV : V.2 = []) (j : Ino) (b : GoString) :
    (namesOf V j (.only [b])).next = 0 := by
  unfold NamesH.next
  rw [(namesOf_nil_lookup hV j b).2.2]
  rfl

theorem DFile.tb_ne (f : DFile) : f.tb ≠ f.b := by
  intro h
  have := congrArg List.length h
  simp [DFile.tb] at this
  omega

theorem inter_only (b : GoString) : (NameSet.except []).inter [b] = .only [b] := by
  simp [NameSet.inter]

theorem inter_only' {b b' : GoString} (h : b' ≠ b) : (NameSet.except [b]).inter [b'] = .only [b'] := by
  simp [NameSet.inter, h]

/-- The boot's physical state, nothing logged, the candidates `cs`. -/
abbrev bootPhys (f : DFile) (V : Hist) (cs : List DCand) : DurPhys :=
  ⟨namesOf V f.J (.only [f.b]), namesOf V f.J (.only [f.tb]), 0, cs, none⟩

/-- **The boot's invariant facts**: the name holding nothing (no candidate) or a candidate's file. -/
theorem durOk_boot {f : DFile} {V : Hist} (hV : V.2 = []) {v : Option GoString} {cs : List DCand}
    (hcs : (V.now.entry f.J f.b = none ∧ v = none ∧ cs = []) ∨
      ∃ c, V.now.entry f.J f.b = some (.file c.i) ∧ v = some c.v ∧ cs = [c] ∧ c.Ok)
    (ht : ∀ J, V.now.entry f.J f.tb ≠ some (.dir J)) :
    DurOk f ⟨v, none⟩ (bootPhys f V cs) := by
  obtain ⟨hbc, hbb, -⟩ := namesOf_nil_lookup hV f.J f.b
  obtain ⟨htc, htb, hte⟩ := namesOf_nil_lookup hV f.J f.tb
  refine ⟨fun K _ => ?_, ?_, fun J => ?_, fun _ => ?_, fun c hc => ?_, ?_, rfl, ?_⟩
  · show OutOk ⟨v, none⟩ cs ((namesOf V f.J (.only [f.b])).valAfter f.J K f.b)
    rw [namesOf_nil_valAfter hV]
    rcases hcs with ⟨he, rfl, rfl⟩ | ⟨c, he, rfl, rfl, -⟩
    · rw [he]; exact Or.inl rfl
    · rw [he]; exact ⟨c, List.mem_singleton_self _, rfl, Or.inl rfl⟩
  · rcases hcs with ⟨he, rfl, rfl⟩ | ⟨c, he, rfl, rfl, -⟩
    · show (namesOf V f.J (.only [f.b])).cur !! f.b = none
      rw [hbc, he]
    · show ∃ c' ∈ [c], c'.v = c.v ∧ (namesOf V f.J (.only [f.b])).cur !! f.b = some (.file c'.i)
      exact ⟨c, List.mem_singleton_self _, rfl, by rw [hbc, he]⟩
  · show (namesOf V f.J (.only [f.tb])).cur !! f.tb ≠ some (.dir J)
    rw [htc]; exact ht J
  · show (namesOf V f.J (.only [f.b])).next ≤ 0
    rw [namesOf_nil_next hV]
    exact Nat.le_refl 0
  · rcases hcs with ⟨-, -, rfl⟩ | ⟨c', -, -, rfl, hc'⟩
    · cases hc
    · rw [List.mem_singleton.1 hc]; exact hc'
  · rcases hcs with ⟨-, -, rfl⟩ | ⟨c', -, -, rfl, -⟩
    · exact List.nodup_nil
    · exact List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩
  · refine ⟨fun J => ?_, fun xe hxe => ?_⟩
    · show (namesOf V f.J (.only [f.tb])).boot !! f.tb ≠ some (.dir J)
      rw [htb]; exact ht J
    · rw [show (bootPhys f V cs).ht = namesOf V f.J (.only [f.tb]) from rfl, hte] at hxe
      cases hxe

/-! ## What a generation finds at the file's names -/

section found
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- **What the generation finds at the file's name** in its first tree `m`, its contents `v`: no file
(`v = none`), or a file whose start resources it holds (`osFileStart`: its `OsMeta` and bytes whole,
on disk), its contents `v` (shorter than `2^63`, as `Write`'s); never a directory. -/
def durFound (f : DFile) (m : Tree) (v : Option GoString) : IProp GF :=
  match m.entry f.J f.b with
  | none => iprop(⌜v = none⌝)
  | some (.file i) => iprop(∃ fl : OsFile,
      ⌜v = some fl.contents ∧ fl.contents.length < 2 ^ 63⌝ ∗ osFileStart (L := L) i fl)
  | some (.dir _) => iprop(False)

/-- **What the generation finds at the temporary's name**: nothing, or a file it holds whole; never a
directory. -/
def durFoundTmp (f : DFile) (m : Tree) : IProp GF :=
  match m.entry f.J f.tb with
  | none => iprop(emp)
  | some (.file i) => trFile (hG := ⟨G, L⟩) i False
  | some (.dir _) => iprop(False)

end found

/-! ## The boot -/

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

theorem osMeta_halves_boot (L : GooseLocalGS GF) (i : Ino) (m : OsMeta) :
    osMeta (L := L) i (DFrac.own 1) m ⊣⊢
      osMeta (L := L) i (DFrac.own (1 : Qp).half) m ∗ osMeta (L := L) i (DFrac.own (1 : Qp).half) m := by
  have h := gElem_split (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm i (1 : Qp).half (1 : Qp).half m
  rw [Qp.half_add_half] at h
  exact h

theorem osBytes_halves_boot (L : GooseLocalGS GF) (i : Ino) (off : Nat) (xs : List ByteG) :
    osBytes (L := L) i off (DFrac.own 1) xs ⊣⊢
      osBytes (L := L) i off (DFrac.own (1 : Qp).half) xs ∗
        osBytes (L := L) i off (DFrac.own (1 : Qp).half) xs := by
  have e : osBytes (L := L) i off (DFrac.own ((1 : Qp).half + (1 : Qp).half)) xs ⊣⊢
      osBytes (L := L) i off (DFrac.own (1 : Qp).half) xs ∗
        osBytes (L := L) i off (DFrac.own (1 : Qp).half) xs := by
    unfold osBytes bytesG
    refine BIBase.BiEntails.trans ?_ BigSepL.bigSepL_sep_eqv
    exact ⟨BigSepL.bigSepL_mono_of_forall (fun {_ _} => (gElem_split _ _ _ _ _ _).1),
      BigSepL.bigSepL_mono_of_forall (fun {_ _} => (gElem_split _ _ _ _ _ _).2)⟩
  rw [Qp.half_add_half] at e
  exact e

theorem osNames_halves_boot (L : GooseLocalGS GF) (j : Ino) (N : NameSet) (h : NamesH) :
    osNames (L := L) j N (DFrac.own 1) h ⊣⊢
      osNames (L := L) j N (DFrac.own (1 : Qp).half) h ∗ osNames (L := L) j N (DFrac.own (1 : Qp).half) h := by
  have e := osNames_frac (L := L) j N (1 : Qp).half (1 : Qp).half h
  rw [Qp.half_add_half] at e
  exact e

/-- Nothing is a commit bound for free (`osCommitLb_zero`, without its section's instances). -/
theorem osCommitLb_zero' (L : GooseLocalGS GF) : ⊢ |==> osCommitLb (L := L) 0 := by
  unfold osCommitLb gCommitLb
  letI := (gooseOsGS (L := L)).osAllG
  exact monoNatLbOwn_0 _

/-- A file found is a candidate: its start resources as two halves, its `OsMeta` a synced file's. -/
theorem durFound_cands (L : GooseLocalGS GF) (f : DFile) (V : Hist) (v : Option GoString) :
    ⊢ durFound (L := L) f V.now v -∗
      ∃ cs : List DCand,
        ⌜(V.now.entry f.J f.b = none ∧ v = none ∧ cs = []) ∨
          ∃ c, V.now.entry f.J f.b = some (.file c.i) ∧ v = some c.v ∧ cs = [c] ∧ c.Ok⌝ ∗
        ([∗list] c ∈ cs, candRes (L := L) c (DFrac.own (1 : Qp).half)) ∗
        ([∗list] c ∈ cs, candRes (L := L) c (DFrac.own (1 : Qp).half)) := by
  iintro Hf
  unfold durFound
  cases he : V.now.entry f.J f.b with
  | none =>
    simp only
    icases Hf with %hv
    iexists []
    isplitr
    · ipureintro; simp [hv]
    isplitl
    · iapply BigSepL.bigSepL_nil.2; iempintro
    · iapply BigSepL.bigSepL_nil.2; iempintro
  | some n =>
    cases n with
    | dir J => simp only; icases Hf with %hF; exact hF.elim
    | file i =>
      simp only
      icases Hf with ⟨%fl, %hv, Hfs⟩
      iunfold osFileStart at Hfs
      icases Hfs with ⟨Hm, Hb⟩
      let c : DCand := ⟨i, initMeta fl, fl.contents⟩
      icases (osMeta_halves_boot L i (initMeta fl)).1 $$ Hm with ⟨Hm1, Hm2⟩
      icases (osBytes_halves_boot L i 0 (fl.contents.map durB)).1 $$ Hb with ⟨Hb1, Hb2⟩
      iexists [c]
      isplitr
      · ipureintro
        refine Or.inr ⟨c, rfl, hv.1, rfl, ?_⟩
        refine ⟨?_, ?_, ?_, hv.2⟩ <;> simp [c, initMeta, OsFile.contents]
      isplitl [Hm1 Hb1]
      · iapply BigSepL.bigSepL_cons.2
        isplitl
        · unfold candRes; iframe Hm1 Hb1
        · iapply BigSepL.bigSepL_nil.2; iempintro
      · iapply BigSepL.bigSepL_cons.2
        isplitl
        · unfold candRes; iframe Hm2 Hb2
        · iapply BigSepL.bigSepL_nil.2; iempintro

/-- The temporary found: never a directory, and the handle's `tmpRes`. -/
theorem durFoundTmp_tmpRes (L : GooseLocalGS GF) (f : DFile) (V : Hist) (hV : V.2 = []) :
    ⊢ durFoundTmp (L := L) f V.now -∗
      ⌜∀ J, V.now.entry f.J f.tb ≠ some (.dir J)⌝ ∗
        tmpRes (L := L) f (namesOf V f.J (.only [f.tb])) := by
  iintro Ht
  unfold durFoundTmp tmpRes
  rw [(namesOf_nil_lookup hV f.J f.tb).1]
  cases he : V.now.entry f.J f.tb with
  | none =>
    simp only
    isplitr
    · ipureintro; intro J h; cases h
    iexact Ht
  | some n =>
    cases n with
    | dir J => simp only; icases Ht with %hF; exact hF.elim
    | file i =>
      simp only
      isplitr
      · ipureintro; intro J h; cases h
      iexact Ht

/-- The boot's candidate's other half: the handle's `curRes`. -/
theorem curRes_boot (L : GooseLocalGS GF) (f : DFile) (V : Hist) (cs : List DCand) (hV : V.2 = [])
    {v : Option GoString}
    (hcs : (V.now.entry f.J f.b = none ∧ v = none ∧ cs = []) ∨
      ∃ c, V.now.entry f.J f.b = some (.file c.i) ∧ v = some c.v ∧ cs = [c] ∧ c.Ok) :
    ⊢ ([∗list] c ∈ cs, candRes (L := L) c (DFrac.own (1 : Qp).half)) -∗
      curRes (L := L) f (bootPhys f V cs) := by
  iintro Hc
  have hcur : (bootPhys f V cs).hb.cur !! f.b = V.now.entry f.J f.b :=
    (namesOf_nil_lookup hV f.J f.b).1
  rcases hcs with ⟨he, -, rfl⟩ | ⟨c, he, -, rfl, -⟩
  · iapply (curRes_none (L := L) f (bootPhys f V []) (by rw [hcur, he])).2
    iempintro
  · iapply (curRes_file (L := L) f (bootPhys f V [c]) c.i (by rw [hcur, he])).2
    icases BigSepL.bigSepL_cons.1 $$ Hc with ⟨Hc, -⟩
    iexists c
    iframe Hc
    ipureintro
    exact ⟨List.mem_singleton_self _, rfl⟩

/-- **The boot** (see the file header): from the whole claim on the file's directory, a root, nothing
logged, and what the generation found at the file's names. -/
theorem durBoot (L : GooseLocalGS GF) (f : DFile) (R : Roots) (V : Hist) (v : Option GoString)
    (E : CoPset) (hV : V.2 = []) (hR : (f.d, f.J) ∈ R) (hE : ↑osShN ⊆ E) :
    ⊢ osSharedInv (L := L) R -∗
      osNames (L := L) f.J (.except []) (DFrac.own 1) (namesOf V f.J (.except [])) -∗
      durFound (L := L) f V.now v -∗ durFoundTmp (L := L) f V.now ={E}=∗
      ∃ γ : DurGS, durInv (L := L) γ f ∗ durHandle (L := L) γ f R ∗
        durSt (GF := GF) γ ⟨v, none⟩ ∗ durCrashTok (GF := GF) γ := by
  iintro #Hsh Hall Hf Ht
  -- the two names' claims
  imod osNames_split R f.J (.except []) [f.b] _ hE $$ Hsh Hall with ⟨Hb, Hrest⟩
  rw [namesOf_restrict V f.J (.except []) ((NameSet.except []).inter [f.b])
      (fun b _ => by simp [NameSet.Mem]),
    namesOf_restrict V f.J (.except []) ((NameSet.except []).diff [f.b])
      (fun b _ => by simp [NameSet.Mem]), inter_only]
  have hd : (NameSet.except []).diff [f.b] = .except [f.b] := rfl
  rw [hd]
  imod osNames_split R f.J (.except [f.b]) [f.tb] _ hE $$ Hsh Hrest with ⟨Htb, -⟩
  rw [namesOf_restrict V f.J (.except [f.b]) ((NameSet.except [f.b]).inter [f.tb])
      (fun b hb => by
        rw [inter_only' f.tb_ne] at hb
        simp only [NameSet.Mem, List.mem_singleton] at hb ⊢
        subst hb; exact f.tb_ne),
    inter_only' f.tb_ne]
  icases (osNames_halves_boot L f.J (.only [f.b]) _).1 $$ Hb with ⟨Hb1, Hb2⟩
  icases (osNames_halves_boot L f.J (.only [f.tb]) _).1 $$ Htb with ⟨Ht1, Ht2⟩
  -- the spine, the commit bound, the candidates
  imod osPathS_root R f.d f.J (DFrac.own 1) hR hE $$ Hsh with Hsp
  imod osCommitLb_zero' L with #Hlb
  icases durFound_cands L f V v $$ Hf with ⟨%cs, %hcs, Hc1, Hc2⟩
  icases durFoundTmp_tmpRes L f V hV $$ Ht with ⟨%htd, Ht⟩
  have hok := durOk_boot (f := f) hV hcs htd
  ihave Hcur := curRes_boot L f V cs hV hcs $$ Hc2
  -- the ghost state and the invariant
  imod ghostVar_alloc (GF := GF) (⟨v, none⟩ : DurSt) with ⟨%γs, Hs⟩
  icases (ghostVar_split_half (GF := GF) γs 1 (⟨v, none⟩ : DurSt)).1 $$ Hs with ⟨Hs1, Hs2⟩
  imod ghostVar_alloc (GF := GF) (bootPhys f V cs) with ⟨%γp, Hp⟩
  icases (ghostVar_split_half (GF := GF) γp 1 (bootPhys f V cs)).1 $$ Hp with ⟨Hp1, Hp2⟩
  imod token_alloc (GF := GF) with ⟨%γc, Htok⟩
  imod inv_alloc durN E iprop(durInvBody (L := L) ⟨γs, γp, γc⟩ f ∨
      (crashed (hC := L.goose_crashGS) ∗ durCrashTok (GF := GF) ⟨γs, γp, γc⟩))
    $$ [Hs1 Hp1 Hb1 Ht1 Hc1] with #Hinv
  · inext
    ileft
    unfold durInvBody durPhys
    iexists ⟨v, none⟩, bootPhys f V cs
    iframe Hs1 Hp1 Hb1 Ht1 Hc1 Hlb
    ipureintro; exact hok
  imodintro
  iexists ⟨γs, γp, γc⟩
  unfold durInv durHandle durHandleP durSt durCrashTok durPhys
  iframe Hinv Hs2 Htok
  iexists bootPhys f V cs
  isplitl
  · iexists 1
    iframe Hp2 Hb2 Ht2 Hsp Ht Hcur
  · ipureintro; rfl

/-- **The boot on the file's own names** (`durBoot` with a claim on only the file's two names, `f.b`
and its temporary's `f.tb`, instead of the whole directory): the rest of the directory's names stay
with the caller, e.g. for another durable file in the same directory. -/
theorem durBootOnly (L : GooseLocalGS GF) (f : DFile) (R : Roots) (V : Hist) (v : Option GoString)
    (E : CoPset) (hV : V.2 = []) (hR : (f.d, f.J) ∈ R) (hE : ↑osShN ⊆ E) :
    ⊢ osSharedInv (L := L) R -∗
      osNames (L := L) f.J (.only [f.b, f.tb]) (DFrac.own 1) (namesOf V f.J (.only [f.b, f.tb])) -∗
      durFound (L := L) f V.now v -∗ durFoundTmp (L := L) f V.now ={E}=∗
      ∃ γ : DurGS, durInv (L := L) γ f ∗ durHandle (L := L) γ f R ∗
        durSt (GF := GF) γ ⟨v, none⟩ ∗ durCrashTok (GF := GF) γ := by
  iintro #Hsh Hall Hf Ht
  -- the two names' claims
  imod osNames_split R f.J (.only [f.b, f.tb]) [f.b] _ hE $$ Hsh Hall with ⟨Hb, Htb⟩
  have hi : (NameSet.only [f.b, f.tb]).inter [f.b] = .only [f.b] := by
    simp [NameSet.inter, f.tb_ne]
  have hd : (NameSet.only [f.b, f.tb]).diff [f.b] = .only [f.tb] := by
    simp [NameSet.diff, f.tb_ne]
  rw [namesOf_restrict V f.J (.only [f.b, f.tb]) ((NameSet.only [f.b, f.tb]).inter [f.b])
      (fun b hb => by
        rw [hi] at hb
        simp only [NameSet.Mem, List.mem_singleton] at hb
        subst hb; simp [NameSet.Mem]),
    namesOf_restrict V f.J (.only [f.b, f.tb]) ((NameSet.only [f.b, f.tb]).diff [f.b])
      (fun b hb => by
        rw [hd] at hb
        simp only [NameSet.Mem, List.mem_singleton] at hb
        subst hb; simp [NameSet.Mem]), hi, hd]
  icases (osNames_halves_boot L f.J (.only [f.b]) _).1 $$ Hb with ⟨Hb1, Hb2⟩
  icases (osNames_halves_boot L f.J (.only [f.tb]) _).1 $$ Htb with ⟨Ht1, Ht2⟩
  -- the spine, the commit bound, the candidates
  imod osPathS_root R f.d f.J (DFrac.own 1) hR hE $$ Hsh with Hsp
  imod osCommitLb_zero' L with #Hlb
  icases durFound_cands L f V v $$ Hf with ⟨%cs, %hcs, Hc1, Hc2⟩
  icases durFoundTmp_tmpRes L f V hV $$ Ht with ⟨%htd, Ht⟩
  have hok := durOk_boot (f := f) hV hcs htd
  ihave Hcur := curRes_boot L f V cs hV hcs $$ Hc2
  -- the ghost state and the invariant
  imod ghostVar_alloc (GF := GF) (⟨v, none⟩ : DurSt) with ⟨%γs, Hs⟩
  icases (ghostVar_split_half (GF := GF) γs 1 (⟨v, none⟩ : DurSt)).1 $$ Hs with ⟨Hs1, Hs2⟩
  imod ghostVar_alloc (GF := GF) (bootPhys f V cs) with ⟨%γp, Hp⟩
  icases (ghostVar_split_half (GF := GF) γp 1 (bootPhys f V cs)).1 $$ Hp with ⟨Hp1, Hp2⟩
  imod token_alloc (GF := GF) with ⟨%γc, Htok⟩
  imod inv_alloc durN E iprop(durInvBody (L := L) ⟨γs, γp, γc⟩ f ∨
      (crashed (hC := L.goose_crashGS) ∗ durCrashTok (GF := GF) ⟨γs, γp, γc⟩))
    $$ [Hs1 Hp1 Hb1 Ht1 Hc1] with #Hinv
  · inext
    ileft
    unfold durInvBody durPhys
    iexists ⟨v, none⟩, bootPhys f V cs
    iframe Hs1 Hp1 Hb1 Ht1 Hc1 Hlb
    ipureintro; exact hok
  imodintro
  iexists ⟨γs, γp, γc⟩
  unfold durInv durHandle durHandleP durSt durCrashTok durPhys
  iframe Hinv Hs2 Htok
  iexists bootPhys f V cs
  isplitl
  · iexists 1
    iframe Hp2 Hb2 Ht2 Hsp Ht Hcur
  · ipureintro; rfl

/-- **The first boot** (the WAL tester's `DurBoot0`): neither the file nor its temporary present. -/
theorem durBoot0 (L : GooseLocalGS GF) (f : DFile) (R : Roots) (V : Hist) (E : CoPset)
    (_hf : f.Ok) (hV : V.2 = []) (hR : (f.d, f.J) ∈ R) (hb : V.now.entry f.J f.b = none)
    (ht : V.now.entry f.J f.tb = none) (hE : ↑osShN ⊆ E) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗
      osNames (L := L) f.J (.except []) (DFrac.own 1) (namesOf V f.J (.except [])) ={E}=∗
      ∃ γ : DurGS, durInv (L := L) γ f ∗ durHandle (L := L) γ f R ∗
        durSt (GF := GF) γ ⟨none, none⟩ ∗ durCrashTok (GF := GF) γ := by
  iintro -  #Hsh Hall
  iapply durBoot L f R V none E hV hR hE $$ Hsh Hall
  · unfold durFound; rw [hb]; ipureintro; rfl
  · unfold durFoundTmp; rw [ht]; iempintro

end boot

end DurFs
end EtcdGrove
end Perennial
