/- Lean-first (no Rocq counterpart).

# `examples/lib/durable` over `fsExt`: the crash lemma (W4c U2, `notes/wal-fsext-w4c-plan.md`)

`durInv_crash`: what a client's crash obligation gets of a durable file from the old generation's
invariant (`durInv`, opened with the generation's `crashed` and the file's crash token, so that it stays
closed with them), the client's half of the state `s` (kept), the shared invariant and the generation's
`crashRest`: the contents `v` the crash left, **`s.cur` or, while a `Write` was between its rename and its
commit, `s.alt`'s** (`v = s.cur ∨ s.alt = some v`: the WAL tester's `tOracleFile_crash`), and what the new
generation finds at the file's names (`durFound`, `durFoundTmp`, `Boot.lean`: the new file's start
resources, its contents `v`; the temporary, if a file, whole), with `crashRest` back with those files
taken (`D'`). The boot of the new generation (`durBoot`) takes them, with the whole claim on the
directory from its `osShared`.

How: the crash keeps what the invariant's two claims allow (`crashRest_region`, the commit bound `nc`): the
name holds what `DurOk.crash` allows (`OutOk`: no file, or a candidate's inode holding `cur`'s or `alt`'s
contents), the temporary no directory (`DurOk.tmpH`); a candidate's file is taken with the invariant's
half of its resources (`osCrash_take_runs_keep`): its crash bounds are its size and its bytes durable
(`DCand.Ok`), so the new file holds its contents (`fileCrashedR_cand`). The temporary's file is taken with
no old resources (`crashRest_take_named`).

The premise `hD`: the files already taken (`D`, by another client's crash lemma) are not at the file's
names in the new tree. It holds when every file of `D` is unnamed in the new tree or named in another
directory (`durCrash_hD`), and trivially when the lemma is called first (`durInv_crash0`); the lemma
says where its own takes are named (`f.b` or `f.tb`), for a crash lemma called after it.
-/
module

public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.lib.durable.Boot
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CrashTakeNamed

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace DurFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs

/-! ## Pure facts -/

/-- What a crash leaves at a name is one of its history's versions. -/
theorem valAfter_mem' (h : NamesH) (j : Ino) (K : Nat → Prop) (b : GoString) :
    h.valAfter j K b = h.boot !! b ∨ ∃ xe ∈ h.ents, h.valAfter j K b = xe.2.2 !! b := by
  unfold NamesH.valAfter
  split
  · rename_i xe hxe
    exact .inr ⟨xe, (List.mem_filter.1 (List.mem_of_getLast? hxe)).1, rfl⟩
  · exact .inl rfl

/-- A history holding no directory at `b` leaves none there after a crash. -/
theorem NoDirH.valAfter {h : NamesH} {b : GoString} (hn : NoDirH h b) (j : Ino) (K : Nat → Prop) :
    ∀ J, h.valAfter j K b ≠ some (.dir J) := by
  intro J
  rcases valAfter_mem' h j K b with e | ⟨xe, hxe, e⟩ <;> rw [e]
  · exact hn.1 J
  · exact hn.2 xe hxe J

/-- **A candidate's file after a crash holds its contents**: its crash bounds are its size, its bytes
durable (`DCand.Ok`). -/
theorem fileCrashedR_cand {c : DCand} (hc : c.Ok) {dq : DFrac} {fl : OsFile}
    (h : FileCrashedR c.m [(0, dq, c.v.map durB)] (some fl)) : fl.contents = c.v := by
  obtain ⟨hsz, hlo, hhi, -⟩ := hc
  obtain ⟨-, h1, h2, hrun, -⟩ := h fl rfl
  have hs : fl.size = c.v.length := by omega
  apply List.ext_getElem
  · rw [contents_length, hs]
  · intro k hk1 hk2
    have hk : k < fl.size := by rw [contents_length] at hk1; exact hk1
    have hkl : k < (c.v.map durB).length := by rw [List.length_map]; exact hk2
    rcases hrun (0, dq, c.v.map durB) (List.mem_singleton_self _) k hkl (by simpa using hk) with
      ⟨s, hs'⟩ | ⟨hl, -⟩
    · simp only [List.getElem_map, List.mem_singleton, Prod.mk.injEq, Nat.zero_add] at hs'
      simp only [OsFile.contents, List.getElem_map, List.getElem_range]
      exact hs'.1
    · simp only [Nat.zero_add] at hl
      omega

/-! ## The crash -/

section crash
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

instance durCrashTok_timeless (γ : DurGS) : Timeless (durCrashTok (GF := GF) γ) := by
  unfold durCrashTok; infer_instance

/-- A file a crash kept, taken: held whole (`trFile`). -/
theorem osFileStart_trFile' (L : GooseLocalGS GF) (i : Ino) (f : OsFile) :
    osFileStart (L := L) i f ⊢ trFile (hG := ⟨G, L⟩) i False := by
  unfold osFileStart trFile
  iintro ⟨Hm, Hb⟩
  iexists initMeta f, f.contents.map durB
  iframe Hm Hb
  isplitl []
  · unfold mcellsAny
    exact BigSepM.bigSepM_empty.2
  ipureintro
  refine ⟨by simp [initMeta, contents_length], fun h => h.elim, rfl, rfl, Nat.le_refl _,
    ⟨pageEnd f.size, rfl, le_pageEnd _⟩, fun h => h.elim⟩

/-- **The name after the crash**: what `OutOk` allows, its file taken with the candidate's half. -/
theorem durCrash_name (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF) (f : DFile)
    (D : List Ino) (tt : Bool) (V' : Hist) (s : DurSt) (cs : List DCand)
    (hout : OutOk s cs (V'.now.entry f.J f.b)) (hcs : ∀ c ∈ cs, c.Ok)
    (hD : ∀ i ∈ D, V'.now.entry f.J f.b ≠ some (.file i)) :
    ⊢ ([∗list] c ∈ cs, candRes (L := L) c (DFrac.own (1 : Qp).half)) -∗
      crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' -∗
      ∃ (v : Option GoString) (D1 : List Ino),
        ⌜(v = s.cur ∨ s.alt = some v) ∧ ∀ i ∈ D1, V'.now.entry f.J f.b = some (.file i)⌝ ∗
        durFound (L := L') f V'.now v ∗
        crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) (D1 ++ D) tt V' := by
  iintro Hcs Hcr
  unfold durFound
  cases he : V'.now.entry f.J f.b with
  | none =>
    rw [he] at hout
    iexists none, []
    simp only [List.nil_append]
    iframe Hcr
    ipureintro
    rcases hout with h | h <;> simp [h]
  | some n =>
    cases n with
    | dir J => rw [he] at hout; exact hout.elim
    | file i =>
      rw [he] at hout
      obtain ⟨c, hc, hci, hv⟩ := hout
      subst hci
      icases BigSepL.bigSepL_mem_acc hc $$ Hcs with ⟨Hc, -⟩
      iunfold candRes at Hc
      icases Hc with ⟨Hm, Hb⟩
      have hi : c.i ∉ D := fun hin => hD c.i hin he
      icases osCrash_take_runs_keep Q L L' D tt V' c.i hi (DFrac.own (1 : Qp).half) c.m
        [(0, DFrac.own (1 : Qp).half, c.v.map durB)] $$ Hcr Hm [Hb]
        with ⟨%fo, %hfo, Hst, Hcr, -, -⟩
      · iapply BigSepL.bigSepL_cons.2
        iframe Hb
        iapply BigSepL.bigSepL_nil.2; iempintro
      obtain ⟨hcr, hnm, -⟩ := hfo
      cases fo with
      | none => exact absurd (hnm ⟨f.J, f.b, he⟩) (by simp)
      | some fl =>
        have hct := fileCrashedR_cand (hcs c hc) hcr
        iexists some c.v, [c.i]
        simp only [List.singleton_append]
        iframe Hcr
        isplitr
        · ipureintro
          refine ⟨?_, fun i' hi' => by obtain rfl := List.mem_singleton.1 hi'; first | rfl | exact he⟩
          rcases hv with h | h
          · exact Or.inl h.symm
          · exact Or.inr h
        iexists fl
        unfold osFileStartO
        iframe Hst
        ipureintro
        refine ⟨by rw [hct], ?_⟩
        rw [hct]; exact (hcs c hc).2.2.2

/-- **The temporary after the crash**: never a directory; its file, if any, taken whole. -/
theorem durCrash_tmp (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF) (f : DFile)
    (D : List Ino) (tt : Bool) (V' : Hist) (htd : ∀ J, V'.now.entry f.J f.tb ≠ some (.dir J))
    (hD : ∀ i ∈ D, V'.now.entry f.J f.tb ≠ some (.file i)) :
    ⊢ crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' -∗
      ∃ D2 : List Ino, ⌜∀ i ∈ D2, V'.now.entry f.J f.tb = some (.file i)⌝ ∗
        durFoundTmp (L := L') f V'.now ∗
        crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) (D2 ++ D) tt V' := by
  iintro Hcr
  unfold durFoundTmp
  cases he : V'.now.entry f.J f.tb with
  | none =>
    iexists []
    simp only [List.nil_append]
    iframe Hcr
    ipureintro; intro i hi; cases hi
  | some n =>
    cases n with
    | dir J => exact absurd he (htd J)
    | file i =>
      simp only
      icases crashRest_take_named (gooseOsGS (L := L)) (gooseOsGS (L := L')) Q D tt V' [i]
        (fun i' hi' hD' => by rw [List.mem_singleton.1 hi'] at hD'; exact hD i hD' he)
        (List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩) (fun i' hi' => by rw [List.mem_singleton.1 hi']; exact ⟨f.J, f.tb, he⟩)
        $$ Hcr with ⟨Hf, Hcr⟩
      iexists [i]
      iframe Hcr
      isplitr
      · ipureintro; intro i' hi'; rw [List.mem_singleton.1 hi']
      icases BigSepL.bigSepL_cons.1 $$ Hf with ⟨⟨%fl, Hf⟩, -⟩
      iapply osFileStart_trFile' L' i fl
      iapply (Fs.fileStart_eq (L := L') i fl).1 $$ Hf

/-- **The crash lemma** (see the file header). -/
theorem durInv_crash (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF) (γ : DurGS) (f : DFile)
    (R : Roots) (D : List Ino) (tt : Bool) (V' : Hist) (s : DurSt) (E : CoPset)
    (hE : ↑durN ⊆ E) (hE' : ↑osShN ⊆ E)
    (hD : ∀ i ∈ D, V'.now.entry f.J f.b ≠ some (.file i) ∧ V'.now.entry f.J f.tb ≠ some (.file i)) :
    ⊢ durInv (L := L) γ f -∗ crashed (hC := L.goose_crashGS) -∗ durCrashTok (GF := GF) γ -∗
      durSt (GF := GF) γ s -∗ osSharedInv (L := L) R -∗
      crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' ={E}=∗
      ∃ (v : Option GoString) (D' : List Ino),
        ⌜(v = s.cur ∨ s.alt = some v) ∧
          ∀ i ∈ D', V'.now.entry f.J f.b = some (.file i) ∨ V'.now.entry f.J f.tb = some (.file i)⌝ ∗
        durSt (GF := GF) γ s ∗ durFound (L := L') f V'.now v ∗ durFoundTmp (L := L') f V'.now ∗
        crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) (D' ++ D) tt V' := by
  iintro #Hinv #Hcrd Htok Hs #Hsh Hcr
  -- the crashed tree is well formed: its names unique
  imod crashRest_treeWf Q L L' D tt V' R E hE' $$ Hsh Hcr with ⟨%hwf, Hcr⟩
  have hu := hwf.2.2.2.2
  -- open the old invariant and close it with the crash token
  unfold durInv
  imod inv_acc (E := E) hE $$ Hinv with ⟨Hi, Hclose⟩
  icases Hi with (>Hb | ⟨-, >Ht⟩)
  rotate_left
  · iexfalso; unfold durCrashTok; iapply token_exclusive $$ Htok Ht
  imod Hclose $$ [Htok] with -
  · inext; iright; iframe Hcrd Htok
  iunfold durInvBody at Hb
  icases Hb with ⟨%s', %p, Hs', -, Hb, Ht, #Hlb, Hcs, %hok⟩
  icases durSt_agree γ s s' $$ Hs Hs' with %hss
  subst hss
  -- the tree: what the claims allow
  let cl : List (Claim × DFrac) :=
    [((f.J, .only [f.b], p.hb), DFrac.own (1 : Qp).half), ((f.J, .only [f.tb], p.ht), DFrac.own (1 : Qp).half)]
  imod crashRest_region Q L L' D tt V' R cl p.nc E hE' $$ Hsh Hcr [Hb Ht] Hlb with ⟨%hreg, Hcr, -⟩
  · unfold osClaims
    simp only [cl]
    iapply BigSepL.bigSepL_cons.2
    iframe Hb
    iapply BigSepL.bigSepL_cons.2
    iframe Ht
    iapply BigSepL.bigSepL_nil.2; iempintro
  obtain ⟨K, -, hK2, hK3⟩ := hreg
  have hbv : V'.now.entry f.J f.b = p.hb.valAfter f.J K f.b :=
    hK3 (f.J, .only [f.b], p.hb) (by simp [cl]) f.b (by simp [NameSet.Mem])
  have htv : V'.now.entry f.J f.tb = p.ht.valAfter f.J K f.tb :=
    hK3 (f.J, .only [f.tb], p.ht) (by simp [cl]) f.tb (by simp [NameSet.Mem])
  have hout : OutOk s p.cands (V'.now.entry f.J f.b) := by
    rw [hbv]
    exact hok.crash K (fun y e E hy hyn => hK2 (f.J, .only [f.b], p.hb) (by simp [cl]) y e E hy hyn)
  have htd : ∀ J, V'.now.entry f.J f.tb ≠ some (.dir J) := by
    rw [htv]; exact hok.tmpH.valAfter f.J K
  -- the name, then the temporary
  icases durCrash_name Q L L' f D tt V' s p.cands hout hok.cands (fun i hi => (hD i hi).1) $$ Hcs Hcr
    with ⟨%v, %D1, ⟨%hv, %hD1⟩, Hf, Hcr⟩
  have hD1' : ∀ i ∈ D1 ++ D, V'.now.entry f.J f.tb ≠ some (.file i) := by
    intro i hi he
    rcases List.mem_append.1 hi with hi | hi
    · exact f.tb_ne (hu _ _ _ _ _ he (hD1 i hi)).2
    · exact (hD i hi).2 he
  icases durCrash_tmp Q L L' f (D1 ++ D) tt V' htd hD1' $$ Hcr with ⟨%D2, %hD2, Ht, Hcr⟩
  imodintro
  iexists v, D2 ++ D1
  rw [List.append_assoc]
  iframe Hs Hf Ht Hcr
  ipureintro
  refine ⟨hv, fun i hi => ?_⟩
  rcases List.mem_append.1 hi with hi | hi
  · exact Or.inr (hD2 i hi)
  · exact Or.inl (hD1 i hi)

/-- `durInv_crash`'s `hD` from where the files already taken are named: none in the file's
directory (each unnamed in the new tree, or named in another directory: another client's crash
lemma took only files of its own directories, e.g. the WAL's, under the area). -/
theorem durCrash_hD (f : DFile) (D : List Ino) (V' : Hist)
    (hD : ∀ i ∈ D, ∀ J b, V'.now.entry J b = some (.file i) → J ≠ f.J) :
    ∀ i ∈ D, V'.now.entry f.J f.b ≠ some (.file i) ∧ V'.now.entry f.J f.tb ≠ some (.file i) :=
  fun i hi => ⟨fun he => hD i hi _ _ he rfl, fun he => hD i hi _ _ he rfl⟩

/-- **The crash lemma called first** (nothing taken yet): no premise on the taken files. Its
`D'` is named at the file's two names only, so a crash lemma called after it whose own takes
are named outside `f.J` (or unnamed) meets its premise by unique naming. -/
theorem durInv_crash0 (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF) (γ : DurGS) (f : DFile)
    (R : Roots) (tt : Bool) (V' : Hist) (s : DurSt) (E : CoPset)
    (hE : ↑durN ⊆ E) (hE' : ↑osShN ⊆ E) :
    ⊢ durInv (L := L) γ f -∗ crashed (hC := L.goose_crashGS) -∗ durCrashTok (GF := GF) γ -∗
      durSt (GF := GF) γ s -∗ osSharedInv (L := L) R -∗
      crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) [] tt V' ={E}=∗
      ∃ (v : Option GoString) (D' : List Ino),
        ⌜(v = s.cur ∨ s.alt = some v) ∧
          ∀ i ∈ D', V'.now.entry f.J f.b = some (.file i) ∨ V'.now.entry f.J f.tb = some (.file i)⌝ ∗
        durSt (GF := GF) γ s ∗ durFound (L := L') f V'.now v ∗ durFoundTmp (L := L') f V'.now ∗
        crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D' tt V' := by
  have h := durInv_crash Q L L' γ f R [] tt V' s E hE hE' (fun i hi => by cases hi)
  simp only [List.append_nil] at h
  exact h

end crash

end DurFs
end EtcdGrove
end Perennial
