/- Lean-first (no Rocq counterpart).

# `Create`'s use of the program's part of the area (`walAreaRes`; W4, eleventh session)

`walAreaRes jr` holds the program's half of the area claim `(jr, N, h)` and the whole claims under each
non-WAL name, tagged by the name (`clOf`). `Create` takes `nm.tmp`'s (after `walInvBody_drop` split the
claim on `nm.tmp` off the area claim): `area_takeTmp` gives the temporary directory's contents
(`tmpSub`) and keeps the claims under every other name; `area_give` rebuilds `walAreaRes` from an area
claim (on the same names) that says of every non-WAL name but `nm.tmp` what `h` said, and the
temporary directory's new contents.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.CreateCallees

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure

/-- The pure facts of `walAreaRes` (`Wn` the split names). -/
def AreaOk (N : NameSet) (h : NamesH) (cl : List (GoString × Claim)) (Wn : List GoString) : Prop :=
  (∀ nm, walNameOk nm → N.Mem nm ∨ nm ∈ Wn) ∧ (∀ nm sfx, walNameOk nm → N.Mem (nm ++ go!"." ++ sfx)) ∧
  (∀ b, N.Mem b → ¬ walNameOk b → SubCover (clOf cl b) (h.cur !! b)) ∧
  (∀ nm, walNameOk nm → TmpOk (clOf cl (tmpName nm)) (h.cur !! tmpName nm))

theorem clOf_append (l1 l2 : List (GoString × Claim)) (b : GoString) :
    clOf (l1 ++ l2) b = clOf l1 b ++ clOf l2 b := by
  simp [clOf, List.filter_append]

theorem clOf_filter_ne (cl : List (GoString × Claim)) (t b : GoString) (hb : b ≠ t) :
    clOf (cl.filter (fun c => decide (c.1 ≠ t))) b = clOf cl b := by
  unfold clOf
  rw [List.filter_filter]
  congr 2
  funext c
  by_cases h : c.1 = b
  · subst h; simp [hb]
  · simp [h]

theorem clOf_filter_eq (cl : List (GoString × Claim)) (t : GoString) :
    clOf (cl.filter (fun c => decide (c.1 ≠ t))) t = [] := by
  unfold clOf
  rw [List.filter_filter]
  simp only [List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro c _
  by_cases h : c.1 = t <;> simp [h]

theorem clOf_single_ne (t b : GoString) (c : Claim) (hb : b ≠ t) : clOf [(t, c)] b = [] := by
  simp [clOf, Ne.symm hb]

theorem clOf_single (t : GoString) (c : Claim) : clOf [(t, c)] t = [c] := by
  simp [clOf]

/-- Through one claim of files only, a directory reaches only itself. -/
theorem clReach_single (J J' K : Ino) (hJ : NamesH) (hf : FilesOnly hJ.cur)
    (h : ClReach [(J, NameSet.except [], hJ)] K J') : J' = K := by
  induction h with
  | refl _ => rfl
  | step a b c hh x hm he _ _ =>
    simp only [List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨-, -, rfl⟩ := hm
    obtain ⟨i, hi⟩ := hf x _ he
    cases hi

theorem subCover_none (cl : List Claim) : SubCover cl none := fun _ h => by cases h

theorem subCover_single (J : Ino) (hJ : NamesH) (hf : FilesOnly hJ.cur) :
    SubCover [(J, NameSet.except [], hJ)] (some (.dir J)) := by
  intro K hK J' hr
  have hK' : K = J := by simpa using hK.symm
  subst hK'
  rw [clReach_single K J' K hJ hf hr]
  exact ⟨hJ, List.mem_singleton_self _⟩

/-- **The pure facts rebuilt** with the temporary directory's new contents (`ct`: its claims). -/
theorem areaOk_give (N N' : NameSet) (h h' : NamesH) (cl : List (GoString × Claim))
    (tmp : GoString) (ct : List Claim) (Wn : List GoString) (hok : AreaOk N h cl Wn)
    (hN : ∀ b, N'.Mem b ↔ N.Mem b)
    (htN : ¬ walNameOk tmp)
    (hcur : ∀ b, b ≠ tmp → ¬ walNameOk b → h'.cur !! b = h.cur !! b)
    (hct : SubCover ct (h'.cur !! tmp) ∧ TmpOk ct (h'.cur !! tmp)) :
    AreaOk N' h' (cl.filter (fun c => decide (c.1 ≠ tmp)) ++ ct.map (fun c => (tmp, c))) Wn := by
  obtain ⟨h1, h2, h3, h4⟩ := hok
  have hcl : ∀ b, b ≠ tmp →
      clOf (cl.filter (fun c => decide (c.1 ≠ tmp)) ++ ct.map (fun c => (tmp, c))) b = clOf cl b := by
    intro b hb
    rw [clOf_append, clOf_filter_ne _ _ _ hb]
    have : clOf (ct.map (fun c => (tmp, c))) b = [] := by
      unfold clOf
      simp only [List.map_eq_nil_iff, List.filter_eq_nil_iff, List.mem_map]
      rintro _ ⟨c, -, rfl⟩
      simp [Ne.symm hb]
    rw [this, List.append_nil]
  have hclt : clOf (cl.filter (fun c => decide (c.1 ≠ tmp)) ++ ct.map (fun c => (tmp, c))) tmp = ct := by
    rw [clOf_append, clOf_filter_eq, List.nil_append]
    unfold clOf
    rw [List.filter_eq_self.2 (by intro c hc; obtain ⟨c', -, rfl⟩ := List.mem_map.1 hc; simp)]
    rw [List.map_map]
    exact List.map_id' _
  refine ⟨fun nm hn => (h1 nm hn).imp_left (hN _).2, fun nm sfx hn => (hN _).2 (h2 nm sfx hn), ?_, ?_⟩
  · intro b hb hbn
    by_cases hbt : b = tmp
    · subst hbt; rw [hclt]; exact hct.1
    · rw [hcl b hbt, hcur b hbt hbn]; exact h3 b ((hN b).1 hb) hbn
  · intro nm hn
    have hnt : ¬ walNameOk (tmpName nm) := by
      intro hw; apply hw.2.2; simp [tmpName]
    by_cases hbt : tmpName nm = tmp
    · rw [hbt, hclt]; exact hct.2
    · rw [hcl _ hbt, hcur _ hbt hnt]; exact h4 nm hn

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [W : WalGS GF]

theorem osClaims_nil' : ⊢ osClaims (GF := GF) hG.goose_localGS [] := by
  unfold osClaims; iintro; iapply BigSepL.bigSepL_nil.2; iempintro

theorem osClaims_app (l1 l2 : List (Claim × DFrac)) :
    osClaims (GF := GF) hG.goose_localGS (l1 ++ l2) ⊣⊢
      osClaims hG.goose_localGS l1 ∗ osClaims hG.goose_localGS l2 := by
  unfold osClaims; exact BigSepL.bigSepL_append

/-- The claims split by a tag. -/
theorem osClaims_partition (cl : List (GoString × Claim)) (t : GoString) :
    osClaims (GF := GF) hG.goose_localGS (cl.map (fun c => (c.2, DFrac.own 1))) ⊢
      osClaims hG.goose_localGS ((clOf cl t).map (fun c => (c, DFrac.own 1))) ∗
      osClaims hG.goose_localGS
        ((cl.filter (fun c => decide (c.1 ≠ t))).map (fun c => (c.2, DFrac.own 1))) := by
  induction cl with
  | nil =>
    simp only [List.map_nil, List.filter_nil, clOf]
    iintro -
    isplitl [] <;> iapply osClaims_nil'
  | cons c cl ih =>
    rw [List.map_cons]
    iintro H
    icases (osClaims_cons _ _ _).1 $$ H with ⟨Hc, H⟩
    icases ih $$ H with ⟨H1, H2⟩
    by_cases hc : c.1 = t
    · have e1 : clOf (c :: cl) t = c.2 :: clOf cl t := by simp [clOf, hc]
      have e2 : (c :: cl).filter (fun c => decide (c.1 ≠ t)) = cl.filter (fun c => decide (c.1 ≠ t)) := by
        simp [hc]
      rw [e1, e2, List.map_cons]
      iframe H2
      iapply (osClaims_cons _ _ _).2
      iframe H1
      iexact Hc
    · have e1 : clOf (c :: cl) t = clOf cl t := by simp [clOf, hc]
      have e2 : (c :: cl).filter (fun c => decide (c.1 ≠ t)) = c :: cl.filter (fun c => decide (c.1 ≠ t)) := by
        simp [hc]
      rw [e1, e2, List.map_cons]
      iframe H1
      iapply (osClaims_cons _ _ _).2
      iframe H2
      iexact Hc

/-- A claim of a list taken out. -/
theorem osClaims_take (l : List Claim) (c : Claim) (hc : c ∈ l) :
    osClaims (GF := GF) hG.goose_localGS (l.map (fun c => (c, DFrac.own 1))) ⊢
      osNames (L := hG.goose_localGS) c.1 c.2.1 (DFrac.own 1) c.2.2 := by
  obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hc
  rw [List.map_append, List.map_cons]
  iintro H
  icases (osClaims_app _ _).1 $$ H with ⟨-, H⟩
  icases (osClaims_cons _ _ _).1 $$ H with ⟨H, -⟩
  iexact H

/-- **The temporary directory's contents taken from the area's claims.** -/
theorem area_takeTmp (N : NameSet) (h : NamesH) (cl : List (GoString × Claim)) (nm : GoString)
    (Wn : List GoString) (hok : AreaOk N h cl Wn) (hnm : walNameOk nm) :
    osClaims (GF := GF) hG.goose_localGS (cl.map (fun c => (c.2, DFrac.own 1))) ⊢
      tmpSub (h.cur !! tmpName nm) ∗
      osClaims hG.goose_localGS
        ((cl.filter (fun c => decide (c.1 ≠ tmpName nm))).map (fun c => (c.2, DFrac.own 1))) := by
  have hnt : ¬ walNameOk (tmpName nm) := by
    intro hw; apply hw.2.2; simp [tmpName]
  have hsc := hok.2.2.1 (tmpName nm) (by have := hok.2.1 nm go!"tmp" hnm; simpa [tmpName] using this) hnt
  have htm := hok.2.2.2 nm hnm
  iintro H
  icases osClaims_partition cl (tmpName nm) $$ H with ⟨Ht, H⟩
  iframe H
  rcases htm with he | ⟨J, he, hf⟩
  · rw [he]; simp only [tmpSub]; iempintro
  · rw [he]
    obtain ⟨hJ, hmem⟩ := hsc J he J (.refl J)
    ihave HJ := osClaims_take _ _ hmem $$ Ht
    simp only [tmpSub]
    iexists hJ
    iframe
    ipureintro; exact hf hJ hmem

/-- **`walAreaRes` rebuilt** (see the file header). -/
theorem area_give (N N' : NameSet) (h h' : NamesH) (cl : List (GoString × Claim)) (jr : Ino)
    (tmp : GoString) (Wn : List GoString) (hok : AreaOk N h cl Wn) (hN : ∀ b, N'.Mem b ↔ N.Mem b)
    (htN : ¬ walNameOk tmp)
    (hcur : ∀ b, b ≠ tmp → ¬ walNameOk b → h'.cur !! b = h.cur !! b) :
    osNames (L := hG.goose_localGS) jr N' (DFrac.own (1 : Qp).half) h' ∗ walSplitFrag (W := W) Wn ∗
      tmpSub (h'.cur !! tmp) ∗ osClaims hG.goose_localGS
        ((cl.filter (fun c => decide (c.1 ≠ tmp))).map (fun c => (c.2, DFrac.own 1))) ⊢
      walAreaRes (L := hG.goose_localGS) jr := by
  iintro ⟨Hn, Hs, Ht, Hc⟩
  rcases he : h'.cur !! tmp with _ | ⟨i | J⟩
  · have hok' := areaOk_give N N' h h' cl tmp [] Wn hok hN htN hcur
      ⟨by rw [he]; exact subCover_none _, by rw [he]; exact .inl rfl⟩
    rw [List.map_nil, List.append_nil] at hok'
    obtain ⟨a1, a2, a3, a4⟩ := hok'
    unfold walAreaRes
    iexists N', h', cl.filter (fun c => decide (c.1 ≠ tmp)), Wn
    iframe Hn Hs Hc
    ipureintro; exact ⟨a1, a2, a3, a4⟩
  · iunfold tmpSub at Ht; icases Ht with %hf; exact hf.elim
  · iunfold tmpSub at Ht
    icases Ht with ⟨%hJ, %hf, HJ⟩
    have hok' := areaOk_give N N' h h' cl tmp [(J, NameSet.except [], hJ)] Wn hok hN htN hcur
      ⟨by rw [he]; exact subCover_single J hJ hf,
       by rw [he]; exact .inr ⟨J, rfl, fun hJ' hm => by
         simp only [List.mem_singleton, Prod.mk.injEq] at hm; obtain ⟨-, -, rfl⟩ := hm; exact hf⟩⟩
    obtain ⟨a1, a2, a3, a4⟩ := hok'
    ihave Hc' : osClaims hG.goose_localGS ((cl.filter (fun c => decide (c.1 ≠ tmp)) ++
        ([(J, NameSet.except [], hJ)] : List Claim).map (fun c => (tmp, c))).map
          (fun c => (c.2, DFrac.own 1))) $$ [Hc HJ]
    · rw [List.map_append]
      iapply (osClaims_app _ _).2
      iframe Hc
      simp only [List.map_cons, List.map_nil]
      iapply (osClaims_cons _ _ _).2
      iframe HJ
      iapply osClaims_nil'
    unfold walAreaRes
    iexists N', h', cl.filter (fun c => decide (c.1 ≠ tmp)) ++
      ([(J, NameSet.except [], hJ)] : List Claim).map (fun c => (tmp, c)), Wn
    iframe Hn Hs Hc'
    ipureintro; exact ⟨a1, a2, a3, a4⟩

/-- `walAreaRes` unpacked. -/
theorem walAreaRes_open (jr : Ino) :
    walAreaRes (L := hG.goose_localGS) jr ⊢ ∃ (N : NameSet) (h : NamesH) (cl : List (GoString × Claim))
      (Wn : List GoString),
      osNames (L := hG.goose_localGS) jr N (DFrac.own (1 : Qp).half) h ∗ walSplitFrag (W := W) Wn ∗
      ⌜AreaOk N h cl Wn⌝ ∗ osClaims hG.goose_localGS (cl.map (fun c => (c.2, DFrac.own 1))) := by
  unfold walAreaRes
  iintro ⟨%N, %h, %cl, %Wn, Hn, Hs, %a1, %a2, Hc, %a3, %a4⟩
  iexists N, h, cl, Wn
  iframe
  ipureintro; exact ⟨a1, a2, a3, a4⟩

end iris

end WalFs
end EtcdGrove
end Perennial

end
