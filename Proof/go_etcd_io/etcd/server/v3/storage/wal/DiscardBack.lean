/- Lean-first (no Rocq counterpart).

# `Discard`'s area back (P6b state C, mit-pdos/etcd-grove#50; `notes/wal-p6-handoff.md`, session 22)

After S (`walInv_discardS`) the program holds the discarded WAL's directory `J` claimed whole but for its
pipeline names (`.except walTmps`, its entries files: `FilesOnly`) and both pipeline names' claims
(`walTmpsRes`, `walTmpsHalf`); `walTmps_whole` makes them one whole claim `(J, .except [], h')`, of files
only. `walInv_discardBack` then merges the program's half of the discard claim `(jr, .only [nm, tmp], hC)`
(`tmp = tmpName nm` holding `J`) back into the area claim (`walInv_merge2`) and rebuilds `walAreaRes`
(`area_giveD`) with `J`'s claim tagged `tmp` (`SubCover`, `ClRanked`: one claim of files only).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.DiscardS
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateArea

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

/-- The names of `N` and of `M`. -/
def nameAddL (N : NameSet) (M : List GoString) : NameSet :=
  match N with
  | .only bs => .only (bs ++ M)
  | .except bs => .except (bs.filter (fun b => decide (b ∉ M)))

theorem nameAddL_mem (N : NameSet) (M : List GoString) (b : GoString) :
    (nameAddL N M).Mem b ↔ N.Mem b ∨ b ∈ M := by
  cases N with
  | only bs => simp [nameAddL, NameSet.Mem]
  | except bs =>
    simp only [nameAddL, NameSet.Mem, List.mem_filter, decide_eq_true_eq, not_and, Decidable.not_not]
    by_cases h : b ∈ M <;> simp [h]

section pure

/-- **`AreaOk` rebuilt over more names** (`N'`: `N`'s and WAL names), fewer split names (`Wn'`: each of
`Wn` in `N'` or `Wn'`), with the temporary directory's new contents `ct` (`areaOk_give`, generalized). -/
theorem areaOk_giveD (N N' : NameSet) (h h' : NamesH) (cl : List (GoString × Claim))
    (tmp : GoString) (ct : List Claim) (Wn Wn' : List GoString) (hok : AreaOk N h cl Wn)
    (hN : ∀ b, N.Mem b → N'.Mem b) (hN' : ∀ b, N'.Mem b → ¬ walNameOk b → N.Mem b)
    (hWn : ∀ b, b ∈ Wn → N'.Mem b ∨ b ∈ Wn')
    (hcur : ∀ b, b ≠ tmp → ¬ walNameOk b → ¬ BrokenSlot b → N.Mem b → h'.cur !! b = h.cur !! b)
    (hct : SubCover ct (h'.cur !! tmp) ∧ ClRanked ct) :
    AreaOk N' h' (cl.filter (fun c => decide (c.1 ≠ tmp)) ++ ct.map (fun c => (tmp, c))) Wn' := by
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
  refine ⟨fun nm hn => (h1 nm hn).elim (fun h => Or.inl (hN _ h)) (fun h => hWn _ h),
    fun nm sfx hn => hN _ (h2 nm sfx hn), ?_, ?_⟩
  · intro b hb hbn hbb
    by_cases hbt : b = tmp
    · subst hbt; rw [hclt]; exact hct.1
    · have hb0 := hN' b hb hbn
      rw [hcl b hbt, hcur b hbt hbn hbb hb0]; exact h3 b hb0 hbn hbb
  · intro nm hn
    by_cases hbt : tmpName nm = tmp
    · rw [hbt, hclt]; exact hct.2
    · rw [hcl _ hbt]; exact h4 nm hn

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- What a pipeline name holds is no directory. -/
theorem tmpEnt_notDir (o : Option Node) :
    tmpEnt (hG := ⟨G, L⟩) o ⊢ ⌜∀ K, o ≠ some (.dir K)⌝ := by
  rcases o with _ | ⟨i | K⟩
  · iintro -; ipureintro; intro K h; cases h
  · iintro -; ipureintro; intro K h; cases h
  · have hF : tmpEnt (hG := ⟨G, L⟩) (some (Node.dir K)) ⊢ (iprop(False) : IProp GF) := .rfl
    iintro H
    iexfalso
    iapply hF
    iexact H

/-- Both pipeline names' halves joined: each name's claim whole, with what it holds. -/
theorem walTmps_join2 (J : Ino) :
    walTmpsRes (hG := ⟨G, L⟩) J ∗ walTmpsHalf (hG := ⟨G, L⟩) J ⊢
      ∃ h0 h1 : NamesH, osNames (L := L) J (.only [go!"0.tmp"]) (DFrac.own 1) h0 ∗
        tmpEnt (hG := ⟨G, L⟩) (h0.cur !! go!"0.tmp") ∗
        osNames (L := L) J (.only [go!"1.tmp"]) (DFrac.own 1) h1 ∗
        tmpEnt (hG := ⟨G, L⟩) (h1.cur !! go!"1.tmp") := by
  unfold walTmpsRes walTmpsHalf walTmps
  iintro ⟨Hr, Hh⟩
  icases BigSepL.bigSepL_cons.1 $$ Hr with ⟨Hr0, Hr⟩
  icases BigSepL.bigSepL_cons.1 $$ Hr with ⟨Hr1, -⟩
  icases BigSepL.bigSepL_cons.1 $$ Hh with ⟨Hh0, Hh⟩
  icases BigSepL.bigSepL_cons.1 $$ Hh with ⟨Hh1, -⟩
  icases tmpClaim_join (hG := ⟨G, L⟩) J go!"0.tmp" $$ [Hr0 Hh0] with ⟨%h0, Hn0, He0⟩
  · iframe Hr0 Hh0
  icases tmpClaim_join (hG := ⟨G, L⟩) J go!"1.tmp" $$ [Hr1 Hh1] with ⟨%h1, Hn1, He1⟩
  · iframe Hr1 Hh1
  iexists h0, h1
  iframe

/-- **A WAL directory's claims made whole** (S's post): its claim less the pipeline names, of files,
and both pipeline names' halves give the whole claim on all its names, of files only. -/
theorem walTmps_whole (R : Roots) (J : Ino) (hj : NamesH) (hf : FilesOnly hj.cur) :
    ⊢ osSharedInv (L := L) R -∗ osNames (L := L) J (.except walTmps) (DFrac.own 1) hj -∗
      walTmpsRes (hG := ⟨G, L⟩) J -∗ walTmpsHalf (hG := ⟨G, L⟩) J ={⊤}=∗
      ∃ h' : NamesH, osNames (L := L) J (.except []) (DFrac.own 1) h' ∗ ⌜FilesOnly h'.cur⌝ := by
  iintro #Hsi Hj Hr Hh
  icases walTmps_join2 J $$ [Hr Hh] with ⟨%h0, %h1, Hn0, He0, Hn1, He1⟩
  · iframe Hr Hh
  icases tmpEnt_notDir _ $$ He0 with %hd0
  icases tmpEnt_notDir _ $$ He1 with %hd1
  imod osNames_merge R J (.only [go!"0.tmp"]) (.only [go!"1.tmp"]) (.only walTmps) h0 h1
    (fun b => by simp [NameSet.Mem, walTmps]) CoPset.subseteq_top
    $$ Hsi Hn0 Hn1 with ⟨%ht, Hnt, %hrt⟩
  imod osNames_merge R J (.except walTmps) (.only walTmps) (.except []) hj ht
    (fun b => by by_cases hb : b ∈ walTmps <;> simp [NameSet.Mem, hb])
    CoPset.subseteq_top
    $$ Hsi Hj Hnt with ⟨%h', Hn, %hr⟩
  imodintro
  iexists h'
  iframe Hn
  ipureintro
  intro x n hx
  by_cases hm : x ∈ walTmps
  · rw [cur_of_part hr.2.1 (by simp [NameSet.Mem, hm])] at hx
    simp only [walTmps, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · rw [cur_of_part hrt.1 (by simp [NameSet.Mem])] at hx
      cases n with
      | file i => exact ⟨i, rfl⟩
      | dir K => exact absurd hx (hd0 K)
    · rw [cur_of_part hrt.2.1 (by simp [NameSet.Mem])] at hx
      cases n with
      | file i => exact ⟨i, rfl⟩
      | dir K => exact absurd hx (hd1 K)
  · rw [cur_of_part hr.1 (by simp [NameSet.Mem, hm])] at hx
    exact hf x n hx

/-- **`walAreaRes` rebuilt over more names and fewer split ones** (`area_give`, generalized:
`areaOk_giveD`). -/
theorem area_giveD (N N' : NameSet) (h h' : NamesH) (cl : List (GoString × Claim)) (jr : Ino)
    (tmp : GoString) (Wn Wn' : List GoString) (hok : AreaOk N h cl Wn)
    (hN : ∀ b, N.Mem b → N'.Mem b) (hN' : ∀ b, N'.Mem b → ¬ walNameOk b → N.Mem b)
    (hWn : ∀ b, b ∈ Wn → N'.Mem b ∨ b ∈ Wn')
    (hcur : ∀ b, b ≠ tmp → ¬ walNameOk b → ¬ BrokenSlot b → N.Mem b → h'.cur !! b = h.cur !! b) :
    osNames (L := L) jr N' (DFrac.own (1 : Qp).half) h' ∗ walSplitFrag (W := W) Wn' ∗
      tmpCls (hG := ⟨G, L⟩) (h'.cur !! tmp) ∗
      areaCls (L := L) (cl.filter (fun c => decide (c.1 ≠ tmp))) ⊢
      walAreaRes (L := L) (W := W) jr := by
  iintro ⟨Hn, Hs, Ht, Hc⟩
  iunfold areaCls at Hc
  iunfold tmpCls at Ht
  icases Ht with ⟨%ct, Hct, %hct⟩
  obtain ⟨a1, a2, a3, a4⟩ := areaOk_giveD N N' h h' cl tmp ct Wn Wn' hok hN hN' hWn hcur hct
  have hm : ((cl.filter (fun c => decide (c.1 ≠ tmp)) ++ ct.map (fun c => (tmp, c))).map
      (fun c => (c.2, DFrac.own 1))) = (cl.filter (fun c => decide (c.1 ≠ tmp))).map
        (fun c => (c.2, DFrac.own 1)) ++ ct.map (fun c => (c, DFrac.own 1)) := by
    simp [List.map_append, List.map_map, Function.comp_def]
  ihave Hac : areaCls (L := L) (cl.filter (fun c => decide (c.1 ≠ tmp)) ++
      ct.map (fun c => (tmp, c))) $$ [Hc Hct]
  · unfold areaCls
    rw [hm]
    iapply (osClaims_app (hG := ⟨G, L⟩) _ _).2
    iframe Hc
    iapply (osClaimsW_eq (hG := ⟨G, L⟩) ct).1
    iexact Hct
  unfold walAreaRes
  iexists N', h', cl.filter (fun c => decide (c.1 ≠ tmp)) ++ ct.map (fun c => (tmp, c)), Wn'
  iframe Hn Hs Hac
  ipureintro; exact ⟨a1, a2, a3, a4⟩

/-- **The area back after S** (see the file header): the program's half of the area claim less `tmp`
(`walInv_drop`'s, `N0.diff [tmp]`) and of the discard claim `(jr, .only [nm, tmp], hC)`, `tmp` holding
the discarded WAL's directory `J`, merged (`walInv_merge2`, by a fresh WAL name `b` of the area claim);
`J`'s claims made whole (`walTmps_whole`) and tagged `tmp`; `walAreaRes` over `N0` and `nm`, the split
names less `nm`. -/
theorem walInv_discardBack (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (N0 : NameSet) (h0 : NamesH) (cl : List (GoString × Claim)) (Wn : List GoString) (nm b : GoString)
    (hC hj : NamesH) (J : Ino)
    (hok : AreaOk N0 h0 cl Wn) (hnm : walNameOk nm) (hnmW : nm ∈ Wn) (hb : walNameOk b)
    (hbW : b ∉ Wn) (hbN : N0.Mem b)
    (hJ : hC.cur !! tmpName nm = some (.dir J)) (hf : FilesOnly hj.cur) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ osSharedInv (L := L) R -∗
      notCrashed (hC := L.goose_crashGS) -∗ walUnlockedTok (W := W) -∗
      walSplitFrag (W := W) (Wn.erase nm) -∗
      osNames (L := L) jr (N0.diff [tmpName nm]) (DFrac.own (1 : Qp).half)
        (h0.restrict jr (N0.diff [tmpName nm])) -∗
      osNames (L := L) jr (.only [nm, tmpName nm]) (DFrac.own (1 : Qp).half) hC -∗
      osNames (L := L) J (.except walTmps) (DFrac.own 1) hj -∗
      walTmpsRes (hG := ⟨G, L⟩) J -∗ walTmpsHalf (hG := ⟨G, L⟩) J -∗
      areaCls (L := L) (cl.filter (fun c => decide (c.1 ≠ tmpName nm))) ={⊤}=∗
      notCrashed (hC := L.goose_crashGS) ∗ walUnlockedTok (W := W) ∗ walAreaRes (L := L) (W := W) jr := by
  classical
  iintro #Hinv #Hsi Hnc Hu Hs H1 H2 Hj Hr Hh Hc
  have htn : ¬ walNameOk (tmpName nm) := by intro hw; apply hw.2.2; simp [tmpName]
  have hbt : b ≠ tmpName nm := fun e => htn (e ▸ hb)
  have hbnm : b ≠ nm := fun e => hbW (e ▸ hnmW)
  have hbN1 : (N0.diff [tmpName nm]).Mem b := by
    cases N0 <;> simp_all [NameSet.diff, NameSet.Mem]
  have hN2 : (NameSet.only [nm, tmpName nm]).Mem nm := by simp [NameSet.Mem]
  -- `nm` is not in the area claim (the discard claim holds it)
  have hNN : N0.diff [tmpName nm] ≠ .only [nm, tmpName nm] := by
    intro e; rw [e] at hbN1; simp [NameSet.Mem, hbt, hbnm] at hbN1
  rcases Classical.em ((N0.diff [tmpName nm]).Mem nm) with hn | hb21
  · imod osNames_same_name R jr _ _ _ _ _ _ nm hn hN2 CoPset.subseteq_top $$ Hsi H1 H2 with ⟨%he, -⟩
    exact absurd he.1 hNN
  -- `J`'s claims whole
  imod walTmps_whole R J hj hf $$ Hsi Hj Hr Hh with ⟨%hJw, HJ, %hfw⟩
  -- the merge
  imod walInv_merge2 C Mr R jr r (N0.diff [tmpName nm]) (.only [nm, tmpName nm])
    (nameAddL N0 [nm]) _ hC b nm (walUnlockedTok (W := W)) walUnlockedTok_exclX ⊤ CoPset.subseteq_top
    walN_osShN_top hb hbN1 hnm hN2 hb21
    (fun x => by
      rw [nameAddL_mem]
      by_cases hx : x = tmpName nm
      · subst hx
        have := hok.2.1 nm go!"tmp" hnm
        cases N0 <;> simp_all [NameSet.diff, NameSet.Mem, tmpName]
      · by_cases hxn : x = nm
        · subst hxn; cases N0 <;> simp [NameSet.diff, NameSet.Mem]
        · cases N0 <;> simp [NameSet.diff, NameSet.Mem, hx, hxn])
    $$ Hinv Hsi Hnc Hu H1 H2 with ⟨Hnc, Hu, %h', Hn, %hp⟩
  obtain ⟨hp1, hp2, -⟩ := hp
  have hcurT : h'.cur !! tmpName nm = some (.dir J) := by
    rw [cur_of_part hp2 (by simp [NameSet.Mem])]; exact hJ
  imodintro
  iframe Hnc Hu
  iapply area_giveD N0 (nameAddL N0 [nm]) h0 h' cl jr (tmpName nm) Wn (Wn.erase nm) hok
    (fun x hx => (nameAddL_mem _ _ _).2 (Or.inl hx))
    (fun x hx hxw => by
      rcases (nameAddL_mem _ _ _).1 hx with h | h
      · exact h
      · simp at h; subst h; exact absurd hnm hxw)
    (fun x hx => by
      by_cases e : x = nm
      · subst e; exact Or.inl ((nameAddL_mem _ _ _).2 (Or.inr (List.mem_singleton_self _)))
      · exact Or.inr ((List.mem_erase_of_ne e).2 hx))
    (fun x hxt hxw _ hxN => by
      have hm : (N0.diff [tmpName nm]).Mem x := by
        cases N0 <;> simp_all [NameSet.diff, NameSet.Mem]
      rw [cur_of_part hp1 hm]
      simp only [NamesH.restrict]
      exact restrictN_lookup _ _ _ hm)
  iframe Hn Hs Hc
  rw [hcurT]
  unfold tmpCls
  iexists [(J, NameSet.except [], hJw)]
  isplitl [HJ]
  · unfold osClaimsW; iapply BigSepL.bigSepL_cons.2; iframe HJ; iapply BigSepL.bigSepL_nil.2; iempintro
  · ipureintro
    refine ⟨subCover_single J hJw hfw, ⟨fun _ => 0, fun c hc x K hx => ?_⟩⟩
    simp only [List.mem_singleton] at hc
    subst hc
    obtain ⟨i, hi⟩ := hfw x _ hx
    cases hi

end iris

end WalFs
end EtcdGrove
end Perennial

end
