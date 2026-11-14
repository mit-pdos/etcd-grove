/- Lean-first (no Rocq counterpart).

# `Create` before the rename: the fresh directory's claims (W4, `notes/wal-fsext-plan.md`, "W4
implementation log", eighteenth session)

* `createJ_claims`: `J`'s claim off the segment's name and the segment's create (`crOut`) merged back,
  then split into the claim off the pipeline's names (`.except walTmps`, for the commit, half to
  `walCreateP`, half to the handle) and the pipeline's names (`walTmpsRes J`, `renameWAL`'s pre), with
  the merged history's facts (`createJ_cur`; its entries below both parts' bounds, `ClaimCoh` of the
  merged claim).
* `osNames_disj`: two claims held on different keys of one directory share no name (the shared
  invariant's `NamesCoh.disj`); so `J ≠ jr` (`Create` holds `nm.tmp`'s claim of `jr` and `J`'s claim
  off the pipeline's names, which holds `nm.tmp`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateJ
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TmpClaim
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateSeg
public import GooseLang.Ext.Fs.TreeSharedRes
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateCoh

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Fs WalEnc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

theorem walTmps_ne_wal {b t : GoString} (hb : walNameP b = true) (ht : t ∈ walTmps) : t ≠ b := by
  rintro rfl; rw [walTmps_not_wal t ht] at hb; cases hb

/-- A logged create's outcome bounds the log below past its entry. -/
theorem crOut_logLb (J : Ino) (b : GoString) (h : NamesH) (dq : DFrac) (x s : Nat) (i : Ino) :
    crOut (GF := GF) J b h dq (some (x, s, i)) ⊢
      crOut (GF := GF) J b h dq (some (x, s, i)) ∗ osLogLb (x + 1) := by
  simp only [crOut]
  iintro ⟨%hp, Hl, Hn⟩
  unfold osLogged
  icases Hl with ⟨%hs, Hle, #Hlb⟩
  iframe Hn Hle Hlb
  ipureintro; exact ⟨hp, hs⟩

/-- **`J`'s claims after the segment's create** (see the file header). -/
theorem createJ_claims {E : CoPset} (R : Roots) (J : Ino) (w0 : GoString) (hJ : NamesH)
    (x s : Nat) (i : Ino) (hJe : hJ.cur = ∅)
    (hw0 : walNameP w0 = true) (hE : ↑osShN ⊆ E) :
    osSharedInv (GF := GF) R -∗
      osNames J ((NameSet.except []).diff [w0]) (DFrac.own 1) (hJ.restrict J ((NameSet.except []).diff [w0])) -∗
      crOut J w0 (hJ.restrict J ((NameSet.except []).inter [w0])) (DFrac.own 1) (some (x, s, i)) ={E}=∗
      ∃ hJ' : NamesH,
        osNames J ((NameSet.except []).diff walTmps) (DFrac.own 1)
          (hJ'.restrict J ((NameSet.except []).diff walTmps)) ∗ walTmpsRes J ∗
        ⌜(∀ xe ∈ (hJ'.restrict J ((NameSet.except []).diff walTmps)).ents,
            xe.1 < max (hJ.restrict J ((NameSet.except []).diff [w0])).next (x + 1)) ∧
          (∀ b, hJ'.cur !! b = if b = w0 then some (.file i) else none)⌝ := by
  iintro #Hsi HD Ho
  have hN : ∀ c, (NameSet.except []).Mem c ↔
      ((NameSet.except []).diff [w0]).Mem c ∨ (NameSet.only [w0]).Mem c := by
    intro c
    rw [NameSet.mem_diff]
    simp only [NameSet.Mem, List.mem_singleton, List.not_mem_nil, not_false_eq_true, _root_.true_and]
    by_cases hc : c = w0 <;> simp [hc]
  simp only [crOut]
  icases Ho with ⟨-, -, Hn1⟩
  imod osNames_merge R J _ _ (.except []) _ _ hN hE $$ Hsi HD Hn1 with ⟨%h'', Hn, %hr⟩
  imod osNames_coh R J _ _ _ hE $$ Hsi Hn with ⟨Hn, %hcoh⟩
  have hlt : ∀ xe ∈ (h''.restrict J ((NameSet.except []).diff walTmps)).ents,
      xe.1 < max (hJ.restrict J ((NameSet.except []).diff [w0])).next (x + 1) := by
    refine restrict_ents_lt (fun xe hxe => ?_)
    have e : ((hJ.restrict J ((NameSet.except []).inter [w0])).log x (crEnt J w0 i s)
        (<[w0 := .file i]> (hJ.restrict J ((NameSet.except []).inter [w0])).cur)).next = x + 1 := by
      simp [NamesH.next, NamesH.log]
    have h1 := hcoh.1 xe hxe
    rw [hr.2.2, e] at h1
    exact h1
  have hcur := createJ_cur (x := x) (s := s) hJe hr.1 hr.2.1
  imod osNames_split R J (.except []) walTmps h'' hE $$ Hsi Hn with ⟨HT, HD⟩
  -- the pipeline's names, one claim each
  imod osNames_split R J _ [go!"0.tmp"] _ hE $$ Hsi HT with ⟨H0, H1⟩
  have hS0 : (((NameSet.except []).inter walTmps).inter [go!"0.tmp"]).Same (.only [go!"0.tmp"]) :=
    fun b => by
      rw [NameSet.mem_inter, NameSet.mem_inter]
      show _ ↔ b ∈ [go!"0.tmp"]
      constructor
      · exact fun h => h.2
      · intro h
        rw [List.mem_singleton] at h; subst h
        exact ⟨⟨by simp [NameSet.Mem], by simp [walTmps]⟩, by simp⟩
  have hS1 : (((NameSet.except []).inter walTmps).diff [go!"0.tmp"]).Same (.only [go!"1.tmp"]) :=
    fun b => by
      rw [NameSet.mem_diff, NameSet.mem_inter]
      show _ ↔ b ∈ [go!"1.tmp"]
      constructor
      · rintro ⟨⟨-, hT⟩, h0⟩
        simp only [walTmps, List.mem_cons, List.not_mem_nil, _root_.or_false] at hT
        rcases hT with rfl | rfl
        · exact absurd (List.mem_singleton_self _) h0
        · exact List.mem_singleton_self _
      · intro h
        rw [List.mem_singleton] at h; subst h
        exact ⟨⟨by simp [NameSet.Mem], by simp [walTmps]⟩, by decide⟩
  imod osNames_rekey R J _ (.only [go!"0.tmp"]) _ hS0 hE $$ Hsi H0 with H0
  imod osNames_rekey R J _ (.only [go!"1.tmp"]) _ hS1 hE $$ Hsi H1 with H1
  have hc : ∀ t (M1 M2 : NameSet), t ∈ walTmps → M1.Mem t → M2.Mem t →
      ((h''.restrict J M1).restrict J M2).cur !! t = none := by
    intro t M1 M2 ht h1 h2
    simp only [NamesH.restrict]
    rw [restrictN_lookup _ _ _ h2, restrictN_lookup _ _ _ h1, hcur, if_neg (walTmps_ne_wal hw0 ht)]
  have h0m : (NameSet.except []).inter walTmps |>.Mem go!"0.tmp" :=
    (NameSet.mem_inter _ _ _).2 ⟨by simp [NameSet.Mem], by simp [walTmps]⟩
  have h1m : (NameSet.except []).inter walTmps |>.Mem go!"1.tmp" :=
    (NameSet.mem_inter _ _ _).2 ⟨by simp [NameSet.Mem], by simp [walTmps]⟩
  have hc0 := hc go!"0.tmp" _ (((NameSet.except []).inter walTmps).inter [go!"0.tmp"]) (by simp [walTmps]) h0m
    ((NameSet.mem_inter _ _ _).2 ⟨h0m, by simp⟩)
  have hc1 := hc go!"1.tmp" _ (((NameSet.except []).inter walTmps).diff [go!"0.tmp"]) (by simp [walTmps]) h1m
    ((NameSet.mem_diff _ _ _).2 ⟨h1m, by decide⟩)
  imodintro
  iexists h''
  iframe HD
  ihave Ht0 : tmpClaim J go!"0.tmp" $$ [H0]
  · unfold tmpClaim; iexists _; iframe H0; rw [hc0]; simp only [tmpEnt]; iempintro
  ihave Ht1 : tmpClaim J go!"1.tmp" $$ [H1]
  · unfold tmpClaim; iexists _; iframe H1; rw [hc1]; simp only [tmpEnt]; iempintro
  isplitl [Ht0 Ht1]
  · unfold walTmpsRes walTmps
    iframe Ht0 Ht1
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  ipureintro
  exact ⟨hlt, hcur⟩

/-- **Two claims held on different keys of a directory share no name.** -/
theorem osNames_disj {E : CoPset} (R : Roots) (j : Ino) (N N' : NameSet) (dq dq' : DFrac)
    (h h' : NamesH) (b : GoString) (hNN : N ≠ N') (hb : N.Mem b) (hb' : N'.Mem b)
    (hE : ↑osShN ⊆ E) :
    ⊢ osSharedInv (GF := GF) R -∗ osNames j N dq h -∗ osNames j N' dq' h' ={E}=∗ False := by
  have hN : N ≠ .only [] := by rintro rfl; simp [NameSet.Mem] at hb
  have hN' : N' ≠ .only [] := by rintro rfl; simp [NameSet.Mem] at hb'
  unfold osSharedInv
  iintro #Hsi H H'
  imod inv_acc hE $$ Hsi with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  icases Hi with ⟨%Vs, %Γn, Hs, HAn, %hcoh, Halen, HAlog⟩
  rw [osNames_of_ne dq h hN, osNames_of_ne dq' h' hN']
  icases gAuth_lookup _ _ _ _ _ _ $$ HAn H with %h1
  icases gAuth_lookup _ _ _ _ _ _ $$ HAn H' with %h2
  exact absurd hb' (hcoh.2.disj j N N' h h' b h1 h2 hNN hb)

/-- **`J` is not the area's directory**: `Create` holds a claim of `jr` on finitely many names, one of
them (`nm`) not a pipeline name, and a claim of `J` on every name but the pipeline's. -/
theorem create_J_ne {E : CoPset} (R : Roots) (jr J : Ino) (bs : List GoString) (b : GoString)
    (dq dq' : DFrac) (h h' : NamesH) (hb : b ∈ bs) (htt : b ∉ walTmps) (hE : ↑osShN ⊆ E) :
    ⊢ osSharedInv (GF := GF) R -∗ osNames jr (.only bs) dq h -∗
      osNames J (.except walTmps) dq' h' ={E}=∗
      ⌜J ≠ jr⌝ ∗ osNames jr (.only bs) dq h ∗
        osNames J (.except walTmps) dq' h' := by
  iintro #Hsi H H'
  by_cases hJ : J = jr
  · subst hJ
    have hne : NameSet.only bs ≠ .except walTmps := by simp
    imod osNames_disj R J _ _ dq dq' h h' b hne hb
      htt hE $$ Hsi H H' with Hf
    iexfalso; iexact Hf
  · imodintro
    iframe H H'
    ipureintro; exact hJ

/-- A WAL directory's name is no pipeline name (it has no `.`). -/
theorem walNameOk_not_tmps {nm : GoString} (h : walNameOk nm) : nm ∉ walTmps := by
  intro hm
  simp only [walTmps, List.mem_cons, List.not_mem_nil, _root_.or_false] at hm
  rcases hm with rfl | rfl <;> exact h.2.2 (by decide)

end proof

end WalFs
end EtcdGrove
end Perennial
