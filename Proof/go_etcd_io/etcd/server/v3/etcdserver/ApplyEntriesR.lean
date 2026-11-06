/-
**`applyEntries`' restart form** (R2d' probe, A5, 2026-11-06; DRAFT: nothing here is frozen,
`notes/restart-plan.md`, "R2d' Scope (approved 2026-11-06)", its probe). Lean-first (no Rocq
counterpart). `applyEntries.specBatchROff`: `applyEntries.specOff` over the restart point `rp` and
Go's log `A`, the ghost rows at `ghostOf rp A`; its proof `wp_proofBatchROff`, `wp_proofOff`'s over
`apply.specROff` (`ApplyR.lean`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyR
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applyEntries

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.cindex
  go_etcd_io.etcd.server.v3.storage go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.applyEntries(ep, ap)` at a restart point** (R2d' probe, A5, DRAFT; auth off,
`applyEntries.specOff`'s window form): `apply.specROff` after `applyEntries`' cut of the batch at
Go's index `ai` (`server.go:1215-1239` at the pin `673da07c8`). Go's rows (`ep.appliedi`,
`ep.appliedt`, `loopOk`) at Go's log `A`; the ghost rows at `ghostOf rp A`, the applied index `g`. -/
abbrev EtcdServer.applyEntries.specBatchROff : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (ρ : ReqNames)
    (b : GoInterface) (ep ap : Loc) (es : GoSlice) (ents : List Loc) (ms : List EntryModel) (f0 : w64)
    (rac : GoChan) (st : ApplyState) (ai at0 a t : w64) (cs : Loc)
    (x : apply.ApplyKV) (γr : ReadNames) (rp : RestartPt) (A : List EntryModel) (γp : WTNames)
    (dv : Option Loc) (w : Nat) (g : w64),
  (ms = [] ∨ (entriesFrom f0 ms ∧ uint.Z f0 ≤ uint.Z ai + 1)) → uint.Z ai + 1 < 2 ^ 64 →
  loopOk γ st ai → logShape E.lm (unapplied ai ms) →
  dvOk ρ.raft γr.kv.c0 dv (ciEff γ st.k) (g + 1) (unapplied ai ms) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ci TM E ρ γr ∗
      batchWaitOk ρ E ms ∗ taEntriesAddr ap ↦□ es ∗ taRaftAdvancedCAddr ap ↦□ rac ∗
      es ↦*□ ents ∗ entriesAt ents ms ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at0 ∗ epConfState ep cs ∗
      epCsAt ρ.raft (ghostOf rp A) cs ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvGoRes s ∗
      srvApplyKV s E ρ.wait x ∗ srvAppliedOwn γr g ∗ appliedLogAt γr g x.log ∗
      batchCommittedIdx γr ms ∗ srvWTPool E γp ∗ srvWTTaken γp.cnt w ∗ srvFS s ∗
      kvApplied γr.raft γr.kv (ghostOf rp A) x ∗ srvRestR E γr rp A ∗
      kvBatchR γr (ciEff γ st.k) ai rp A (unapplied ai ms) ∗
      ⌜uint.Z g = uint.Z γr.raft.ai0 + (ghostOf rp A).length⌝ ∗
      dvView ρ.raft dv (ghostOf rp A) ∗ dvRes s ρ.raft dv (A ++ unapplied ai ms) ∗ srvRunH ρ.raft dv ∗
      srvApRes s γr (ghostOf rp A) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyEntries"))
      (Val #ep)) (Val #ap))
  {{ RET #(); srvFS s ∗ dvView ρ.raft dv (ghostOf rp (A ++ unapplied ai ms)) ∗ srvRunH ρ.raft dv ∗
      srvApRes s γr (ghostOf rp (A ++ unapplied ai ms)) ∗
      ∃ (st' : ApplyState) (ai' at' a' t' : w64) (cs' : Loc) (g' : w64),
        epAppliedIAddr ep ↦ ai' ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs' ∗
        epCsAt ρ.raft (ghostOf rp (A ++ unapplied ai ms)) cs' ∗
        applyThread γ st' ∗ applyBackend γ ci b ∗ ciApplying ci a' t' ∗ srvLgReader s ∗ srvGoRes s ∗
        srvAppliedOwn γr g' ∗ srvWTTaken γp.cnt (w + (unapplied ai ms).length) ∗
        (∃ x' : apply.ApplyKV, srvApplyKV s E ρ.wait x' ∗
          ⌜entriesStep (ciEff γ st.k) (unapplied ai ms) x x'⌝ ∗ appliedLogAt γr g' x'.log ∗
          kvApplied γr.raft γr.kv (ghostOf rp (A ++ unapplied ai ms)) x' ∗
          srvRestR E γr rp (A ++ unapplied ai ms)) ∗
        ⌜uint.Z g' = uint.Z γr.raft.ai0 + (ghostOf rp (A ++ unapplied ai ms)).length ∧
          loopOk γ st' ai' ∧
          uint.Z ai' = max (uint.Z ai) (((ms.getLast?).map (fun m => uint.Z m.index)).getD 0) ∧
          uint.Z ai' = uint.Z ai + (unapplied ai ms).length ∧
          ((unapplied ai ms = [] ∧ ciEff γ st'.k = ciEff γ st.k) ∨
            uint.Z (ciEff γ st'.k) = max (uint.Z (ciEff γ st.k)) (uint.Z ai')) ∧
          termAfter at0 (unapplied ai ms) at'⌝ }}

/-- **`applyEntries.specBatchROff`** (R2d' probe, DRAFT): over `apply.specROff`. -/
theorem EtcdServer.applyEntries.wp_proofBatchROff
    (hGI : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG))
    (hApply : EtcdServer.apply.specROff (GF := GF) (hG := hG)) :
    EtcdServer.applyEntries.specBatchROff (GF := GF) (hG := hG) := by
  have hGI := wp_entryAt_GetIndex hGI
  intro s γ ci TM E ρ b ep ap es ents ms f0 rac st ai at0 a t cs x γr rp A γp dv w g Hms Hai1 Hok hEok hdv
  unfold EtcdServer.apply.specROff at hApply
  wp_start as ⟨#Hsrv, #Hbw, #Hes, #Hrac, #Hesl, #Hentsat, Hai, Hat, Hcs, #Hcv, Hst, Hbe, Happ, Hlr, Hgr, HKV, Hao, #Hlog, #Hbc, #HW, #HWA, Hfs, Hka, HRS, #Hkb, %Hg0, Hdv, #Hdvr, Hrun, HAR⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hesl
  iunfold entriesAt at Hentsat
  icases Hentsat with ⟨%Hlen2, #Hent⟩
  ihave #Hrpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  wp_auto
  wp_if_destruct
  · -- no entries: nothing changes
    have hms : ms = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [← Hlen2, Hlen.1]; rw [Hif]; rfl
    subst hms
    ihave #Hcv2 : epCsAt ρ.raft (ghostOf rp (A ++ unapplied ai [])) cs $$ []
    · rw [show A ++ unapplied ai [] = A by simp [unapplied]]; iexact Hcv
    iapply HΦ
    iframe Hfs
    isplitl [Hdv]
    · rw [show A ++ unapplied ai [] = A by simp [unapplied]]; iexact Hdv
    isplitl [Hrun]
    · iexact Hrun
    isplitl [HAR]
    · rw [show A ++ unapplied ai [] = A by simp [unapplied]]; iexact HAR
    iexists st, ai, at0, a, t, cs, g
    iframe
    iframe Hcv2
    isplitr
    · rw [show (unapplied ai []).length = 0 by simp [unapplied], Nat.add_zero]; iexact HWA
    isplitl [Hka HRS]
    · isplitr
      · ipureintro; rfl
      iframe Hlog
      rw [show A ++ unapplied ai [] = A by simp [unapplied]]; iframe Hka HRS
    ipureintro
    refine ⟨by rw [show A ++ unapplied ai [] = A by simp [unapplied]]; exact Hg0, Hok, ?_, by simp [unapplied], Or.inl ⟨by simp [unapplied], rfl⟩, Or.inl ⟨by simp [unapplied], rfl⟩⟩
    simp only [List.getLast?_nil, Option.map_none, Option.getD_none]
    have : (0 : Int) ≤ uint.Z ai := by word
    omega
  rcases Hms with hnil | ⟨Hfrom, Hle⟩
  · exfalso; subst hnil; simp only [List.length_nil] at Hlen2
    rw [Hlen2] at Hlen; apply Hif; word
  have hlenpos : 0 < sint.Z es.len := by
    rcases Hlen with ⟨h1, h2⟩
    rcases Int.lt_or_eq_of_le h2 with h | h
    · exact h
    · exfalso; apply Hif; word
  have hlen0 : 0 < ents.length := by
    rw [Hlen.1]; word
  list_elem ents 0 as e0
  list_elem ms 0 as m0
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by
    have : sint.Z (W64 0) = 0 := by decide
    omega⟩)]
  wp_apply wp_load_slice_index es (sint.Z (W64 0)) ents DFrac.discard e0 (by decide) $$ [] as -
  · iframe Hesl; ipureintro; exact He0_lookup
  ihave He0 := Hent $$ %0 %e0 %m0 %He0_lookup %Hm0_lookup
  wp_apply hGI e0 m0 $$ [$He0]
  have hm0 : uint.Z m0.index = uint.Z f0 := by
    have := (Hfrom.2.2 0 m0 Hm0_lookup).1; simpa using this
  (try wp_auto)
  wp_if_destruct
  · -- `firsti > ep.appliedi + 1`: raft hands over no gap
    exfalso
    have h1 : uint.Z (ai + 1) = uint.Z ai + 1 := by word
    word
  -- the entries from `ai + 1` on: offset `off`
  have hoff : uint.Z (ai + W64 1 - m0.index) = uint.Z ai + 1 - uint.Z f0 := by word
  have hlenu : uint.Z es.len = ents.length := by
    have h1 := Hlen.1; have h2 := Hlen.2; rw [h1]; word
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hesl
  wp_if_destruct
  · -- `off < len(entries)`: `ents = entries[off:]`
    generalize hoffdef : ai + W64 1 - m0.index = off at hoff Hif ⊢
    have hoffl : uint.Z off < uint.Z es.len := Hif
    have hsoff : sint.Z off = uint.Z off := by word
    have hslen : sint.Z es.len = uint.Z es.len := by word
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega, Hwf.2⟩)]
    ihave Hsub := (ownSlice_slice off es.len es DFrac.discard ents ⟨by omega, by omega, Int.le_refl _⟩).1 $$ Hesl
    icases Hsub with ⟨-, #Hsub, -⟩
    obtain ⟨k, hkdef⟩ : ∃ k, k = (uint.Z off).toNat := ⟨_, rfl⟩
    have hk : k < ents.length := by omega
    have hsubl : subslice (sint.nat off) (sint.nat es.len) ents = ents.drop k := by
      unfold subslice
      have : sint.nat off = k := by simp only [sint.nat, hsoff, hkdef]
      rw [this, List.take_of_length_le]; rw [Hlen.1]; exact Nat.le_refl _
    rw [hsubl] at *
    wp_auto
    wp_if_destruct
    · exfalso; apply absurd Hif; intro h; have : uint.Z (es.len - off) = 0 := by rw [h]; rfl
      have : uint.Z (es.len - off) = uint.Z es.len - uint.Z off := by word
      omega
    have hf' : uint.Z (ai + 1) = uint.Z f0 + k := by
      have : uint.Z (ai + 1) = uint.Z ai + 1 := by word
      rw [hkdef, this]; have := hoff; omega
    have hkms : k < ms.length := by omega
    have hfrom' := entriesFrom_drop f0 (ai + 1) ms k Hfrom hkms hf'
    have hne' : ms.drop k ≠ [] := by
      intro h; have := congrArg List.length h; simp only [List.length_drop, List.length_nil] at this; omega
    have hok' : loopOk γ st (ai + 1 - 1) := by
      rw [show ai + 1 - 1 = ai by word]; exact Hok
    ihave #Hentsd := entriesAt_drop ents ms k $$ [Hent]
    · iunfold entriesAt; isplitr
      · ipureintro; exact Hlen2
      iexact Hent
    have hun : unapplied ai ms = ms.drop k := by
      rw [unapplied_eq_drop ai ms (uint.Z f0) (fun n m h => (Hfrom.2.2 n m h).1), hkdef, hoff]
    rw [hun] at hEok hdv
    ihave #Hdvr2 : iprop(dvRes s ρ.raft dv (A ++ ms.drop k)) $$ []
    · rw [← hun]; iexact Hdvr
    ihave #Hkb' : iprop(kvBatchR γr (ciEff γ st.k) ai rp A (ms.drop k)) $$ []
    · rw [← hun]; iexact Hkb
    ihave #Hbw' : iprop(batchWaitOk ρ E (ms.drop k)) $$ []
    · iunfold batchWaitOk at Hbw
      iunfold batchWaitOk
      imodintro
      iintro %m %hm
      iapply Hbw
      ipureintro; exact List.mem_of_mem_drop hm
    ihave #Hbc' : iprop(batchCommittedIdx γr (ms.drop k)) $$ []
    · iunfold batchCommittedIdx at Hbc
      iunfold batchCommittedIdx
      imodintro
      iintro %m %hm
      iapply Hbc
      ipureintro; exact List.mem_of_mem_drop hm
    wp_apply hApply s γ ci TM E ρ b (slice.slice es Loc off es.len) (ents.drop k) (ms.drop k)
      (ai + 1) ep cs rac st a t x γr rp A γp dv w g hne' hfrom' hok' hEok hdv
      $$ [Hst Hbe Happ Hcs Hcv Hlr Hgr HKV Hao Hfs Hka HRS Hdv Hrun HAR]
      as %appt %appi %stop ⟨Hfs, Hdv, Hrun, HAR, %st', %a', %at', %csl, %g', Hst, Hbe, Happ, Hcs, #Hcv', Hlr, Hgr, Hao, #HWA',
        ⟨%x', HKV, %Hx', #Hlog', Hka, HRS⟩, %Hpost⟩
    · rw [show ai + 1 - 1 = ai by word]
      iframe Hsrv Hbw' Hsub Hentsd Hst Hbe Happ Hcs Hcv Hlr Hgr HKV Hao HW HWA Hfs Hbc' Hlog Hka HRS Hkb'
        Hdv Hdvr2 Hrun HAR
      ipureintro; exact Hg0
    obtain ⟨hg', hli, hlt, hok2, hci2, hstop⟩ := Hpost
    -- `apply` never asks to stop (D19m: no member removed), so `stopWithDelay` is not reached
    subst hstop
    have hlast : ms.getLast? = (ms.drop k).getLast? := by
      rw [List.getLast?_drop]; simp only [ite_eq_right (show ¬ ms.length ≤ k by omega)]
    obtain ⟨mL, hmL, hmLi⟩ := entriesFrom_last f0 ms Hfrom (by
      intro h; subst h; simp only [List.length_nil] at Hlen2; omega)
    have happi : appi = mL.index := by
      rw [← hlast, hmL] at hli; simp only [Option.map_some, Option.some.injEq] at hli; exact hli.symm
    have hfin : uint.Z appi = max (uint.Z ai)
        (((ms.getLast?).map (fun m => uint.Z m.index)).getD 0) := by
      rw [hmL]; simp only [Option.map_some, Option.getD_some]; rw [happi]
      have : uint.Z f0 + k ≤ uint.Z f0 + ms.length - 1 := by omega
      omega
    wp_auto
    ihave #Hcv2 : epCsAt ρ.raft (ghostOf rp (A ++ unapplied ai ms)) csl $$ []
    · rw [hun]; iexact Hcv'
    iapply HΦ
    iframe Hfs
    isplitl [Hdv]
    · rw [hun]; iexact Hdv
    isplitl [Hrun]
    · iexact Hrun
    isplitl [HAR]
    · rw [hun]; iexact HAR
    iexists st', appi, appt, a', at', csl, g'
    iframe
    iframe Hcv2
    isplitr
    · rw [hun]; iexact HWA'
    isplitl [Hka HRS]
    · isplitr
      · ipureintro; rw [hun]; exact Hx'
      iframe Hlog'
      rw [hun]; iframe Hka HRS
    ipureintro
    refine ⟨by rw [hun]; exact hg', hok2, hfin, ?_, Or.inr hci2, Or.inr (by rw [hun]; exact hlt)⟩
    rw [hun, List.length_drop, happi, hmLi]
    have : uint.Z (ai + 1) = uint.Z ai + 1 := by word
    omega
  · -- `off ≥ len(entries)`: every entry is already applied
    (try wp_auto)
    obtain ⟨mL, hmL, hmLi⟩ := entriesFrom_last f0 ms Hfrom (by
      intro h; subst h; simp only [List.length_nil] at Hlen2; omega)
    have hun : unapplied ai ms = [] := by
      rw [unapplied_eq_drop ai ms (uint.Z f0) (fun n m h => (Hfrom.2.2 n m h).1)]
      apply List.drop_of_length_le
      have : ¬ uint.Z ai + 1 - uint.Z f0 < ents.length := by rw [← hoff, ← hlenu]; exact Hif
      omega
    ihave #Hcv2 : epCsAt ρ.raft (ghostOf rp (A ++ unapplied ai ms)) cs $$ []
    · rw [hun, List.append_nil]; iexact Hcv
    iapply HΦ
    iframe Hfs
    isplitl [Hdv]
    · rw [hun, List.append_nil]; iexact Hdv
    isplitl [Hrun]
    · iexact Hrun
    isplitl [HAR]
    · rw [hun, List.append_nil]; iexact HAR
    iexists st, ai, at0, a, t, cs, g
    iframe
    iframe Hcv2
    isplitr
    · rw [hun, List.length_nil, Nat.add_zero]; iexact HWA
    isplitl [Hka HRS]
    · isplitr
      · ipureintro; rw [hun]; rfl
      iframe Hlog
      rw [hun, List.append_nil]; iframe Hka HRS
    ipureintro
    refine ⟨by rw [hun, List.append_nil]; exact Hg0, Hok, ?_, by rw [hun]; simp, Or.inl ⟨hun, rfl⟩, Or.inl ⟨hun, rfl⟩⟩
    rw [hmL]
    simp only [Option.map_some, Option.getD_some]
    have : ¬ uint.Z ai + 1 - uint.Z f0 < ents.length := by rw [← hoff, ← hlenu]; exact Hif
    omega



end proof

end EtcdGrove
end Perennial
