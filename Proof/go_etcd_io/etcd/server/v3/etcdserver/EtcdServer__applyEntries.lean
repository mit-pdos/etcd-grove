/-
Proof of `Spec/EtcdServer__applyEntries.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applyEntries
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__apply

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.cindex go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.server.v3.storage

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- A suffix of a batch of entries is a batch, from the shifted index. -/
theorem entriesFrom_drop (f0 f' : w64) (ms : List EntryModel) (k : Nat) (h : entriesFrom f0 ms)
    (hk : k < ms.length) (hf : uint.Z f' = uint.Z f0 + k) : entriesFrom f' (ms.drop k) := by
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨by omega, by simp only [List.length_drop]; omega, fun n m hn => ?_⟩
  rw [List.getElem?_drop] at hn
  obtain ⟨h3, h4⟩ := h2 (k + n) m hn
  exact ⟨by rw [h3, hf]; omega, h4⟩

/-- The last entry of a batch: index `f0 + |ms| - 1`. -/
theorem entriesFrom_last (f0 : w64) (ms : List EntryModel) (h : entriesFrom f0 ms)
    (hne : ms ≠ []) :
    ∃ m, ms.getLast? = some m ∧ uint.Z m.index = uint.Z f0 + ms.length - 1 := by
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (List.getLast?_isSome.mpr hne)
  refine ⟨m, hm, ?_⟩
  have hl : ms[ms.length - 1]? = some m := by
    rw [List.getLast?_eq_getElem?] at hm; exact hm
  have := (h.2.2 _ m hl).1
  have hpos : 0 < ms.length := List.length_pos_iff.mpr hne
  rw [this]; omega

end proof

section proof2
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- A suffix of entries is modelled by the suffix of the models. -/
theorem entriesAt_drop (ents : List Loc) (ms : List EntryModel) (k : Nat) :
    entriesAt (GF := GF) ents ms ⊢ entriesAt (ents.drop k) (ms.drop k) := by
  iunfold entriesAt
  iintro ⟨%Hl, #H⟩
  isplitr
  · ipureintro; simp [Hl]
  imodintro
  iintro %n %e %m %He %Hm
  rw [List.getElem?_drop] at He Hm
  iapply H $$ %(k + n) %e %m %He %Hm

theorem EtcdServer.applyEntries.wp_proof
    (hGI : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG))
    (hApply : EtcdServer.apply.spec (GF := GF) (hG := hG)) :
    EtcdServer.applyEntries.spec (GF := GF) (hG := hG) := by
  have hGI := wp_entryAt_GetIndex hGI
  intro s γ ci TM E ρ b ep ap es ents ms f0 rac st ai at0 a t cs x γr A γp dv w Hms Hai1 Hok hEok hdv
  wp_start as ⟨#Hsrv, #Hbw, #Hes, #Hrac, #Hesl, #Hentsat, Hai, Hat, Hcs, Hst, Hbe, Happ, Hlr, Hgr, HKV, Hao, #Hlog, #Hbc, #HW, #HWA, Hfs, Hka, HRS, #Hkb, Hdv, #Hdvr, HAR⟩
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
    iapply HΦ
    iframe Hfs
    isplitl [Hdv]
    · rw [show A ++ unapplied ai [] = A by simp [unapplied]]; iexact Hdv
    isplitl [HAR]
    · rw [show A ++ unapplied ai [] = A by simp [unapplied]]; iexact HAR
    iexists st, ai, at0, a, t, cs
    iframe
    isplitr
    · rw [show (unapplied ai []).length = 0 by simp [unapplied], Nat.add_zero]; iexact HWA
    isplitl [Hka HRS]
    · isplitr
      · ipureintro; rfl
      iframe Hlog
      rw [show A ++ unapplied ai [] = A by simp [unapplied]]; iframe Hka HRS
    ipureintro
    refine ⟨Hok, ?_, by simp [unapplied], Or.inl rfl, Or.inl ⟨by simp [unapplied], rfl⟩⟩
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
    ihave #Hkb' : iprop(kvBatch γr (ciEff γ st.k) ai A (ms.drop k)) $$ []
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
      (ai + 1) ep cs rac st a t x γr A γp dv w hne' hfrom' hok' hEok hdv
      $$ [Hst Hbe Happ Hcs Hlr Hgr HKV Hao Hfs Hka HRS Hdv HAR]
      as %appt %appi %stop ⟨Hfs, Hdv, HAR, %st', %a', %at', %csl, Hst, Hbe, Happ, Hcs, Hlr, Hgr, Hao, #HWA',
        ⟨%x', HKV, %Hx', #Hlog', Hka, HRS⟩, %Hpost⟩
    · rw [show ai + 1 - 1 = ai by word]
      iframe Hsrv Hbw' Hsub Hentsd Hst Hbe Happ Hcs Hlr Hgr HKV Hao HW HWA Hfs Hbc' Hlog Hka HRS Hkb'
        Hdv Hdvr2 HAR
    obtain ⟨hli, hlt, hok2, hci2, hstop⟩ := Hpost
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
    iapply HΦ
    iframe Hfs
    isplitl [Hdv]
    · rw [hun]; iexact Hdv
    isplitl [HAR]
    · rw [hun]; iexact HAR
    iexists st', appi, appt, a', at', csl
    iframe
    isplitr
    · rw [hun]; iexact HWA'
    isplitl [Hka HRS]
    · isplitr
      · ipureintro; rw [hun]; exact Hx'
      iframe Hlog'
      rw [hun]; iframe Hka HRS
    ipureintro
    refine ⟨hok2, hfin, ?_, Or.inr hci2, Or.inr (by rw [hun]; exact hlt)⟩
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
    iapply HΦ
    iframe Hfs
    isplitl [Hdv]
    · rw [hun, List.append_nil]; iexact Hdv
    isplitl [HAR]
    · rw [hun, List.append_nil]; iexact HAR
    iexists st, ai, at0, a, t, cs
    iframe
    isplitr
    · rw [hun, List.length_nil, Nat.add_zero]; iexact HWA
    isplitl [Hka HRS]
    · isplitr
      · ipureintro; rw [hun]; rfl
      iframe Hlog
      rw [hun, List.append_nil]; iframe Hka HRS
    ipureintro
    refine ⟨Hok, ?_, by rw [hun]; simp, Or.inl rfl, Or.inl ⟨hun, rfl⟩⟩
    rw [hmL]
    simp only [Option.map_some, Option.getD_some]
    have : ¬ uint.Z ai + 1 - uint.Z f0 < ents.length := by rw [← hoff, ← hlenu]; exact Hif
    omega


/-- **`applyEntries.specOn`** (the auth plan's E3p): `wp_proof` over `apply.specOn`. -/
theorem EtcdServer.applyEntries.wp_proofOn
    (hGI : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG))
    (hApply : EtcdServer.apply.specOn (GF := GF) (hG := hG)) :
    EtcdServer.applyEntries.specOn (GF := GF) (hG := hG) := by
  have hGI := wp_entryAt_GetIndex hGI
  intro s γ ci TM E ρ b ep ap es ents ms f0 rac st ai at0 a t cs x γr A γp dv w γa sa hM hRB Hms Hai1 Hok hEok
    hdv
  wp_start as ⟨#Hsrv, #Hlnil, #Hbw, #Hes, #Hrac, #Hesl, #Hentsat, Hai, Hat, Hcs, Hst, Hbe, Happ, Hlr, Hgr, HKV, Hao, #Hlog, #Hbc, #HW, #HWA, Hfs, Hka, HRS, #Hkb, Hdv, #Hdvr, HAR⟩
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
    iapply HΦ
    iframe Hfs
    isplitl [Hdv]
    · rw [show A ++ unapplied ai [] = A by simp [unapplied]]; iexact Hdv
    isplitl [HAR]
    · rw [show A ++ unapplied ai [] = A by simp [unapplied]]; iexact HAR
    iexists st, ai, at0, a, t, cs
    iframe
    isplitr
    · rw [show (unapplied ai []).length = 0 by simp [unapplied], Nat.add_zero]; iexact HWA
    isplitl [Hka HRS]
    · isplitr
      · ipureintro; rfl
      iframe Hlog
      rw [show A ++ unapplied ai [] = A by simp [unapplied]]; iframe Hka HRS
    ipureintro
    refine ⟨Hok, ?_, by simp [unapplied], Or.inl rfl, Or.inl ⟨by simp [unapplied], rfl⟩⟩
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
    ihave #Hkb' : iprop(kvBatch γr (ciEff γ st.k) ai A (ms.drop k)) $$ []
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
      (ai + 1) ep cs rac st a t x γr A γp dv w γa sa hM hRB hne' hfrom' hok' hEok hdv
      $$ [Hst Hbe Happ Hcs Hlr Hgr HKV Hao Hfs Hka HRS Hdv HAR]
      as %appt %appi %stop ⟨Hfs, Hdv, HAR, %st', %a', %at', %csl, Hst, Hbe, Happ, Hcs, Hlr, Hgr, Hao, #HWA',
        ⟨%x', %sa', HKV, %Hx', #Hlog', Hka, HRS⟩, %Hpost⟩
    · rw [show ai + 1 - 1 = ai by word]
      iframe Hsrv Hlnil Hbw' Hsub Hentsd Hst Hbe Happ Hcs Hlr Hgr HKV Hao HW HWA Hfs Hbc' Hlog Hka HRS Hkb'
        Hdv Hdvr2 HAR
    obtain ⟨hli, hlt, hok2, hci2, hstop⟩ := Hpost
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
    iapply HΦ
    iframe Hfs
    isplitl [Hdv]
    · rw [hun]; iexact Hdv
    isplitl [HAR]
    · rw [hun]; iexact HAR
    iexists st', appi, appt, a', at', csl
    iframe
    isplitr
    · rw [hun]; iexact HWA'
    isplitl [Hka HRS]
    · isplitr
      · ipureintro; rw [hun]; exact Hx'
      iframe Hlog'
      rw [hun]; iframe Hka HRS
    ipureintro
    refine ⟨hok2, hfin, ?_, Or.inr hci2, Or.inr (by rw [hun]; exact hlt)⟩
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
    iapply HΦ
    iframe Hfs
    isplitl [Hdv]
    · rw [hun, List.append_nil]; iexact Hdv
    isplitl [HAR]
    · rw [hun, List.append_nil]; iexact HAR
    iexists st, ai, at0, a, t, cs
    iframe
    isplitr
    · rw [hun, List.length_nil, Nat.add_zero]; iexact HWA
    isplitl [Hka HRS]
    · isplitr
      · ipureintro; rw [hun]; rfl
      iframe Hlog
      rw [hun, List.append_nil]; iframe Hka HRS
    ipureintro
    refine ⟨Hok, ?_, by rw [hun]; simp, Or.inl rfl, Or.inl ⟨hun, rfl⟩⟩
    rw [hmL]
    simp only [Option.map_some, Option.getD_some]
    have : ¬ uint.Z ai + 1 - uint.Z f0 < ents.length := by rw [← hoff, ← hlenu]; exact Hif
    omega

end proof2

end EtcdGrove
end Perennial
