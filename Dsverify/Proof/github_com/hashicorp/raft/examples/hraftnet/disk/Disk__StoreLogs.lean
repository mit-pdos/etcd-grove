/-
(hraft_robust R3) The proof of `disk.(*Disk).StoreLogs`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Disk__StoreLogs
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.WriteLemmas
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Disk__insert
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Disk__persist
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section sec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]
variable [dur_sem : github_com.mit_pdos.etcd_grove.examples.lib.durable.Assumptions]

open github_com.hashicorp.raft proto github_com.hashicorp.raft.examples.hraftnet.disk EtcdGrove

set_option goose.wp.extras true

/-- The loop's insertions so far: the first `k` entries, at `first..`. -/
def dkStoredPre (first : Nat) (es : RLog) (ds : List DEnt) : Prop :=
  ∀ j d, ds[j]? = some d → uint.nat d.idx = first + j ∧ es[j]? = some (entOf d)

theorem dk_stored_snoc (first : Nat) (es : RLog) (ds : List DEnt) (d : DEnt) (e : Entry)
    (h : dkStoredPre first es ds) (hk : uint.nat d.idx = first + ds.length) (he : es[ds.length]? = some e)
    (hent : entOf d = e) : dkStoredPre first es (ds ++ [d]) := by
  intro j d' hd'
  by_cases hj : j < ds.length
  · rw [List.getElem?_append_left hj] at hd'; exact h j d' hd'
  · have : j = ds.length := by
      have := (List.getElem?_eq_some_iff.1 hd').1; simp at this; omega
    subst this
    rw [List.getElem?_append_right (by omega), Nat.sub_self] at hd'
    simp at hd'; subst hd'
    exact ⟨hk, by rw [he, hent]⟩

theorem dk_stored_all (first : Nat) (es : RLog) (ds : List DEnt) (h : dkStoredPre first es ds)
    (hl : ds.length = es.length) : StoredAs first es ds := ⟨hl, h⟩

theorem dk_store_img (I : DiskImg) (stg : w64) (first : Nat) (es : RLog) (ds : List DEnt) (hok : I.Ok)
    (h : StoredAs first es ds) (hb : first + es.length ≤ 2 ^ 64) (hf : 1 ≤ first) :
    (storeImg I ds stg).Pre ∧
    DiskAbs.of (storeImg I ds stg) stg = (DiskOp.log (.store first es)).apply (DiskAbs.of I stg) := by
  have hd : ∀ d ∈ ds, 1 ≤ uint.nat d.idx := by
    intro d hd
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hd
    have := (h.2 j _ (List.getElem?_eq_getElem hj)).1; omega
  obtain ⟨h1, h2⟩ := storeImg_absL I stg first es ds hok.idx h hb hd
  refine ⟨⟨h2, hok.kvKeys, hok.ikvKeys⟩, ?_⟩
  rw [apply_log]
  unfold DiskAbs.of
  simp only [logApply]
  rw [h1]; rfl

theorem github_com.hashicorp.raft.examples.hraftnet.disk.Disk.StoreLogs.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_insert : github_com.hashicorp.raft.examples.hraftnet.disk.Disk.insert.spec (GF := GF) (hG := hG))
    (wp_persist : github_com.hashicorp.raft.examples.hraftnet.disk.Disk.persist.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.disk.Disk.StoreLogs.spec (GF := GF) (hG := hG) := by
  intro g d Wl Ws Wf sl dq ptrs first es
  iintro %Φ %Hpre #Hdisk Hsl #Hptrs Hw HAU
  obtain ⟨hfirst, hlen, hb⟩ := Hpre
  iunfold isDisk at Hdisk
  icases Hdisk with ⟨%mu, #Hpkg, #Hmu, #Hisl, #Hfile, #Hinv, #Hdinv, #Hos, #Hsh, %Hf⟩
  ihave %Hsll := ownSlice_len $$ Hsl
  wp_method_call
  wp_call
  try wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  try wp_auto
  wp_apply (lc := 2) wp_Lock $$ [$Hisl] as ⟨Hlocked, HR⟩
  iunfold diskLockInv at HR
  icases HR with ⟨%I, %stg, %qc, Hmem, Hrec, %HIok, Hdh, Hcp⟩
  try wp_auto
  ihave HI : (∃ (i : w64) (ds : List DEnt) (lp : Loc), "i" ∷ i_ptr ↦ i ∗ "l" ∷ l_ptr ↦ lp ∗
      "Hsl" ∷ sl ↦*{dq} ptrs ∗
      "Hmem" ∷ diskMem d { I with ents := insAll I.ents ds } stg ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z sl.len ∧ ds.length = sint.nat i ∧ dkStoredPre first es ds⌝ :
      IProp GF) $$ [i l Hsl Hmem]
  · iexists W64 0, [], _
    iframe
    ipureintro
    exact ⟨by word, Hsll.2, rfl, fun j d h => by simp at h⟩
  wp_for HI
  wp_if_destruct
  · have hlt := Hif
    have hil : sint.nat i < ptrs.length := dk_idx_lt i sl.len _ Hsll Hi.1 hlt
    list_elem ptrs (sint.nat i) as p
    ihave Hp := BigSepL.bigSepL_lookup Hp_lookup $$ Hptrs
    icases Hp with ⟨%e, %He, #Hlp⟩
    iunfold logPtr at Hlp
    icases Hlp with ⟨%lvp, #Hl, #Hlis⟩
    iunfold logIs at Hlis
    icases Hlis with ⟨%Hlf, #Hdata, %x, #Hext⟩
    simp only [show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len from ⟨Hi.1, hlt⟩, _root_.and_self, ↓reduceIte]
    wp_apply (wp_load_slice_index sl (sint.Z i) ptrs dq p Hi.1) $$ [$Hsl] as Hsl
    · ipureintro; rw [dk_toNat_sint]; exact Hp_lookup
    ihave Hlsp := Hl
    iStructNamed Hlsp
    try wp_auto
    wp_apply (wp_insert d { I with ents := insAll I.ents ds } stg _ ⟨lvp.Index', lvp.Term', lvp.Type', e.data, x⟩)
      $$ [$Hmem] as Hmem
    · iunfold entRep
      isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl⟩
      iframe #
    obtain ⟨hs1, hs2, hs3⟩ := dk_idx_succ i sl.len Hi.1 hlt
    wp_for_post
    iframe
    iexists i + W64 1, ds ++ [⟨lvp.Index', lvp.Term', lvp.Type', e.data, x⟩], p
    have heq : insEnt ⟨lvp.Index', lvp.Term', lvp.Type', e.data, x⟩ (insAll I.ents ds) =
        insAll I.ents (ds ++ [⟨lvp.Index', lvp.Term', lvp.Type', e.data, x⟩]) := by
      simp only [insAll, List.foldl_append, List.foldl_cons, List.foldl_nil, insEnt_eq]
    simp only [heq]
    iframe
    ipureintro
    refine ⟨hs2, hs3, by rw [List.length_append, Hi.2.2.1, List.length_singleton, ← hs1], ?_⟩
    have hk : ds.length = sint.nat i := Hi.2.2.1
    refine dk_stored_snoc first es ds _ e Hi.2.2.2 (by rw [hk]; exact Hlf.1) (by rw [hk]; exact He) ?_
    unfold entOf
    cases e; simp only at Hlf ⊢; rw [Hlf.2.1, Hlf.2.2]
  · have hie := dk_idx_eq i sl.len _ Hsll Hi.2.1 Hif
    have hds : StoredAs first es ds := dk_stored_all first es ds Hi.2.2.2 (by rw [Hi.2.2.1, hie, hlen])
    obtain ⟨hpre, hab⟩ := dk_store_img I stg first es ds HIok hds hb hfirst
    iunfold diskMem at Hmem
    icases Hmem with ⟨%es', %ks, %vs, %iks, %ivs, %lvs, %kss, %vss, %ikss, Hents, Hes, Hescap, #Hent,
      Hkeys, Hks, Hkscap, #Hkr, Hvals, Hvs, Hvscap, #Hvr, Hikeys, Hiks, Hikscap, #Hikr,
      Hivals, Hivs, Hivscap, Hstaged, Hcommit⟩
    try wp_auto
    ihave Hmem : diskMem d (storeImg I ds stg) stg $$
        [Hents Hes Hescap Hkeys Hks Hkscap Hvals Hvs Hvscap Hikeys Hiks Hikscap Hivals Hivs Hivscap
         Hstaged Hcommit]
    · iunfold diskMem; simp only [storeImg]
      iexists es', ks, vs, iks, ivs, lvs, kss, vss, ikss; iframe; iframe #
    wp_bind (App (Val #(methods (go.GoType.PointerType Disk.ty) go!"persist" #d)) (Val #()))
    iapply (wp_persist g d (storeImg I ds stg) stg qc) $$ Hpkg Hfile [] Hos Hsh Hdinv Hmem Hdh Hcp
    · ipureintro; exact Hf
    iapply (diskWriteAU g Wl Ws Wf I (storeImg I ds stg) stg (.log (.store first es)) _ hpre hab)
      $$ Hinv Hrec [Hw]
    · simp only [winOf]; iexact Hw
    iintro Hrec Hdh Hcp Hmem
    try wp_auto
    iapply wp_ncfupd _ _ rfl
    iintro Hnc
    imod (diskCommitL g Wl Ws Wf I (storeImg I ds stg) stg (.store first es)
        (fun A => iprop(diskOwnL g (A.store first es) ={∅,⊤ \ ↑storeN}=∗ (sl ↦*{dq} ptrs -∗ Φ #interface.nil)))
        iprop(sl ↦*{dq} ptrs -∗ Φ #interface.nil)) $$ Hinv Hrec Hlc1 Hlc2 [] HAU Hnc with ⟨Hnc, Hrec, %Hok', HΦ⟩
    · iintro %A HR Hown
      rw [show logApply (LogOp.store first es) A = A.store first es from rfl]
      iapply HR $$ Hown
    imodintro
    iframe Hnc
    try wp_auto
    wp_apply wp_Unlock $$ [$Hisl $Hlocked Hrec Hdh Hcp Hmem]
    · inext; iunfold diskLockInv; iexists storeImg I ds stg, stg, qc; iframe
      ipureintro; exact Hok'
    try wp_auto
    iapply HΦ $$ Hsl

end sec

end Perennial
