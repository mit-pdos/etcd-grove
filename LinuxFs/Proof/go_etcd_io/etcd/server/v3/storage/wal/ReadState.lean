/- Lean-first (no Rocq counterpart).

# The WAL as `ReadAll` reads it, proved (W3/W5 of `notes/wal-fsext-plan.md`, eighteenth session)

`walInvBody_readState` (was the hypothesis `WalReadState`, `ReadAllLaws.lean`): at a step, the WAL's
key, the program's half of its directory's claim, the empty program half of the tails' authority and
the program's halves of the pinned segments `gs` give the invariant's state `d`, layout and directory
names with `WalAbsD` (whose `cutPos` and `nameBound`'s `ix < 2^64` `readAll_success` reads), the tail
idle (`WalTailIdle`), and the pinned segments the layout's from some `kk` on.

The pinned segments need no invariant law of their own (the sixteenth session's `WalPinnedSegs` and
"files singly named" designs): the program's half of the directory's claim agrees with the
invariant's (`osClaims_agree`), so the claim's `.wal` names are the layout's segments' (`WalAbsD.names`,
`SegsNamed`: `walNames_segs`), and `walReadTie` records that the pinned segments' names are those names
from some position on (`openAtIndex` knows it at the pin). Each pinned segment's name then gives its
inode (both entries are the same claim's), and the halves of its `OsMeta` and bytes agree with the
invariant's (no change in flight: `walTailsRes_none`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllLaws
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailSyncIdle
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenNames

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Fs WalEnc

section pure
variable [GooseExts]

/-- **The claim's `.wal` names are the segments'**, in order (`walNamesOut_segs`'s argument, over
`walNames`). -/
theorem walNames_segs {hj : NamesH} {segs : List SegG}
    (hsn : SegsNamed segs hj.cur)
    (hnames : walInos hj.cur = segs.map (·.ino)) (hnd : (segs.map (·.ino)).Nodup)
    (hsort : (segs.map (·.name)).Pairwise (fun a b => go.GoStringLt a b)) :
    walNames hj.cur = segs.map (·.name) := by
  have hnds : (segs.map (·.name)).Nodup :=
    hsort.imp (fun {a b} h hab => by subst hab; exact go.goStringLt_irrefl _ h)
  have hndk : (((GMap.toList hj.cur).map (·.1)).filter walNameP).Nodup :=
    List.Nodup.sublist List.filter_sublist (GMap.toList_keys_nodup hj.cur)
  have hperm : (((GMap.toList hj.cur).map (·.1)).filter walNameP).Perm (segs.map (·.name)) := by
    refine (List.perm_ext_iff_of_nodup hndk hnds).2 fun b => ⟨fun hb => ?_, fun hb => ?_⟩
    · obtain ⟨hbk, hbw⟩ := List.mem_filter.1 hb
      obtain ⟨⟨b', e⟩, he, rfl⟩ := List.mem_map.1 hbk
      have he' := (GMap.mem_toList _ _ _).1 he
      obtain ⟨g, hg, rfl⟩ := walName_seg hsn hnames hnd hbw he'
      exact List.mem_map.2 ⟨g, hg, rfl⟩
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hb
      obtain ⟨hgw, hge⟩ := hsn.1 g hg
      exact List.mem_filter.2 ⟨List.mem_map.2 ⟨(g.name, _), (GMap.mem_toList _ _ _).2 hge, rfl⟩, hgw⟩
  unfold walNames
  rw [mergeSort_name_perm hperm]
  exact List.mergeSort_of_pairwise (hsort.imp fun h => by simp [h])

/-- The `i`-th names of two lists with equal name maps. -/
theorem name_at_eq {a b : List SegG} (hn : a.map (·.name) = b.map (·.name)) (i : Nat)
    (h1 : i < a.length) (h2 : i < b.length) : a[i].name = b[i].name := by
  have := congrArg (·[i]?) hn
  simp only [List.getElem?_map, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2,
    Option.map_some, Option.some.injEq] at this
  exact this

/-- The inodes of the pinned segments are the layout's from `kk` on (each at its name in the
directory's entries). -/
theorem segs_drop_inos {segs gs : List SegG} {ents : Ents} {kk : Nat}
    (hn : (segs.drop kk).map (·.name) = gs.map (·.name)) (hsn : SegsNamed segs ents)
    (hnm : ∀ g ∈ gs, ents !! g.name = some (.file g.ino)) :
    gs.map (·.ino) = (segs.drop kk).map (·.ino) := by
  have hl : (segs.drop kk).length = gs.length := by
    have := congrArg List.length hn; simpa using this
  refine List.ext_getElem (by simp only [List.length_map]; exact hl.symm) (fun i h1 h2 => ?_)
  simp only [List.length_map] at h1 h2
  simp only [List.getElem_map]
  have hname := name_at_eq hn i h2 h1
  have hmem : (segs.drop kk)[i] ∈ segs := List.mem_of_mem_drop (List.getElem_mem h2)
  have he1 := (hsn.1 _ hmem).2
  have he2 := hnm _ (List.getElem_mem h1)
  rw [hname, he2] at he1
  injection he1 with h; injection h

/-- **The pinned segments are the layout's from `kk` on**, given their names are and each is at its
name in the directory's entries, and their `OsMeta`s and bytes agree index by index. -/
theorem segs_drop_eq {segs gs : List SegG} {ents : Ents} {kk : Nat}
    (hn : (segs.drop kk).map (·.name) = gs.map (·.name)) (hsn : SegsNamed segs ents)
    (hnm : ∀ g ∈ gs, ents !! g.name = some (.file g.ino))
    (hom : ∀ (i : Nat) (g g' : SegG), gs[i]? = some g → (segs.drop kk)[i]? = some g' →
      g.om = g'.om ∧ g.bs = g'.bs) :
    segs.drop kk = gs := by
  have hl : (segs.drop kk).length = gs.length := by
    have := congrArg List.length hn; simpa using this
  have hinos := segs_drop_inos hn hsn hnm
  refine List.ext_getElem hl (fun i h1 h2 => ?_)
  have hname := name_at_eq hn i h1 h2
  have hino : (segs.drop kk)[i].ino = gs[i].ino := by
    have := congrArg (·[i]?) hinos
    simp only [List.getElem?_map, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2,
      Option.map_some, Option.some.injEq] at this
    exact this.symm
  obtain ⟨hom1, hbs1⟩ := hom i gs[i] (segs.drop kk)[i] (List.getElem?_eq_getElem h2)
    (List.getElem?_eq_getElem h1)
  generalize (segs.drop kk)[i] = a at hname hino hom1 hbs1
  generalize gs[i] = b at hname hino hom1 hbs1
  cases a; cases b
  simp_all

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- Two parts of an `OsMeta` agree. -/
theorem osMeta_agree_rs (i : Ino) (dq1 dq2 : DFrac) (m1 m2 : OsMeta) :
    ⊢@{IProp GF} osMeta (L := L) i dq1 m1 -∗ osMeta (L := L) i dq2 m2 -∗ ⌜m1 = m2⌝ := by
  unfold osMeta
  iintro H1 H2
  icases gElem_valid_2 _ _ _ _ _ _ _ $$ H1 H2 with %hv
  ipureintro; exact hv.2

/-- A segment list's parts with no change in flight are its halves. -/
theorem segResF_empty_list (l : List SegG) :
    ([∗list] g ∈ l, segResF (L := L) ∅ g) ⊣⊢ [∗list] g ∈ l, segRes (L := L) g := by
  unfold segResF
  have h : ∀ i : Ino, (∅ : GMap Ino SegFl) !! i = none := fun i => by simp
  simp only [h]
  exact .rfl

/-- A list's resources, split at `k`. -/
theorem rs_bigSepL_take_drop (P : SegG → IProp GF) (l : List SegG) (k : Nat) :
    ([∗list] g ∈ l, P g) ⊣⊢ ([∗list] g ∈ l.take k, P g) ∗ [∗list] g ∈ l.drop k, P g := by
  conv => lhs; rw [← List.take_append_drop k l]
  exact BigSepL.bigSepL_append

/-- **The program's halves of segments agree with the invariant's** of segments of the same inodes,
index by index (the sizes their bytes' lengths). -/
theorem halves_agree : ∀ (gs gs' : List SegG), gs.map (·.ino) = gs'.map (·.ino) →
    (∀ g ∈ gs, g.om.size = g.bs.length) → (∀ g ∈ gs', g.om.size = g.bs.length) →
    ⊢ ([∗list] g ∈ gs, osMeta (L := L) g.ino (DFrac.own (1 : Qp).half) g.om ∗
        osBytes (L := L) g.ino 0 (DFrac.own (1 : Qp).half) g.bs) -∗
      ([∗list] g ∈ gs', segRes (L := L) g) -∗
      ⌜∀ (i : Nat) (g g' : SegG), gs[i]? = some g → gs'[i]? = some g' → g.om = g'.om ∧ g.bs = g'.bs⌝ ∗
      ([∗list] g ∈ gs, osMeta (L := L) g.ino (DFrac.own (1 : Qp).half) g.om ∗
        osBytes (L := L) g.ino 0 (DFrac.own (1 : Qp).half) g.bs) ∗
      ([∗list] g ∈ gs', segRes (L := L) g)
  | [], [], _, _, _ => by
    iintro H1 H2
    iframe H1 H2
    ipureintro; intro i g g' h; simp at h
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h
  | g :: gs, g' :: gs', h, hs, hs' => by
    simp only [List.map_cons, List.cons.injEq] at h
    iintro H1 H2
    icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ H1 with ⟨⟨Hm, Hb⟩, H1⟩
    icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ H2 with ⟨H2a, H2⟩
    iunfold segRes at H2a
    icases H2a with ⟨Hm', Hb'⟩
    rw [← h.1]
    icases osMeta_agree_rs g.ino _ _ g.om g'.om $$ Hm Hm' with %hm
    have hl : g.bs.length = g'.bs.length := by
      rw [← hs g (List.mem_cons_self ..), ← hs' g' (List.mem_cons_self ..), hm]
    icases osBytes_agree (L := L) g.ino _ _ 0 g.bs g'.bs hl $$ Hb Hb' with %hb
    icases halves_agree gs gs' h.2 (fun x hx => hs x (List.mem_cons_of_mem _ hx))
      (fun x hx => hs' x (List.mem_cons_of_mem _ hx)) $$ H1 H2 with ⟨%hr, H1, H2⟩
    isplitr
    · ipureintro
      intro i a b ha hb'
      cases i with
      | zero => simp at ha hb'; subst ha; subst hb'; exact ⟨hm, hb⟩
      | succ i => exact hr i a b (by simpa using ha) (by simpa using hb')
    isplitl [Hm Hb H1]
    · iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
      iframe
    · iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
      iframe H2
      unfold segRes
      rw [← h.1]
      iframe

/-- **The WAL as `ReadAll` reads it** (see the file header; was the hypothesis `WalReadState`). -/
theorem walInvBody_readState (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (dir : GoString) (j : Ino) (X : List GoString) (hj0 : NamesH) (gs : List SegG)
    (hnm : ∀ g ∈ gs, hj0.cur !! g.name = some (.file g.ino))
    (hdrop : ∃ kk, (walNames hj0.cur).drop kk = gs.map (·.name))
    (hsz : ∀ g ∈ gs, g.om.size = g.bs.length) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ walDirKey (W := W) dir j X -∗
      osNames (L := L) j (.except X) (DFrac.own (1 : Qp).half) hj0 -∗
      walTailsFrag (W := W) ∅ -∗
      ([∗list] g ∈ gs, osMeta (L := L) g.ino (DFrac.own (1 : Qp).half) g.om ∗
        osBytes (L := L) g.ino 0 (DFrac.own (1 : Qp).half) g.bs) -∗
      ∃ (d : WalDur) (lay : WalLay) (kk : Nat),
        ⌜s.wal !! dir = some d ∧ lay.j = j ∧ WalAbsD C Mr d lay hj0.cur ∧ TailExact lay ∧
          lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length ∧ lay.segs.drop kk = gs⌝ ∗
        walInvBody (L := L) (W := W) C Mr R jr r s ∗ walDirKey (W := W) dir j X ∗
        osNames (L := L) j (.except X) (DFrac.own (1 : Qp).half) hj0 ∗ walTailsFrag (W := W) ∅ ∗
        ([∗list] g ∈ gs, osMeta (L := L) g.ino (DFrac.own (1 : Qp).half) g.om ∗
          osBytes (L := L) g.ino 0 (DFrac.own (1 : Qp).half) g.bs) := by
  iintro Hb Hk Hn Hf Hgs
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl, Hcm, Hlays, %HW, %HWC, HCR, Htl, %Hab, %HNm, Hpk,
    ⟨%K, %cp, Hdk, Hcp, %Hdko⟩, %HAt, Hnms, %Hbd⟩
  icases walDirKey_lookup K dir j X $$ Hdk Hk with %hK
  obtain ⟨lay, hj, hl, hlj, -, -, hOnce, -, hOther⟩ := Hdko.1 dir j X hK
  obtain ⟨d, hd⟩ : ∃ d, s.wal !! dir = some d := by
    cases h : s.wal !! dir with
    | none => rw [HW.2.1 dir h] at hl; cases hl
    | some d => exact ⟨d, rfl⟩
  obtain ⟨lay1, nm, hj', hl1, -, -, -, hWDC, habs, -⟩ := HW.1 dir d hd
  rw [hl] at hl1; cases hl1
  have hjj : hj' = hj := by
    obtain ⟨X', hX', hmem, -⟩ := hWDC
    by_cases hc : (lay.j, NameSet.except X', hj') = (j, NameSet.except X, hj)
    · simp only [Prod.mk.injEq] at hc; exact hc.2.2
    · exact absurd (exceptMem_dotWal hX') (hOther _ hmem hc hlj go!".wal" walNameP_dotWal)
  subst hjj
  obtain ⟨l1, l2, hcl, -, -⟩ := hOnce
  icases osClaims_agree (L := L) cl (j, NameSet.except X, hj') (by rw [hcl]; simp) hj0 $$ [Hcl Hn] with
    ⟨%h0, Hcl, Hn⟩
  · iframe Hcl Hn
  simp only at h0
  subst h0
  icases walTailsRes_idle C Mr s Ls F $$ Htl Hf with ⟨%hidle, Htl, Hf⟩
  icases walTailsRes_none C Mr s Ls F $$ Htl Hf with ⟨%hF, Htl, Hf⟩
  have hF' : F = ∅ := (GMap.lookup_empty_iff F).1 hF
  subst hF'
  have hid : TailIdle C Mr d lay := hidle dir d lay hd hl
  have hsn : SegsNamed lay.segs hj0.cur := (HNm dir lay hl).1 hj0 hWDC
  have hnd : (lay.segs.map (·.ino)).Nodup := ((segsAll_nodup_iff Ls).1 HW.2.2.1).1 dir lay hl
  obtain ⟨kk, hkk⟩ := hdrop
  have hn : (lay.segs.drop kk).map (·.name) = gs.map (·.name) := by
    rw [List.map_drop, ← walNames_segs hsn habs.names.1 hnd habs.names.2]; exact hkk
  have hinos := segs_drop_inos hn hsn hnm
  icases (laysResF_del (L := L) ∅ Ls dir lay hl).1 $$ Hlays with ⟨Hsegs, Hrest⟩
  icases (segResF_empty_list (L := L) lay.segs).1 $$ Hsegs with Hsegs
  icases (rs_bigSepL_take_drop (segRes (L := L)) lay.segs kk).1 $$ Hsegs with ⟨Hpre, Hsuf⟩
  icases halves_agree (L := L) gs (lay.segs.drop kk) hinos hsz
    (fun g hg => (habs.metas g (List.mem_of_mem_drop hg)).1) $$ Hgs Hsuf with ⟨%hom, Hgs, Hsuf⟩
  have hdeq := segs_drop_eq hn hsn hnm hom
  iexists d, lay, kk
  isplitr
  · ipureintro; exact ⟨hd, hlj, habs, hid.1, hid.2.1, hdeq⟩
  iframe Hk Hn Hf Hgs
  iexists Ls, cl, n, ∅
  iframe Hg Hcm HCR Htl Hpk Hnms Hcl
  isplitr
  · ipureintro; exact Har
  isplitl [Hpre Hsuf Hrest]
  · iapply (laysResF_del (L := L) ∅ Ls dir lay hl).2
    iframe Hrest
    iapply (segResF_empty_list (L := L) lay.segs).2
    iapply (rs_bigSepL_take_drop (segRes (L := L)) lay.segs kk).2
    iframe
  isplitr
  · ipureintro; exact HW
  isplitr
  · ipureintro; exact HWC
  isplitr
  · ipureintro; exact Hab
  isplitr
  · ipureintro; exact HNm
  isplitl [Hdk Hcp]
  · iexists K, cp; iframe Hdk Hcp; ipureintro; exact Hdko
  isplitr
  · ipureintro; exact HAt
  ipureintro; exact Hbd

end iris

end WalFs
end EtcdGrove
end Perennial
