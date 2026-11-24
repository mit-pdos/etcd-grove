/- Lean-first (no Rocq counterpart).

# The WAL's crash boot (`notes/wal-fsext-w4c-plan.md`, §3, "W4c U3 log", (b))

`walBootCrash`: the new generation's boot after a crash. From what `walInv_crash` gives the crash
obligation (the new generation's `walStart` over the crashed tree, the crashed state's `WalsBounded`
and `DirsRoots`, the area, the crash boot's files `bootFiles`, the tree well formed) and the new
generation's shared view (`osShared`, with `V` the crashed history, nothing logged: `crashRest_treeS`),
what a WAL client needs to call `Open`, `Create`, ...: the area's
`walAreaOk` (the invariant, allocated by `walInv_alloc`) and the program's `walAreaRes`; back, the
area's claim on the names that are no `AreaSlot` holding an entry (`bootOthers`) and every directory's
whole claim but the area's, the WALs' and those under an `nm.<sfx>` (`bootRest`; another root's
directory among them, `mem_bootRest_root`). The lock and crash tokens and `walPast` come from
`walInv_crash`; `osCallPerm 1` is the program's.

The claims (`BootCrashSub`): `walInv_alloc`'s `cl` holds the area's claim on `bootN` (every name but the
WALs' and those given back), each WAL directory's on its non-pipeline names (`walDir_boot`; its pipeline
names to `walTmpsRes`), each WAL name's own (`.only [nm]`); `walAreaRes` the area claim's other half and
the whole claims of every directory under an `nm.<sfx>`, tagged with it (`bootCls`).

Premises beyond the first boot's (`walBoot0`): **`hfo : BootFo V.now jr`** (every WAL directory holds only
files: `walInv_crash` gives it, `bootFo_of`; its `nm.tmp` parts retired 2026-11-22), and the facts
`walInv_crash` returns (`hwf`, `har`, `hbd`, `hdr`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.BootCrashRes
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Crash

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- The WALs' directory claims (`walInv_alloc`'s `hdirs`). -/
def bootWalCls (V : Hist) (jr : Ino) : List Claim :=
  (bootWals V.now jr).map (fun p => (p.2, NameSet.except walTmps, namesOf V p.2 (.except walTmps)))

/-- The WALs' name claims (`walInv_alloc`'s `hnames`). -/
def bootNameCls (V : Hist) (jr : Ino) : List Claim :=
  (bootWn V.now jr).map (fun nm => (jr, NameSet.only [nm], namesOf V jr (.only [nm])))

/-- The area's claim. -/
def bootAreaCl (V : Hist) (jr : Ino) : Claim := (jr, bootN V.now jr, namesOf V jr (bootN V.now jr))

/-- **`walInv_alloc`'s claims at the crash boot.** -/
def bootCl (V : Hist) (jr : Ino) : List Claim :=
  bootAreaCl V jr :: (bootWalCls V jr ++ bootNameCls V jr)

/-- The temporary directories' map (`walInv_alloc`'s `Jm`): each WAL's path to its directory. -/
def bootJm (V : Hist) (jr : Ino) (r : GoString) : GMap GoString Ino :=
  GMap.ofList ((bootWals V.now jr).map (fun p => (r ++ go!"/" ++ p.1, p.2)))

theorem claimOnce_of_nodup {c : Claim} {cl : List Claim} (hn : cl.Nodup) (hc : c ∈ cl) :
    ClaimOnce c cl := by
  obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hc
  refine ⟨l1, l2, rfl, fun h => ?_, (List.nodup_cons.1 (List.nodup_append.1 hn).2.1).1⟩
  exact (List.nodup_append.1 hn).2.2 c h c (List.mem_cons_self ..) rfl

theorem mem_bootWalCls {V : Hist} {jr : Ino} {c : Claim} :
    c ∈ bootWalCls V jr ↔ ∃ nm J, (nm, J) ∈ bootWals V.now jr ∧
      c = (J, NameSet.except walTmps, namesOf V J (.except walTmps)) := by
  unfold bootWalCls
  constructor
  · intro h; obtain ⟨⟨nm, J⟩, hm, rfl⟩ := List.mem_map.1 h; exact ⟨nm, J, hm, rfl⟩
  · rintro ⟨nm, J, hm, rfl⟩; exact List.mem_map.2 ⟨_, hm, rfl⟩

theorem mem_bootNameCls {V : Hist} {jr : Ino} {c : Claim} :
    c ∈ bootNameCls V jr ↔ ∃ nm, nm ∈ bootWn V.now jr ∧
      c = (jr, NameSet.only [nm], namesOf V jr (.only [nm])) := by
  unfold bootNameCls
  constructor
  · intro h; obtain ⟨nm, hm, rfl⟩ := List.mem_map.1 h; exact ⟨nm, hm, rfl⟩
  · rintro ⟨nm, hm, rfl⟩; exact List.mem_map.2 ⟨_, hm, rfl⟩

theorem bootCl_nodup {R : Roots} {V : Hist} (hw : TreeWf R V.now) {r : GoString} {jr : Ino}
    (hr : (r, jr) ∈ R) : (bootCl V jr).Nodup := by
  have hu := uniqNames_of_wf hw
  unfold bootCl
  refine List.nodup_cons.2 ⟨fun hm => ?_, List.nodup_append.2 ⟨?_, ?_, fun x hx y hy e => ?_⟩⟩
  · rcases List.mem_append.1 hm with h | h
    · obtain ⟨nm, J, hJ, e⟩ := mem_bootWalCls.1 h
      unfold bootAreaCl at e
      simp only [Prod.mk.injEq] at e
      exact bootWals_ne_root hw hr hJ e.1.symm
    · obtain ⟨nm, -, e⟩ := mem_bootNameCls.1 h
      unfold bootAreaCl bootN at e
      simp only [Prod.mk.injEq] at e
      cases e.2.1
  · refine List.Nodup.mapOnW (bootWals_nodup V.now jr) (fun x hx y hy e => ?_)
    obtain ⟨a, J⟩ := x
    obtain ⟨a', J'⟩ := y
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, -⟩ := e
    rw [bootWals_inj hu hx hy]
  · refine List.Nodup.mapOnW (bootWn_nodup V.now jr) (fun x _ y _ e => ?_)
    have e' := congrArg (fun c : Claim => c.2.1) e
    simpa using e'
  · subst e
    obtain ⟨nm, J, -, e1⟩ := mem_bootWalCls.1 hx
    obtain ⟨nm', -, e2⟩ := mem_bootNameCls.1 hy
    rw [e1] at e2
    simp only [Prod.mk.injEq] at e2
    cases e2.2.1

theorem bootCl_hcl (V : Hist) (jr : Ino) : ∀ c ∈ bootCl V jr, c.2.2 = namesOf V c.1 c.2.1 := by
  intro c hc
  unfold bootCl at hc
  rcases List.mem_cons.1 hc with rfl | hc
  · rfl
  rcases List.mem_append.1 hc with h | h
  · obtain ⟨nm, J, -, rfl⟩ := mem_bootWalCls.1 h; rfl
  · obtain ⟨nm, -, rfl⟩ := mem_bootNameCls.1 h; rfl

theorem bootCl_area (V : Hist) (jr : Ino) : WalsCreateOk jr (bootCl V jr) := by
  intro nm hnm
  rcases bootN_walName (m := V.now) (jr := jr) hnm with h | h
  · exact ⟨_, _, List.mem_cons_self .., h⟩
  · refine ⟨.only [nm], namesOf V jr (.only [nm]), List.mem_cons_of_mem _ (List.mem_append.2
      (.inr (mem_bootNameCls.2 ⟨nm, h, rfl⟩))), List.mem_singleton_self _⟩

theorem bootCl_dirs {V : Hist} {jr : Ino} {nm : GoString} {J : Ino} (hnm : walNameOk nm)
    (he : V.now.entry jr nm = some (.dir J)) :
    (J, NameSet.except walTmps, namesOf V J (.except walTmps)) ∈ bootCl V jr :=
  List.mem_cons_of_mem _ (List.mem_append.2 (.inl (mem_bootWalCls.2
    ⟨nm, J, mem_bootWals.2 ⟨hnm, he⟩, rfl⟩)))

theorem bootCl_dirs1 {R : Roots} {V : Hist} (hw : TreeWf R V.now) {r : GoString} {jr : Ino}
    (hr : (r, jr) ∈ R) (nm : GoString) (J : Ino) (h : NamesH) (hnm : walNameOk nm)
    (he : V.now.entry jr nm = some (.dir J)) (hc : (J, NameSet.except walTmps, h) ∈ bootCl V jr) :
    ClaimOnce (J, NameSet.except walTmps, h) (bootCl V jr) ∧
      ∀ c' ∈ bootCl V jr, c' ≠ (J, NameSet.except walTmps, h) → c'.1 = J →
        ∀ b, (NameSet.except walTmps).Mem b → ¬ c'.2.1.Mem b := by
  have hu := uniqNames_of_wf hw
  have hJ : (nm, J) ∈ bootWals V.now jr := mem_bootWals.2 ⟨hnm, he⟩
  refine ⟨claimOnce_of_nodup (bootCl_nodup hw hr) hc, fun c' hc' hne hj => (hne ?_).elim⟩
  have hh := bootCl_hcl V jr _ hc
  simp only at hh
  subst hh
  unfold bootCl at hc'
  rcases List.mem_cons.1 hc' with rfl | hc'
  · exact (bootWals_ne_root hw hr hJ hj.symm).elim
  rcases List.mem_append.1 hc' with h' | h'
  · obtain ⟨nm', J', -, rfl⟩ := mem_bootWalCls.1 h'
    simp only at hj
    subst hj; rfl
  · obtain ⟨nm', -, rfl⟩ := mem_bootNameCls.1 h'
    simp only at hj
    exact (bootWals_ne_root hw hr hJ hj.symm).elim

theorem bootCl_names {V : Hist} {jr : Ino} {nm : GoString} {J : Ino} (hnm : walNameOk nm)
    (he : V.now.entry jr nm = some (.dir J)) :
    (jr, NameSet.only [nm], namesOf V jr (.only [nm])) ∈ bootCl V jr :=
  List.mem_cons_of_mem _ (List.mem_append.2 (.inr (mem_bootNameCls.2
    ⟨nm, mem_bootWn.2 ⟨J, mem_bootWals.2 ⟨hnm, he⟩⟩, rfl⟩)))

theorem bootCl_nok {R : Roots} {V : Hist} (hw : TreeWf R V.now) {jr : Ino} (b : GoString) (h : NamesH)
    (hc : (jr, NameSet.only [b], h) ∈ bootCl V jr) : NameOk b := by
  unfold bootCl at hc
  rcases List.mem_cons.1 hc with e | hc
  · unfold bootAreaCl bootN at e
    simp only [Prod.mk.injEq] at e
    cases e.2.1
  rcases List.mem_append.1 hc with h' | h'
  · obtain ⟨nm', J', -, e⟩ := mem_bootWalCls.1 h'
    simp only [Prod.mk.injEq] at e
    cases e.2.1
  · obtain ⟨nm', hm, e⟩ := mem_bootNameCls.1 h'
    simp only [Prod.mk.injEq, NameSet.only.injEq, List.cons.injEq, and_true] at e
    obtain ⟨-, rfl, -⟩ := e
    obtain ⟨J, hJ⟩ := mem_bootWn.1 hm
    exact bootWals_nameOk hw hJ

theorem ofList_lookup_none {K V : Type} [DecidableEq K] (k : K) :
    ∀ (l : List (K × V)), k ∉ l.map (·.1) → GMap.ofList l !! k = none
  | [], _ => rfl
  | (k', v) :: l, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    show (GMap.insert k' v (GMap.ofList l)) !! k = none
    rw [GMap.lookup_insert_ne _ _ (Ne.symm h.1)]
    exact ofList_lookup_none k l h.2

theorem ofList_lookup_some {K V : Type} [DecidableEq K] {k : K} {v : V} :
    ∀ (l : List (K × V)), (l.map (·.1)).Nodup → (k, v) ∈ l → GMap.ofList l !! k = some v
  | [], _, h => by cases h
  | (k', v') :: l, hn, h => by
    show (GMap.insert k' v' (GMap.ofList l)) !! k = some v
    rcases List.mem_cons.1 h with e | h
    · cases e; exact GMap.lookup_insert _ _ _
    · have hk : k' ≠ k := by
        intro e; subst e
        exact (List.nodup_cons.1 hn).1 (List.mem_map.2 ⟨_, h, rfl⟩)
      rw [GMap.lookup_insert_ne _ _ hk]
      exact ofList_lookup_some l (List.nodup_cons.1 hn).2 h

theorem bootJm_keys (V : Hist) (jr : Ino) (r : GoString) :
    (((bootWals V.now jr).map (fun p => (r ++ go!"/" ++ p.1, p.2))).map (·.1)).Nodup := by
  rw [List.map_map]
  apply List.Nodup.mapOnW (bootWals_nodup V.now jr)
  intro x hx y hy e
  simp only [Function.comp] at e
  have e1 := List.append_cancel_left e
  obtain ⟨a, J⟩ := x
  obtain ⟨a', J'⟩ := y
  simp only at e1
  subst e1
  rw [bootWals_fun hx hy]

theorem bootJm_lookup {V : Hist} {jr : Ino} {r : GoString} (dir nm : GoString) (J : Ino)
    (hin : InArea r dir nm) (he : V.now.entry jr nm = some (.dir J)) : bootJm V jr r !! dir = some J := by
  obtain ⟨hnm, rfl⟩ := hin
  exact ofList_lookup_some _ (bootJm_keys V jr r)
    (List.mem_map.2 ⟨(nm, J), mem_bootWals.2 ⟨hnm, he⟩, rfl⟩)

/-- **A WAL found has a layout of its name** (the start's `WalsStart`, the area `r`). -/
theorem bootWals_lay {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {m : Tree} (hst : WalsStart C Mr R jr s Ls m) {nm : GoString} {J : Ino}
    (h : (nm, J) ∈ bootWals m jr) : ∃ dir lay, Ls !! dir = some lay ∧ lay.nm = nm := by
  obtain ⟨hnm, he⟩ := mem_bootWals.1 h
  have hin : InArea s.area (s.area ++ go!"/" ++ nm) nm := ⟨hnm, rfl⟩
  cases hd : s.wal !! (s.area ++ go!"/" ++ nm) with
  | none => rw [hst.2.2.1 _ _ hin hd] at he; cases he
  | some d =>
    obtain ⟨lay, nm', hl, hin', -, hnm', -⟩ := hst.1 _ d hd
    refine ⟨_, lay, hl, ?_⟩
    rw [hnm']
    exact (List.append_cancel_left hin'.2).symm

/-- The area's claim is no WAL directory's claim. -/
theorem bootAreaCl_not {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {V : Hist} (hst : WalsStart C Mr R jr s Ls V.now) :
    ¬ (WalDirClaimOf Ls (bootAreaCl V jr) ∨ NameClaimOf jr Ls (bootAreaCl V jr)) := by
  rintro (⟨dir, lay, hl, hj, -⟩ | ⟨-, dir, lay, hl, hN⟩)
  · exact (hst.2.2.2.2.2 dir lay hl).1 hj.symm
  · unfold bootAreaCl bootN at hN; cases hN

end pure


section boot
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

/-- A map from a list of distinct keys. -/
theorem bigSepM_ofList_intro {K V : Type} [DecidableEq K] (Φ : K → V → IProp GF) :
    ∀ (l : List (K × V)), (l.map (·.1)).Nodup →
      ([∗list] x ∈ l, Φ x.1 x.2) ⊢ [∗map] k ↦ v ∈ GMap.ofList l, Φ k v
  | [], _ => by
    refine (BigSepL.bigSepL_nil.1).trans ?_
    exact BigSepM.bigSepM_empty.2
  | (k, v) :: l, hn => by
    have hk : GMap.ofList l !! k = none :=
      ofList_lookup_none k l (List.nodup_cons.1 hn).1
    refine (BigSepL.bigSepL_cons.1).trans ?_
    refine (sep_mono_right (bigSepM_ofList_intro Φ l (List.nodup_cons.1 hn).2)).trans ?_
    exact (BigSepM.bigSepM_insert (m := GMap.ofList l) (i := k) (x := v) (Φ := Φ) hk).2

/-- A big separating conjunction of updates, each under a persistent resource. -/
theorem bigSepL_fupd_wand [L : GooseLocalGS GF] {A : Type} (P : IProp GF) [Persistent P] (Φ Ψ1 Ψ : A → IProp GF)
    (E : CoPset) : ∀ (l : List A), (∀ x ∈ l, ⊢ P -∗ Φ x -∗ Ψ1 x ={E}=∗ Ψ x) →
      ⊢ P -∗ ([∗list] x ∈ l, Φ x) -∗ ([∗list] x ∈ l, Ψ1 x) ={E}=∗ [∗list] x ∈ l, Ψ x
  | [], _ => by
    iintro #HP - -
    imodintro
    iapply BigSepL.bigSepL_nil.2; iempintro
  | x :: l, h => by
    iintro #HP H1 H2
    icases BigSepL.bigSepL_cons.1 $$ H1 with ⟨H1, Hr1⟩
    icases BigSepL.bigSepL_cons.1 $$ H2 with ⟨H2, Hr2⟩
    imod h x (List.mem_cons_self ..) $$ HP H1 H2 with Hx
    imod bigSepL_fupd_wand (L := L) P Φ Ψ1 Ψ E l (fun y hy => h y (List.mem_cons_of_mem _ hy)) $$ HP Hr1 Hr2
      with Hr
    imodintro
    iapply BigSepL.bigSepL_cons.2
    iframe Hx Hr

/-- **The crash boot's files, by directory**: the WALs' (the temporary directories' probes dropped:
`walAreaRes` holds no file since 2026-11-22). -/
theorem bootFiles_split (L : GooseLocalGS GF) (R : Roots) (m : Tree) (jr : Ino) :
    ([∗list] i ∈ bootFiles m jr, trFile (hG := ⟨G, L⟩) i False) ⊢
      ([∗list] p ∈ bootWals m jr, [∗list] i ∈ dirBootFiles m p.1 p.2, trFile (hG := ⟨G, L⟩) i False) := by
  classical
  let F : GoString → Node → IProp GF := fun a n => iprop([∗list] i ∈ (match n with
    | .dir J => dirBootFiles m a J
    | .file _ => []), trFile (hG := ⟨G, L⟩) i False)
  have e : ([∗list] i ∈ bootFiles m jr, trFile (hG := ⟨G, L⟩) i False) =
      [∗list] an ∈ GMap.toList (entsOf m jr), F an.1 an.2 := by
    unfold bootFiles
    rw [BigSepL.bigSepL_flatMap]
    rfl
  rw [e]
  refine (BigSepL.bigSepL_mono (Ψ := fun _ an => iprop(if walNameOk an.1 then F an.1 an.2 else emp))
      (fun {k an} _ => ?_)).trans ?_
  · by_cases hw : walNameOk an.1
    · rw [if_pos hw]
    · rw [if_neg hw]; exact Affine.affine
  · refine (bigSepM_sub_list (entsOf m jr) (fun a n => if walNameOk a then F a n else emp)
      (bootWals m jr) Prod.fst (fun p => .dir p.2) (bootWn_nodup m jr) (fun p hp => by
        rw [entsOf_lookup]; exact (mem_bootWals.1 hp).2)).trans (BigSepL.bigSepL_mono
        (fun {k p} hk => ?_))
    have hp := List.mem_of_getElem? hk
    show (if walNameOk p.1 then F p.1 (.dir p.2) else emp) ⊢ _
    rw [if_pos (mem_bootWals.1 hp).1]

/-- **The crash boot of the WAL area `r`** (the root directory `jr`), at the new generation's shared
mode's switch (`V` the crashed history, nothing logged), from `walInv_crash`'s outputs: the WAL's area
resources; back, the area's claim on its names that are no `AreaSlot` holding an entry and the whole
claim of every directory not taken (`bootRest`). -/
theorem walBootCrash (C : WalCodec) (hC : C.Ok) (Mr : WalMarshal) (L : GooseLocalGS GF)
    (W : WalGS GF) (R : Roots) (jr : Ino) (r : GoString) (s : AbsDiskState) (V : Hist)
    (hV : V.2 = []) (hR : RootsOk R) (hr : (r, jr) ∈ R) (hwf : TreeWf R V.now)
    (hbd : WalsBounded s) (hdr : DirsRoots R s) (hfo : BootFo V.now jr)
    (hrb : ReceiptBoundLe GF (2 ^ 62)) (henc : ∀ hs : HardStateM, (Mr.encState hs).length < 2 ^ 32)
    (hWR : W.roots = R) (E : CoPset) (hE : ↑osShN ⊆ E) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osAboveInv (L := L) -∗ walStart L W C Mr R jr r s V.now -∗
      ([∗list] i ∈ bootFiles V.now jr, trFile (hG := ⟨G, L⟩) i False) -∗
      ([∗list] j ∈ (GMap.toList V.now).map (·.1),
        osNames (L := L) j (.except []) (DFrac.own 1) (namesOf V j (.except []))) ={E}=∗
      walAreaOk (L := L) (W := W) C Mr R jr r ∗ walAreaRes (L := L) (W := W) jr ∗
      osNames (L := L) jr ((NameSet.except []).inter (bootOthers V.now jr)) (DFrac.own 1)
        (namesOf V jr ((NameSet.except []).inter (bootOthers V.now jr))) ∗
      [∗list] j ∈ bootRest V.now jr,
        osNames (L := L) j (.except []) (DFrac.own 1) (namesOf V j (.except [])) := by
  classical
  iintro #Hos #Hsh #Hab Hst Hfiles Hall
  -- the claims: the area's, the WALs', those under an `nm.<sfx>`, the rest
  ihave Hall := (BigSepL.bigSepL_perm (Φ := fun j => osNames (L := L) j (.except []) (DFrac.own 1)
    (namesOf V j (.except []))) (dom_perm_taken hwf hr)).1 $$ Hall
  icases BigSepL.bigSepL_append.1 $$ Hall with ⟨Ht, Hrest⟩
  have eT : bootTaken V.now jr =
      jr :: ((bootWals V.now jr).map (·.2) ++ (bootSubs V.now jr).map (·.2)) := rfl
  rw [eT]
  icases BigSepL.bigSepL_cons.1 $$ Ht with ⟨Hjr, Ht⟩
  icases BigSepL.bigSepL_append.1 $$ Ht with ⟨Hw, Hs⟩
  rw [BigSepL.bigSepL_map, BigSepL.bigSepL_map]
  -- the files
  ihave Hwf := bootFiles_split L R V.now jr $$ Hfiles
  -- each WAL directory
  imod bigSepL_fupd_wand (L := L) (osSharedInv (L := L) R)
    (fun p => osNames (L := L) p.2 (.except []) (DFrac.own 1) (namesOf V p.2 (.except [])))
    (fun p => iprop([∗list] i ∈ dirBootFiles V.now p.1 p.2, trFile (hG := ⟨G, L⟩) i False))
    (fun p => iprop(osNames (L := L) p.2 (.except walTmps) (DFrac.own 1) (namesOf V p.2 (.except walTmps)) ∗
      (walTmpsRes (hG := ⟨G, L⟩) p.2 ∗ walTmpsHalf (hG := ⟨G, L⟩) p.2) ∗
      walOthers (L := L) [] p.2 (restrictN (.except walTmps) (entsOf V.now p.2))))
    E (bootWals V.now jr) (fun p hp => by
      obtain ⟨hnm, he⟩ := mem_bootWals.1 hp
      exact walDir_boot L R V hV p.2 p.1 hnm (hfo _ _ hnm he) E hE) $$ Hsh Hw Hwf with Hw
  icases BigSepL.bigSepL_sep_eqv.1 $$ Hw with ⟨Hwc, Hw⟩
  icases BigSepL.bigSepL_sep_eqv.1 $$ Hw with ⟨Hwt, Hwo⟩
  -- the area's claim: the names given back, the WALs' names, the rest
  imod osNames_split R jr (.except []) (bootOthers V.now jr) _ hE $$ Hsh Hjr with ⟨Hoth, Har⟩
  rw [namesOf_restrict V jr (.except []) ((NameSet.except []).inter (bootOthers V.now jr))
      (fun b _ => by simp [NameSet.Mem]),
    namesOf_restrict V jr (.except []) ((NameSet.except []).diff (bootOthers V.now jr))
      (fun b _ => by simp [NameSet.Mem])]
  have ed : (NameSet.except []).diff (bootOthers V.now jr) = .except (bootOthers V.now jr) := rfl
  rw [ed]
  imod osNames_split_only L R V jr E hE (bootWn V.now jr) (bootOthers V.now jr) (bootWn_nodup V.now jr)
    (fun b hb ho => by
      obtain ⟨J, hJ⟩ := mem_bootWn.1 hb
      exact (mem_bootOthers.1 ho).1 (areaSlot_walName (mem_bootWals.1 hJ).1)) $$ Hsh Har
    with ⟨Har, Hnc⟩
  -- the area's path
  imod osPathS_root R r jr (DFrac.own 1) hr hE $$ Hsh with Hsp
  -- the new invariant
  imod walInv_alloc (W := W) C hC Mr L R jr r s V (bootCl V jr) hV (bootCl_hcl V jr) (bootCl_area V jr)
    (fun nm J h he => ⟨_, bootCl_dirs h he⟩) (bootCl_dirs1 hwf hr) hWR
    (dirsOk_roots hR hdr _ 0) (dirsAvoid_roots hR hdr jr) (bootJm V jr r)
    (fun dir nm J hin he => bootJm_lookup dir nm J hin he) (fun nm J h he => ⟨_, bootCl_names h he⟩)
    (bootCl_nok hwf) hbd hdr
    (fun nm J h he b J' _ hd => by obtain ⟨i, hi⟩ := hfo nm J h he b _ hd; cases hi) 1 E $$ Hst [Har Hwc Hnc] [Hwt] Hsp [Hwo]
    with ⟨#Hinv, %Ls, %hLs, Hnw, %hnc, Hcl⟩
  · unfold osClaims bootCl
    rw [List.map_cons, List.map_append]
    dsimp only [bootAreaCl, bootN]
    iapply BigSepL.bigSepL_cons.2
    isplitl [Har]
    · iexact Har
    iapply BigSepL.bigSepL_append.2
    unfold bootWalCls bootNameCls
    rw [List.map_map, List.map_map, BigSepL.bigSepL_map, BigSepL.bigSepL_map]
    dsimp only [Function.comp]
    unfold bootWn
    rw [BigSepL.bigSepL_map]
    iframe Hwc Hnc
  · unfold bootJm
    iapply bigSepM_ofList_intro
    · exact bootJm_keys V jr r
    rw [BigSepL.bigSepL_map]
    iexact Hwt
  · iintro %Ls %hLs
    unfold walOthersL bootCl
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · rw [if_neg (fun h => bootAreaCl_not hLs (.inl h))]
      iempintro
    iapply BigSepL.bigSepL_append.2
    isplitl [Hwo]
    · unfold bootWalCls
      rw [BigSepL.bigSepL_map]
      have hwo : ([∗list] p ∈ bootWals V.now jr,
          walOthers (L := L) [] p.2 (restrictN (.except walTmps) (entsOf V.now p.2))) ⊢
          [∗list] p ∈ bootWals V.now jr,
            if WalDirClaimOf Ls (p.2, NameSet.except walTmps, namesOf V p.2 (.except walTmps)) then
              walOthers (L := L) [] p.2 (namesOf V p.2 (.except walTmps)).cur else emp := by
        refine BigSepL.bigSepL_mono (fun {k p} _ => ?_)
        by_cases hc : WalDirClaimOf Ls (p.2, NameSet.except walTmps, namesOf V p.2 (.except walTmps))
        · rw [if_pos hc]; exact .rfl
        · rw [if_neg hc]; exact Affine.affine
      iapply hwo
      iexact Hwo
    · have hnc : (emp : IProp GF) ⊢ [∗list] c ∈ bootNameCls V jr,
          if WalDirClaimOf Ls c then walOthers (L := L) [] c.1 c.2.2.cur else emp := by
        refine (BigSepL.bigSepL_emp (l := bootNameCls V jr)).2.trans
          (BigSepL.bigSepL_mono (fun {k c} hk => ?_))
        obtain ⟨nm, -, e⟩ := mem_bootNameCls.1 (List.mem_of_getElem? hk)
        rw [e, if_neg (fun ⟨_, _, _, _, X, hX, _⟩ => by cases hX)]
      iapply hnc
      iempintro
  -- the area claim's half comes back
  unfold bootCl
  icases BigSepL.bigSepL_cons.1 $$ Hcl with ⟨Hac, -⟩
  rw [if_neg (bootAreaCl_not hLs)]
  dsimp only [bootAreaCl]
  imodintro
  iframe Hoth Hrest
  isplitr
  · unfold walAreaOk
    iframe Hinv Hos Hsh Hab
    ipureintro; exact ⟨hrb, henc⟩
  unfold walAreaRes
  iexists bootN V.now jr, namesOf V jr (bootN V.now jr), bootCls V jr,
    nameClaimsOf jr Ls ((jr, bootN V.now jr, namesOf V jr (bootN V.now jr)) ::
      (bootWalCls V jr ++ bootNameCls V jr))
  iframe Hac Hnw
  isplitr
  · ipureintro
    intro nm hnm
    rcases bootN_walName (m := V.now) (jr := jr) hnm with h | h
    · exact .inl h
    · obtain ⟨J, hJ⟩ := mem_bootWn.1 h
      exact .inr ((hnc nm).2 (bootWals_lay hLs hJ))
  isplitr
  · ipureintro; exact fun nm sfx h => bootN_sfx nm sfx h
  isplitl [Hs]
  · unfold areaCls
    unfold osClaims bootCls
    rw [List.map_map, BigSepL.bigSepL_map]
    dsimp only [Function.comp]
    iexact Hs
  isplitr
  · ipureintro; exact fun b hb hnw _ => bootCls_subCover hwf hr b hb hnw
  · ipureintro; exact fun nm _ => bootCls_ranked hwf jr (tmpName nm)

end boot

end WalFs
end EtcdGrove
end Perennial

end
