/- Lean-first (no Rocq counterpart).

# The WAL's first boot (`notes/wal-fsext-w4c-plan.md`, §3, "W4c U3 log")

`walBoot0`: from the tree's shared view at the first start (`osShared`, `fs_start`: the shared invariant,
a whole claim on all names of every directory of the boot tree `V.now`, nothing logged), what a WAL
client needs to call `Create`, `Open`, ...: the area's `walAreaOk` (the WAL invariant, allocated by
`walInv_alloc` over `walStart_boot0`), the program's `walAreaRes`, the lock and crash tokens, the
WAL's past (`walPast`, for `dirDurable r`) and the program's (empty) WAL map (`walOwn ∅`, for a client's
`walAbsent`); the claims the WAL does not take go back to the program
(the area's names holding an entry, and every other directory's claim).

Its premises, each a world premise of a closed theorem's first boot:
* `hV`: nothing logged (`fs_start`'s `osShared`);
* `hR`, `hr`: the roots well formed (`FsInit`) and **the area `r` one of them** (its directory `jr`):
  the area must be durable for `Create` (`dirDurable r`), and no `fsExt` step makes a directory durable
  (`BootPure`);
* `Js`, `hjr`: the directories whose whole claims the caller holds (the boot tree's, from `osShared`, or
  what an earlier area's boot left: `walBoot0s`), the area's among them;
* `hslots`: **no entry of the area at a name a WAL function may change** (`AreaSlot`: a WAL name `nm`,
  no `.` or `/`, or `nm.<sfx>`: every name not starting with `.`), so no WAL is found (as
  `absDiskInitOk`'s `s.wal = ∅`), and the program's part of the area (`walAreaRes`) holds no entry:
  nothing for `SubCover` or `ClRanked` to say;
* `hrb`, `henc`: `walAreaOk`'s pure parts, the receipts' bound (the adequacy theorem's constant) and the
  marshaller's law (U4).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.BootStart0
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateDefs

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]

/-- The names of the area holding an entry in the tree `m` (the program keeps them at the first
boot). -/
def areaOthers (m : Tree) (jr : Ino) : List GoString := (GMap.toList (entsOf m jr)).map (·.1)

theorem mem_areaOthers {m : Tree} {jr : Ino} {b : GoString} (h : m.entry jr b = none) :
    b ∉ areaOthers m jr := by
  intro hb
  obtain ⟨⟨b', v⟩, hm, rfl⟩ := List.mem_map.1 hb
  have := (GMap.mem_toList _ _ _).1 hm
  rw [entsOf_lookup] at this
  simp only at h
  rw [h] at this; cases this

/-- The area's claim on the names holding no entry knows none. -/
theorem areaCur_none (m : Tree) (jr : Ino) (b : GoString) :
    restrictN (.except (areaOthers m jr)) (entsOf m jr) !! b = none := by
  by_cases hb : (NameSet.except (areaOthers m jr)).Mem b
  · rw [restrictN_lookup _ _ _ hb]
    cases he : entsOf m jr !! b with
    | none => rfl
    | some v =>
      exfalso; apply hb
      exact List.mem_map.2 ⟨(b, v), (GMap.mem_toList _ _ _).2 he, rfl⟩
  · exact restrictN_lookup_not _ _ _ hb

/-- A WAL name is an area slot. -/
theorem areaSlot_of_walName {nm : GoString} (h : walNameOk nm) : AreaSlot nm := ⟨nm, h, Or.inl rfl⟩

/-- A name `nm.<sfx>` of a WAL name is an area slot. -/
theorem areaSlot_sfx {nm : GoString} (h : walNameOk nm) (sfx : GoString) :
    AreaSlot (nm ++ go!"." ++ sfx) := ⟨nm, h, Or.inr ⟨sfx, rfl⟩⟩

end pure

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

/-- **The first boot of the WAL area `r`** (the root directory `jr`), at the shared mode's switch:
the WAL's area resources, its tokens and past; back, the area's claim on its names holding an entry
and every other directory's whole claim. -/
theorem walBoot0 (hPre : AbsDiskGpreS GF) (C : WalCodec) (hC : C.Ok) (Mr : WalMarshal)
    (L : GooseLocalGS GF) (R : Roots) (jr : Ino) (r : GoString) (V : Hist) (hV : V.2 = [])
    (hR : RootsOk R) (hr : (r, jr) ∈ R) (Js : List Ino) (hjr : jr ∈ Js)
    (hslots : ∀ b, AreaSlot b → V.now.entry jr b = none)
    (hrb : ReceiptBoundLe GF (2 ^ 62)) (henc : ∀ hs : HardStateM, (Mr.encState hs).length < 2 ^ 32)
    (E : CoPset) (hE : ↑osShN ⊆ E) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osAboveInv (L := L) -∗
      ([∗list] j ∈ Js,
        osNames (L := L) j (.except []) (DFrac.own 1) (namesOf V j (.except []))) ={E}=∗
      ∃ W : WalGS GF, walAreaOk (L := L) (W := W) C Mr R jr r ∗ walAreaRes (L := L) (W := W) jr ∗
        walUnlockedTok (W := W) ∗ walCrashTok (W := W) ∗ walPast (W := W) (walBoot0St r) ∗
        walOwn (W := W) ∅ ∗
        osNames (L := L) jr ((NameSet.except []).inter (areaOthers V.now jr)) (DFrac.own 1)
          (namesOf V jr ((NameSet.except []).inter (areaOthers V.now jr))) ∗
        [∗list] j ∈ Js.erase jr,
          osNames (L := L) j (.except []) (DFrac.own 1) (namesOf V j (.except [])) := by
  iintro #Hos #Hsh #Hab Hall
  -- the area's claim, out of the others
  have hmem : jr ∈ Js := hjr
  ihave Hall := (BigSepL.bigSepL_perm (Φ := fun j => osNames (L := L) j (.except []) (DFrac.own 1)
    (namesOf V j (.except []))) (List.perm_cons_erase hmem)).1 $$ Hall
  icases Hall with ⟨Hjr, Hrest⟩
  imod osNames_split R jr (.except []) (areaOthers V.now jr) _ hE $$ Hsh Hjr with ⟨Hoth, Har⟩
  rw [namesOf_restrict V jr (.except []) ((NameSet.except []).inter (areaOthers V.now jr))
      (fun b _ => by simp [NameSet.Mem]),
    namesOf_restrict V jr (.except []) ((NameSet.except []).diff (areaOthers V.now jr))
      (fun b _ => by simp [NameSet.Mem])]
  -- the WAL's start and the area's path
  have hnone : ∀ nm, walNameOk nm → V.now.entry jr nm = none :=
    fun nm h => hslots nm (areaSlot_of_walName h)
  imod walStart_boot0 hPre L C Mr R jr r V.now hR hr hnone with ⟨%W, %hWR, Hst, #Hp, Hu, Hc, Hown⟩
  imod osPathS_root R r jr (DFrac.own 1) hr hE $$ Hsh with Hsp
  -- the invariant's claims: the area's names holding no entry
  let N : NameSet := .except (areaOthers V.now jr)
  let cl : List Claim := [(jr, N, namesOf V jr N)]
  rw [show (NameSet.except []).diff (areaOthers V.now jr) = N from rfl]
  have hnot : ∀ nm, walNameOk nm → N.Mem nm := fun nm h => mem_areaOthers (hnone nm h)
  have hdir : ∀ nm J, walNameOk nm → V.now.entry jr nm = some (.dir J) → False := by
    intro nm J h he; rw [hnone nm h] at he; cases he
  imod walInv_alloc (W := W) C hC Mr L R jr r (walBoot0St r) V cl hV
    (fun c hc => by rw [List.mem_singleton] at hc; subst hc; rfl)
    (fun nm h => ⟨N, namesOf V jr N, List.mem_singleton_self _, hnot nm h⟩)
    (fun nm J h he => (hdir nm J h he).elim) (fun nm J _ h he => (hdir nm J h he).elim) hWR
    (dirsOk_roots hR (walBoot0St_dirsRoots hr) cl 0) (dirsAvoid_roots hR (walBoot0St_dirsRoots hr) jr)
    ∅ (fun dir nm J hin he => (hdir nm J hin.1 he).elim) (fun nm J h he => (hdir nm J h he).elim)
    (fun b h hc => by simp [cl, N] at hc) (walBoot0St_bounded r) (walBoot0St_dirsRoots hr)
    (fun nm J h he => (hdir nm J h he).elim) 1 E
    $$ Hst [Har] [] Hsp [] with ⟨#Hinv, %Ls, %hLs, Hnw, -, Hcl⟩
  · unfold osClaims
    simp only [cl, List.map_cons, List.map_nil]
    iapply BigSepL.bigSepL_cons.2
    iframe Har
    iapply BigSepL.bigSepL_nil.2; iempintro
  · iapply BigSepM.bigSepM_empty.2; iempintro
  · iintro %Ls %hLs
    unfold walOthersL
    simp only [cl]
    have hw : ¬ WalDirClaimOf Ls (jr, N, namesOf V jr N) := by
      rintro ⟨dir, lay, hl, -⟩
      rw [hLs.2.1 dir (by simp [walBoot0St])] at hl; cases hl
    iapply BigSepL.bigSepL_cons.2
    rw [if_neg hw]
    isplitl
    · iempintro
    · iapply BigSepL.bigSepL_nil.2; iempintro
  -- no layout: the area claim's half is the program's
  have hLs0 : ∀ dir, Ls !! dir = none := fun dir => hLs.2.1 dir (by simp [walBoot0St])
  have hnc : nameClaimsOf jr Ls cl = [] := by
    apply List.eq_nil_iff_forall_not_mem.2
    intro nm hnm
    obtain ⟨c, -, ⟨-, dir, lay, hl, -⟩, -⟩ := mem_nameClaimsOf.1 hnm
    rw [hLs0 dir] at hl; cases hl
  rw [hnc]
  have hc : ¬ (WalDirClaimOf Ls (jr, N, namesOf V jr N) ∨ NameClaimOf jr Ls (jr, N, namesOf V jr N)) := by
    rintro (⟨dir, lay, hl, -⟩ | ⟨-, dir, lay, hl, -⟩) <;> (rw [hLs0 dir] at hl; cases hl)
  simp only [cl]
  icases Hcl with ⟨Hcl, -⟩
  rw [if_neg hc]
  imodintro
  iexists W
  iframe Hu Hc Hp Hown Hoth Hrest
  isplitr
  · unfold walAreaOk
    iframe Hinv Hos Hsh Hab
    ipureintro; exact ⟨hrb, henc⟩
  unfold walAreaRes
  iexists N, namesOf V jr N, [], []
  iframe Hcl Hnw
  have hcur : ∀ b, (namesOf V jr N).cur !! b = none := fun b => by
    show restrictN N (entsOf V.now jr) !! b = none
    exact areaCur_none V.now jr b
  isplitr
  · ipureintro; exact fun nm h => Or.inl (hnot nm h)
  isplitr
  · ipureintro; exact fun nm sfx h => mem_areaOthers (hslots _ (areaSlot_sfx h sfx))
  isplitr
  · unfold areaCls osClaims
    simp only [List.map_nil]
    iapply BigSepL.bigSepL_nil.2; iempintro
  isplitr
  · ipureintro
    intro b _ _ _ J hJ
    rw [hcur b] at hJ; cases hJ
  · ipureintro
    intro nm _
    exact ⟨fun _ => 0, fun c hc => by simp [clOf] at hc⟩

/-- **The first boot of several WAL areas, one ghost generation each** (`notes/wal-link-scope.md` §4.3, L4:
one `WalGS` per area, its own lock token `walUnlockedTok` and crash token): `walBoot0` for each area `(r, jr)`
of `As` in turn, each in a root of `R`, their directories distinct and among the claims held (`Js`); back,
each area's claim on its names holding an entry, and the claims of the directories no area took. -/
theorem walBoot0s (hPre : AbsDiskGpreS GF) (C : WalCodec) (hC : C.Ok) (Mr : WalMarshal)
    (L : GooseLocalGS GF) (R : Roots) (V : Hist) (hV : V.2 = []) (hR : RootsOk R)
    (hrb : ReceiptBoundLe GF (2 ^ 62)) (henc : ∀ hs : HardStateM, (Mr.encState hs).length < 2 ^ 32)
    (E : CoPset) (hE : ↑osShN ⊆ E) :
    ∀ (As : List (GoString × Ino)) (Js : List Ino), (∀ a ∈ As, a ∈ R) → (As.map (·.2)).Nodup →
      (∀ a ∈ As, a.2 ∈ Js) → (∀ a ∈ As, ∀ b, AreaSlot b → V.now.entry a.2 b = none) →
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osAboveInv (L := L) -∗
      ([∗list] j ∈ Js,
        osNames (L := L) j (.except []) (DFrac.own 1) (namesOf V j (.except []))) ={E}=∗
      ([∗list] a ∈ As, ∃ W : WalGS GF, walAreaOk (L := L) (W := W) C Mr R a.2 a.1 ∗
          walAreaRes (L := L) (W := W) a.2 ∗ walUnlockedTok (W := W) ∗ walCrashTok (W := W) ∗
          walPast (W := W) (walBoot0St a.1) ∗ walOwn (W := W) ∅ ∗
          osNames (L := L) a.2 ((NameSet.except []).inter (areaOthers V.now a.2)) (DFrac.own 1)
            (namesOf V a.2 ((NameSet.except []).inter (areaOthers V.now a.2)))) ∗
        [∗list] j ∈ As.foldl (fun l a => l.erase a.2) Js,
          osNames (L := L) j (.except []) (DFrac.own 1) (namesOf V j (.except [])) := by
  intro As
  induction As with
  | nil =>
    intro Js _ _ _ _
    iintro _ _ _ Hall
    imodintro
    simp only [List.foldl_nil]
    iframe Hall
    iapply BigSepL.bigSepL_nil.2; iempintro
  | cons a As ih =>
    intro Js hAR hnd hJ hsl
    have hnd' : (As.map (·.2)).Nodup := (List.nodup_cons.1 hnd).2
    have hJ' : ∀ a' ∈ As, a'.2 ∈ Js.erase a.2 := by
      intro a' ha'
      have hne : a'.2 ≠ a.2 := by
        intro h
        have hm := List.mem_map_of_mem (f := fun x : GoString × Ino => x.2) ha'
        rw [h] at hm
        exact (List.nodup_cons.1 hnd).1 hm
      exact (List.mem_erase_of_ne hne).2 (hJ a' (List.mem_cons_of_mem _ ha'))
    iintro #Hos #Hsh #Hab Hall
    imod walBoot0 hPre C hC Mr L R a.2 a.1 V hV hR (hAR a List.mem_cons_self) Js
      (hJ a List.mem_cons_self) (hsl a List.mem_cons_self) hrb henc E hE $$ Hos Hsh Hab Hall
      with ⟨%W, Hok, Hres, Hu, Hc, Hp, Hown, Hoth, Hrest⟩
    imod ih (Js.erase a.2) (fun a' h => hAR a' (List.mem_cons_of_mem _ h)) hnd' hJ'
      (fun a' h => hsl a' (List.mem_cons_of_mem _ h)) $$ Hos Hsh Hab Hrest with ⟨Has, Hrest⟩
    imodintro
    simp only [List.foldl_cons]
    iframe Hrest
    iapply BigSepL.bigSepL_cons.2
    iframe Has
    iexists W
    iframe

end boot

end WalFs
end EtcdGrove
end Perennial

end
