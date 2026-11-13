/- Lean-first (no Rocq counterpart).

# `Create`'s client update at the rename (W4, `notes/wal-fsext-plan.md`, "W4 implementation log")

`walCreate_osAUnc`: the atomic update `Create` gives `os.Rename.specDirSnc` for `renameWAL`'s rename of
`nm.tmp` (the directory `J`, the fresh WAL's one segment `g` in it, synced) onto the WAL-less name `nm`
of the area `r`, in the area claim `(jr, N, h)` that the program's `walCreating dir N h` token names.

* *Opening* (with the generation's `notCrashed`): opens `walInv`, finds the claim among the
  invariant's (`CreatingOk`: once in its claims), hands out the invariant's half of it, and opens the
  client's update (`walAbsent dir`).
* *Abort*, or a commit with no effect: both closed again; the program's resources back.
* *Commit*: the rename logged at `x` by a call begun at `s0 ≥ lb` (`renDirOut`). The client's update
  commits to `walDiskAt dir (walDurFresh md)` (the real WAL state `createSt`, `walGhost_upd`); the
  invariant takes the logged claim's half, half of `J`'s claim, the segment's halves (its inode none of
  the layouts', `laysResF_ino_ne`), the new layout `lay`, and the creating entry is deleted; its pure
  facts are `walsOk_create`'s. The program gets the client's `Q`, the segment's other halves, and a past
  state with the fresh WAL in `dir`.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateAuLemmas
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateDefs

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- Replacing a claim found once. -/
theorem replClaim_split {c c' : Claim} {l1 l2 : List Claim} (h1 : c ∉ l1) (h2 : c ∉ l2) :
    replClaim c c' (l1 ++ c :: l2) = l1 ++ c' :: l2 := by
  classical
  unfold replClaim
  rw [List.map_append, List.map_cons, if_pos rfl]
  have e : ∀ l : List Claim, c ∉ l → l.map (fun x => if x = c then c' else x) = l := by
    intro l hl
    induction l with
    | nil => rfl
    | cons y ys ih =>
      rw [List.map_cons, if_neg (fun (e : y = c) => hl (e ▸ List.mem_cons_self ..)),
        ih (fun hm => hl (List.mem_cons_of_mem _ hm))]
  rw [e l1 h1, e l2 h2]

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

theorem osClaims_append (l1 l2 : List (Claim × DFrac)) :
    osClaims L (l1 ++ l2) ⊣⊢ osClaims L l1 ∗ osClaims L l2 := by
  unfold osClaims; exact BigSepL.bigSepL_append

/-- The claims with one taken out (all at fraction `dq`). -/
theorem osClaims_split (l1 l2 : List Claim) (c : Claim) (dq : DFrac) :
    osClaims L ((l1 ++ c :: l2).map (fun c => (c, dq))) ⊣⊢
      osClaims L (l1.map (fun c => (c, dq))) ∗ osNames (L := L) c.1 c.2.1 dq c.2.2 ∗
        osClaims L (l2.map (fun c => (c, dq))) := by
  rw [List.map_append, List.map_cons]
  refine (osClaims_append (L := L) _ _).trans ?_
  exact sep_congr .rfl (osClaims_cons L _ _)

/-- The claims after the commit: the replaced one's new fraction, `J`'s appended. -/
theorem osClaims_create (l1 l2 : List Claim) (c c' cJ : Claim) (dq : DFrac) (hl1 : c ∉ l1)
    (hl2 : c ∉ l2) :
    osClaims L (l1.map (fun c => (c, dq))) ∗ osNames (L := L) c'.1 c'.2.1 dq c'.2.2 ∗
        osClaims L (l2.map (fun c => (c, dq))) ∗ osNames (L := L) cJ.1 cJ.2.1 dq cJ.2.2 ⊢
      osClaims L ((replClaim c c' (l1 ++ c :: l2) ++ [cJ]).map (fun c => (c, dq))) := by
  rw [replClaim_split hl1 hl2, List.map_append, List.map_cons, List.map_nil]
  iintro ⟨H1, Hc, H2, HJ⟩
  iapply (osClaims_append (L := L) _ _).2
  isplitl [H1 Hc H2]
  · iapply (osClaims_split (L := L) _ _ _ _).2
    iframe H1 Hc H2
  · iapply (osClaims_cons L _ _).2
    iframe HJ
    unfold osClaims
    iapply BigSepL.bigSepL_nil.2
    iempintro

/-- The creating token's entry in the authority. -/
theorem walCreating_lookup (CR : GMap GoString (NameSet × NamesH)) (dir : GoString) (N : NameSet)
    (h : NamesH) :
    ⊢ walCreatingAuth (W := W) CR -∗ walCreating (W := W) dir N h -∗
      ⌜CR !! dir = some (N, h)⌝ ∗ walCreatingAuth (W := W) CR ∗ walCreating (W := W) dir N h := by
  unfold walCreatingAuth walCreating
  letI := walAllG (W := W)
  iintro Ha Ht
  icases ghost_map_lookup $$ Ha Ht with %H
  iframe Ha Ht
  ipureintro; exact H

/-- Deleting the creating token's entry. -/
theorem walCreating_delete (CR : GMap GoString (NameSet × NamesH)) (dir : GoString) (N : NameSet)
    (h : NamesH) :
    ⊢ walCreatingAuth (W := W) CR -∗ walCreating (W := W) dir N h ==∗
      walCreatingAuth (W := W) (GMap.delete dir CR) := by
  unfold walCreatingAuth walCreating
  letI := walAllG (W := W)
  iintro Ha Ht
  iapply ghost_map_delete $$ Ha Ht

end iris

section au
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [W : WalGS GF]

/-- **What `Create` holds for the rename's update**: the creating token, the client's update, and what
the invariant takes at the commit: half of `J`'s claim, the segment `g` whole (its `OsMeta`, its
bytes). -/
def walCreateP (dir : GoString) (N : NameSet) (h : NamesH) (md : List w8) (Q : IProp GF)
    (J : Ino) (X : List GoString) (hJ : NamesH) (g : SegG) : IProp GF :=
  iprop(walCreating (W := W) dir N h ∗
    (AU <{ walAbsent (W := W) dir }> @ walAuMask, ∅ <{ walDiskAt (W := W) dir (walDurFresh md), COMM Q }>) ∗
    osNames J (.except X) (DFrac.own (1 : Qp).half) hJ ∗
    osMeta g.ino (DFrac.own 1) g.om ∗ osBytes g.ino 0 (DFrac.own 1) g.bs)

/-- **What `Create` gets from the rename's update**: with no effect, what it held; after the commit,
the client's `Q`, the segment's halves the invariant did not take, and a past state with the fresh
WAL in `dir`. -/
def walCreateQ (dir : GoString) (N : NameSet) (h : NamesH) (md : List w8) (Q : IProp GF)
    (J : Ino) (X : List GoString) (hJ : NamesH) (g : SegG) : Option (Nat × Nat) → IProp GF
  | none => walCreateP (W := W) dir N h md Q J X hJ g
  | some _ => iprop(Q ∗ osMeta g.ino (DFrac.own (1 : Qp).half) g.om ∗
      osBytes g.ino 0 (DFrac.own (1 : Qp).half) g.bs ∗
      ∃ s', walPast (W := W) s' ∗ ⌜s'.wal !! dir = some (walDurFresh md)⌝)

/-- **`Create`'s update for `os.Rename.specDirSnc`** (see the file header). The program's premises:
`dir = r/nm`, `tmp` (`nm.tmp`) holding `J` in the claim, both names of the claim; `J ≠ jr`; the call's
log bound `lb` past both claims' last entries; the new layout `lay` of `jr`, `nm`, `J` with the one
segment `g` (nonempty), its static relation over `J`'s names, every byte durable, the stream then
zeros. -/
theorem walCreate_osAUnc (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir nm tmp : GoString) (md : List w8) (Q : IProp GF) (N : NameSet) (h : NamesH) (J : Ino)
    (X : List GoString) (hJ : NamesH) (lay : WalLay) (g : SegG) (lb : Nat)
    (hin : InArea r dir nm) (hne : tmp ≠ nm) (hnmN : N.Mem nm) (htmpN : N.Mem tmp)
    (hctmp : h.cur !! tmp = some (.dir J))
    (htmp : ¬ walNameOk tmp) (htw : walNameP tmp = false) (htmpS : AreaSlot tmp) (hJjr : J ≠ jr)
    (hlb : h.next ≤ lb) (hJlb : hJ.next ≤ lb)
    (hlay : lay.jr = jr ∧ lay.nm = nm ∧ lay.j = J) (hsegs : lay.segs = [g]) (hbs : g.bs ≠ [])
    (hJcoh : ClaimCoh hJ J (.except X)) (hX : ∀ b ∈ X, walNameP b = false)
    (habs : WalAbsD C Mr (walDurFresh md) lay hJ.cur)
    (hdur : ∀ y ∈ g.bs, y = durB y.1)
    (htail : lay.wr = (segStream C Mr (walDurFresh md) lay.cuts lay.cuts.length).length)
    (hold0 : ∀ b, lay.wr ≤ b → b < lay.old.length → lay.old.getD b 0 = 0)
    (hz : lay.old.length - lay.wr = 0 ∨ 8 ≤ lay.old.length - lay.wr)
    (hcut : g.om.cut = none) :
    ⊢ walInv (W := W) C Mr R jr r -∗ walCreateP (W := W) dir N h md Q J X hJ g -∗
      osAUnc (osNames jr N (DFrac.own (1 : Qp).half) h)
        (renDirOut jr J N tmp nm h (DFrac.own (1 : Qp).half) lb)
        (walCreateQ (W := W) dir N h md Q J X hJ g) := by
  iintro #Hinv HP
  iapply osAUnc_coiter _ _ _ (walCreateP (W := W) dir N h md Q J X hJ g) $$ [] HP
  iintro !> HP
  unfold osAUncPre
  iintro Hnc
  imod walInv_open C Mr R jr r osAuMask walN_sub_au $$ Hinv Hnc with ⟨Hb, Hnc, Hcl⟩
  rw [show osAuMask \ (↑walN : CoPset) = walAuMask from rfl]
  icases Hb with ⟨%s, Hb⟩
  unfold walCreateP
  icases HP with ⟨Htok, Hau, HJ, Hm, Hbs⟩
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl0, #Hcm, Hlays, %Hok, %Hco, ⟨%CR, Hcra, %Hcro⟩,
    Htl, %Han⟩
  icases walCreating_lookup CR dir N h $$ Hcra Htok with ⟨%Hcr, Hcra, Htok⟩
  have hco := Hcro
  obtain ⟨hc, hcoh, hexcl, honce, hdist⟩ := Hcro dir N h Hcr
  obtain ⟨l1, l2, hcl, hl1, hl2⟩ := honce
  subst hcl
  icases (osClaims_split _ _ _ _).1 $$ Hcl0 with ⟨Hl1, Hα, Hl2⟩
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_nil] at Hacc
  icases Hacc with ⟨Hab0, Hcla⟩
  imodintro
  isplitl [Hα]
  · iexact Hα
  iframe Hnc
  isplit
  · -- abort
    iintro Hα
    icases Hcla with ⟨Hab, -⟩
    imod Hab $$ Hab0 with Hau
    imod Hcl $$ [Hg Hl1 Hα Hl2 Hlays Hcra Htl]
    · iexists s
      iexists Ls, l1 ++ (jr, N, h) :: l2, n, F
      iframe Hg Hcm Hlays Htl
      isplitr
      · ipureintro; exact Har
      isplitl [Hl1 Hα Hl2]
      · iapply (osClaims_split _ _ _ _).2
        iframe Hl1 Hα Hl2
      isplitr
      · ipureintro; exact Hok
      isplitr
      · ipureintro; exact Hco
      isplitl [Hcra]
      · iexists CR
        iframe Hcra
        ipureintro; exact hco
      ipureintro; exact Han
    imodintro
    dsimp only
    iframe Htok Hau HJ Hm Hbs
  · -- commit
    iintro %o Hβ
    rcases o with _ | ⟨x, s0⟩
    · -- no effect: as the abort
      unfold renDirOut
      simp only [logOut, claimOut]
      icases Hβ with ⟨-, Hα⟩
      icases Hcla with ⟨Hab, -⟩
      imod Hab $$ Hab0 with Hau
      imod Hcl $$ [Hg Hl1 Hα Hl2 Hlays Hcra Htl]
      · iexists s
        iexists Ls, l1 ++ (jr, N, h) :: l2, n, F
        iframe Hg Hcm Hlays Htl
        isplitr
        · ipureintro; exact Har
        isplitl [Hl1 Hα Hl2]
        · iapply (osClaims_split _ _ _ _).2
          iframe Hl1 Hα Hl2
        isplitr
        · ipureintro; exact Hok
        isplitr
        · ipureintro; exact Hco
        isplitl [Hcra]
        · iexists CR
          iframe Hcra
          ipureintro; exact hco
        ipureintro; exact Han
      imodintro
      dsimp only [walCreateQ, walCreateP]
      iframe Htok Hau HJ Hm Hbs
    · -- the commit
      unfold renDirOut
      simp only [logOut, claimOut]
      icases Hβ with ⟨⟨%hls, Hlog⟩, Hα⟩
      unfold osLogged
      icases Hlog with ⟨%hsx, -, -⟩
      simp only [renDirEnt] at hsx
      icases Hcla with ⟨-, Hco⟩
      isimp only [tforall_nil, Std.Tele.app, ULift.down] at Hco
      -- the client's map: `dir` holds no WAL
      irevert Hab0
      dsimp only [Std.Tele.app]
      iintro Hab0
      unfold walAbsent walDirIs
      icases Hab0 with ⟨%M, HM, %HMd⟩
      icases walOwn_agree s M $$ Hg HM with %HMs
      have hMd : M !! dir = none := (walOptLe_none_iff _).1 HMd
      have hsd : s.wal !! dir = none := by
        have := HMs dir; rw [hMd] at this; exact (walOptLe_none_iff _).1 this
      have hLd : Ls !! dir = none := Hok.2.1 dir hsd
      -- the new segment is none of the layouts'
      obtain ⟨y, ys, hgbs⟩ : ∃ y ys, g.bs = y :: ys := by
        cases hb : g.bs with
        | nil => exact absurd hb hbs
        | cons y ys => exact ⟨y, ys, rfl⟩
      rw [hgbs]
      icases laysResF_ino_ne F Ls g.ino g.om y ys $$ Hlays Hm Hbs with ⟨%hino, Hlays, Hm, Hbs⟩
      -- the pure facts after the commit
      have hin' : InArea s.area dir nm := Har ▸ hin
      have hothers : ∀ c' ∈ l1 ++ (jr, N, h) :: l2, c' ≠ (jr, N, h) → c'.1 = jr →
          ¬ c'.2.1.Mem nm ∧ ¬ c'.2.1.Mem tmp := fun c' hc' hne' hj =>
        ⟨hexcl c' hc' hne' hj nm hnmN, hexcl c' hc' hne' hj tmp htmpN⟩
      have hdisj : ∀ g1 ∈ lay.segs, ∀ g' ∈ segsAll Ls, g1.ino ≠ g'.ino := by
        rw [hsegs]; intro g1 hg1 g' hg'
        rw [List.mem_singleton] at hg1; subst hg1
        exact (hino g' hg').symm
      have hdur' : ∀ g1 ∈ lay.segs, ∀ y ∈ g1.bs, y = durB y.1 := by
        rw [hsegs]; intro g1 hg1
        rw [List.mem_singleton] at hg1; subst hg1
        exact hdur
      obtain ⟨hok', han'⟩ := walsOk_create (x := x) (st := s0) Hok Han.1 hsd hin' hc hcoh
        (Nat.le_trans hlb hls) hsx hne hnmN htmpN hctmp hothers htmp htw hJjr hlay hJcoh
        (Nat.le_trans hJlb hls) hX habs hdur' htail hold0 hz (by rw [hsegs]; simp)
        hdisj (by rw [hsegs]; simpa using hcut) Han.2 htmpS
      -- the ghost state, the client's commit, the creating entry
      imod walGhost_upd s (createSt s dir md) M (absLe_createSt hsd)
        (walKeysInArea_createSt hin') $$ Hg HM with ⟨-, Hg, HM, #Hp⟩
      imod Hco $$ [HM] with HQ
      · unfold walDiskAt walDirIs
        iexists (createSt s dir md).wal
        iframe HM
        ipureintro
        simp only [createSt, GMap.lookup_insert_eq]
        exact walDurLe_refl _
      imod walCreating_delete CR dir N h $$ Hcra Htok with Hcra
      icases (osMeta_halves g.ino g.om).1 $$ Hm with ⟨Hm1, Hm2⟩
      icases (osBytes_halves g.ino 0 (y :: ys)).1 $$ Hbs with ⟨Hb1, Hb2⟩
      have hF : ∀ g' ∈ segsAll Ls, (GMap.delete g.ino F) !! g'.ino = F !! g'.ino := fun g' hg' =>
        GMap.lookup_delete_ne _ (Ne.symm (hino g' hg'))
      imod Hcl $$ [Hg Hl1 Hα Hl2 HJ Hlays Hm1 Hb1 Hcra Htl]
      · iexists (createSt s dir md)
        iexists <[dir := lay]> Ls,
          createClaims (l1 ++ (jr, N, h) :: l2) jr N h x (renDirEnt jr tmp nm J s0)
            (renCur N h tmp nm J) J X hJ, n, GMap.delete g.ino F
        iframe Hg Hcm
        isplitr
        · ipureintro; exact Har
        isplitl [Hl1 Hα Hl2 HJ]
        · unfold createClaims
          iapply osClaims_create l1 l2 (jr, N, h) (jr, N, h.log x (renDirEnt jr tmp nm J s0)
            (renCur N h tmp nm J)) (J, NameSet.except X, hJ) _ hl1 hl2
          dsimp only [renCur]
          iframe Hl1 Hα Hl2 HJ
        isplitl [Hlays Hm1 Hb1]
        · iapply laysResF_insert _ Ls dir lay hLd
          isplitl [Hm1 Hb1]
          · rw [hsegs]
            iapply BigSepL.bigSepL_singleton.2
            unfold segResF
            rw [GMap.lookup_delete_eq]
            dsimp only
            unfold segRes
            rw [hgbs]
            iframe Hm1 Hb1
          · iapply laysResF_congr F _ Ls hF $$ Hlays
        isplitr
        · ipureintro; exact hok'
        isplitr
        · ipureintro; exact walsCreateOk_create Hco
        isplitl [Hcra]
        · iexists GMap.delete dir CR
          iframe Hcra
          ipureintro; exact creatingOk_create hco Hcr hnmN hJjr
        isplitl [Htl]
        · iapply walTailsRes_create C Mr s Ls F _ dir md lay hsd hF $$ Htl
        ipureintro; exact ⟨han', Han.2⟩
      imodintro
      dsimp only [walCreateQ]
      rw [hgbs]
      iframe HQ Hm2 Hb2
      iexists (createSt s dir md)
      iframe Hp
      ipureintro
      simp only [createSt, GMap.lookup_insert_eq]

end au

end WalFs
end EtcdGrove
end Perennial

end
