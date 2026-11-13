/- Lean-first (no Rocq counterpart).

# The open handle's access to its tail in `walInv` (W6; `notes/wal-fsext-plan.md`, "W6 implementation log")

`walInvBody_tail`: with the handle's key to its tail record (`walTailKey dir γ`) and its half of the
record, the invariant's contents give the WAL `d` of `dir`, its layout `lay` (the segments `pre`
then the tail `g0`), the tail's part (`segResF`, idle or with a write in flight) and the other half
of the record, which agrees with the handle's; and they are given back with the tail replaced by
any `g` and the write position by any `wr'`, the writes in flight changed on the tail only, as long
as the static relation holds of the new layout (`walsOk_tail`, `TailStepPure.lean`, does the rest).

Also `osBytes_agree` (two runs of a file's bytes of the same length agree) and `osN_sub_nwal`.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailStepPure
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateAuLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

/-- The extension's invariants are outside the WAL invariant's namespace. -/
theorem osN_sub_nwal : (↑osN : CoPset) ⊆ (⊤ : CoPset) \ ↑walN := by
  have h1 : (↑walN : CoPset) ## ↑osN := ndot_ne_disjoint nroot (by decide)
  intro p hp
  exact LawfulSet.mem_diff.2 ⟨CoPset.mem_full, fun hn => h1 p ⟨hn, hp⟩⟩

/-- `SegsNamed` depends on the segments' names and inodes only. -/
theorem SegsNamed.swap {segs segs' : List SegG} {ents : Ents}
    (hs : ∀ x ∈ segs', ∃ y ∈ segs, y.name = x.name ∧ y.ino = x.ino) (h : SegsNamed segs ents) :
    SegsNamed segs' ents := by
  refine ⟨fun x hx => ?_, h.2⟩
  obtain ⟨y, hy, hn, hi⟩ := hs x hx
  have := h.1 y hy
  rw [← hn, ← hi]; exact this

theorem SegsNamedC.swap {segs segs' : List SegG} {ents : Ents}
    (hs : ∀ x ∈ segs', ∃ y ∈ segs, y.name = x.name ∧ y.ino = x.ino) (h : SegsNamedC segs ents) :
    SegsNamedC segs' ents := by
  refine ⟨fun x hx => ?_, h.2⟩
  obtain ⟨y, hy, hn, hi⟩ := hs x hx
  have := h.1 y hy
  rw [← hn, ← hi]; exact this

theorem segs_swap_tail {pre : List SegG} {g g0 : SegG} (hn : g.name = g0.name) (hi : g.ino = g0.ino) :
    ∀ x ∈ pre ++ [g], ∃ y ∈ pre ++ [g0], y.name = x.name ∧ y.ino = x.ino := by
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · exact ⟨x, List.mem_append_left _ h, rfl, rfl⟩
  · rw [List.mem_singleton] at h; subst h
    exact ⟨g0, by simp, hn.symm, hi.symm⟩

/-- **The tail replaced keeps `WalsNamed`** (same name, same inode). -/
theorem walsNamed_tail {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} {dir : GoString}
    {lay : WalLay} {pre : List SegG} {g0 g : SegG} (wr : Nat) (h : WalsNamed Ls cl n)
    (hl : Ls !! dir = some lay) (hs : lay.segs = pre ++ [g0]) (hn : g.name = g0.name)
    (hi : g.ino = g0.ino) : WalsNamed (<[dir := tailLay lay pre g wr]> Ls) cl n := by
  intro dir' lay' hl'
  by_cases hd : dir' = dir
  · subst hd
    rw [GMap.lookup_insert] at hl'
    cases hl'
    obtain ⟨h1, h2⟩ := h dir' lay hl
    have hsw := segs_swap_tail (pre := pre) hn hi
    rw [← hs] at hsw
    exact ⟨fun hj hc => (h1 hj hc).swap hsw, fun m' hm => (h2 m' hm).swap hsw⟩
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm hd)] at hl'
    exact h dir' lay' hl'

/-- The tail replaced leaves the WAL directories' claims as they were. -/
theorem walDirClaimOf_tail {Ls : GMap GoString WalLay} {dir : GoString} {lay : WalLay}
    (pre : List SegG) (g : SegG) (wr : Nat) (hl : Ls !! dir = some lay) (c : Claim) :
    WalDirClaimOf (<[dir := tailLay lay pre g wr]> Ls) c ↔ WalDirClaimOf Ls c := by
  constructor
  · rintro ⟨dir', lay', hl', hj, hX⟩
    by_cases hd : dir' = dir
    · subst hd
      rw [GMap.lookup_insert] at hl'
      cases hl'
      exact ⟨dir', lay, hl, hj, hX⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hd)] at hl'
      exact ⟨dir', lay', hl', hj, hX⟩
  · rintro ⟨dir', lay', hl', hj, hX⟩
    by_cases hd : dir' = dir
    · subst hd
      rw [hl] at hl'; cases hl'
      exact ⟨dir', tailLay lay pre g wr, GMap.lookup_insert _ _ _, hj, hX⟩
    · exact ⟨dir', lay', by rw [GMap.lookup_insert_ne _ _ (Ne.symm hd)]; exact hl', hj, hX⟩

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **Two runs of a file's bytes from the same offset, of the same length, agree.** -/
theorem osBytes_agree (i : Ino) (dq1 dq2 : DFrac) :
    ∀ (off : Nat) (xs ys : List ByteG), xs.length = ys.length →
    ⊢ osBytes (L := L) i off dq1 xs -∗ osBytes (L := L) i off dq2 ys -∗ ⌜xs = ys⌝
  | _, [], [], _ => by iintro - -; ipureintro; rfl
  | _, [], _ :: _, h => by simp at h
  | _, _ :: _, [], h => by simp at h
  | off, x :: xs, y :: ys, h => by
    unfold osBytes
    iintro Hx Hy
    icases (bytesG_cons _ _ _ _ _ _).1 $$ Hx with ⟨Hx, Hxs⟩
    icases (bytesG_cons _ _ _ _ _ _).1 $$ Hy with ⟨Hy, Hys⟩
    icases gElem_valid_2 _ _ _ _ _ _ _ $$ Hx Hy with %Hv
    ihave %Hr := osBytes_agree i dq1 dq2 (off + 1) xs ys (by simpa using h) $$ [Hxs] [Hys]
    · unfold osBytes; iexact Hxs
    · unfold osBytes; iexact Hys
    ipureintro; rw [Hv.2, Hr]

/-- **A half of a tail record** (`walTailsRes`'s, with the WAL's camera). -/
def tailVar (γ : GName) (tg : TailG) : IProp GF :=
  letI := walAllG (W := W)
  ghostVar γ (1 : Qp).half tg

/-- The tails' authority knows a handle's key. -/
theorem walTailKey_lookup (T : GMap GoString GName) (dir : GoString) (γ : GName) :
    ⊢ walTailsAuth (W := W) T -∗ walTailKey (W := W) dir γ -∗ ⌜T !! dir = some γ⌝ := by
  letI := walAllG (W := W)
  unfold walTailsAuth walTailKey
  exact ghost_map_lookup

/-- **No three halves of a file's byte 0.** -/
theorem osBytes_three (i : Ino) (x y z : ByteG) (xs ys zs : List ByteG) :
    ⊢ osBytes (L := L) i 0 (DFrac.own (1 : Qp).half) (x :: xs) -∗
      osBytes (L := L) i 0 (DFrac.own (1 : Qp).half) (y :: ys) -∗
      osBytes (L := L) i 0 (DFrac.own (1 : Qp).half) (z :: zs) -∗ False := by
  unfold osBytes
  iintro Hx Hy Hz
  icases (bytesG_cons _ _ _ _ _ _).1 $$ Hx with ⟨Hx, -⟩
  icases (bytesG_cons _ _ _ _ _ _).1 $$ Hy with ⟨Hy, -⟩
  icases (bytesG_cons _ _ _ _ _ _).1 $$ Hz with ⟨Hz, -⟩
  unfold gElem
  letI := (gooseOsGS (L := L)).osAllG
  icases ghostMapElem_combine _ _ _ _ _ _ $$ Hx Hy with ⟨Hxy, -⟩
  icases ghostMapElem_valid_2 _ _ _ _ _ _ $$ Hxy Hz with %Hv
  have e : (DFrac.own (1 : Qp).half • DFrac.own (1 : Qp).half : DFrac) = DFrac.own 1 := by
    show DFrac.own ((1 : Qp).half + (1 : Qp).half) = _
    rw [Qp.half_add_half]
  rw [e] at Hv
  exact absurd (DFrac.valid_own_op Hv.1) (by simp)

/-- **A segment's part in the invariant, a parked copy of its halves and the program's half of its
byte 0 exclude each other**: three halves of byte 0. -/
theorem segResF_parked_false (F : GMap Ino SegFl) (g : SegG) (x : ByteG) (xs : List ByteG)
    (hg : g.bs ≠ []) :
    ⊢ segResF (L := L) F g -∗ segRes (L := L) g -∗
      osBytes (L := L) g.ino 0 (DFrac.own (1 : Qp).half) (x :: xs) -∗ False := by
  iintro Hs Hp Hx
  obtain ⟨y, ys, hy⟩ : ∃ y ys, g.bs = y :: ys := by
    cases h : g.bs with
    | nil => exact absurd h hg
    | cons y ys => exact ⟨y, ys, rfl⟩
  unfold segRes
  icases Hp with ⟨-, Hp⟩
  rw [hy]
  unfold segResF
  split
  · try unfold segRes
    icases Hs with ⟨-, Hs⟩
    rw [hy]
    iapply osBytes_three g.ino x y y xs ys ys $$ Hx Hp Hs
  · rename_i fl _
    split
    · icases Hs with ⟨-, Hb0, -, %Hok⟩
      obtain ⟨z, zs, hz⟩ := segFl_take_cons Hok
      rw [hz]
      iapply osBytes_three g.ino x y z xs ys zs $$ Hx Hp Hb0
    · rename_i tg _
      icases Hs with ⟨-, Hb0, %Hok⟩
      obtain ⟨z, zs, hz⟩ := segFlR_take_cons Hok
      rw [hz]
      iapply osBytes_three g.ino x y z xs ys zs $$ Hx Hp Hb0

/-- The segments' runs as a map over the layouts. -/
theorem segsAll_map (P : SegG → IProp GF) (Ls : GMap GoString WalLay) :
    ([∗list] g ∈ segsAll Ls, P g) ⊣⊢ [∗map] _dir ↦ lay ∈ Ls, [∗list] g ∈ lay.segs, P g := by
  unfold segsAll
  rw [BigSepL.bigSepL_flatMap (PROP := IProp GF)]
  exact (BigSepM.bigSepM_toList (Φ := fun (_ : GoString) (lay : WalLay) =>
    iprop([∗list] g ∈ lay.segs, P g)) (m := Ls)).symm

/-- **One layout's segments out of a run over every segment, and in again, replaced.** -/
theorem segsAll_swap (P : SegG → IProp GF) (Ls : GMap GoString WalLay) (dir : GoString)
    (lay lay' : WalLay) (hl : Ls !! dir = some lay) :
    ([∗list] g ∈ segsAll Ls, P g) ⊢ ([∗list] g ∈ lay.segs, P g) ∗
      (([∗list] g ∈ lay'.segs, P g) -∗ [∗list] g ∈ segsAll (<[dir := lay']> Ls), P g) := by
  iintro H
  ihave H := (segsAll_map P Ls).1 $$ H
  icases (BigSepM.bigSepM_delete (Φ := fun (_ : GoString) (lay : WalLay) =>
    iprop([∗list] g ∈ lay.segs, P g)) hl).1 $$ H with ⟨Hd, Hr⟩
  iframe Hd
  iintro Hn
  iapply (segsAll_map P _).2
  iapply (BigSepM.bigSepM_insert_delete (Φ := fun (_ : GoString) (lay : WalLay) =>
    iprop([∗list] g ∈ lay.segs, P g))).2
  iframe Hn Hr

/-- The segments' parts, the layout of `dir` apart. -/
theorem laysResF_del (F : GMap Ino SegFl) (Ls : GMap GoString WalLay) (dir : GoString) (lay : WalLay)
    (hl : Ls !! dir = some lay) :
    laysResF (L := L) F Ls ⊣⊢ ([∗list] g ∈ lay.segs, segResF (L := L) F g) ∗
      laysResF (L := L) F (Iris.Std.delete Ls dir) := by
  refine (laysResF_map (L := L) F Ls).trans ?_
  refine (BigSepM.bigSepM_delete (Φ := fun (_ : GoString) (lay : WalLay) =>
    iprop([∗list] g ∈ lay.segs, segResF (L := L) F g)) hl).trans ?_
  exact sep_congr .rfl (laysResF_map (L := L) F _).symm

/-- **The tail's access** (see the file header). -/
theorem walInvBody_tail (C : WalCodec) (hC : C.Ok) (Mr : WalMarshal) (R : Roots) (jr : Ino)
    (r : GoString) (s : AbsDiskState) (dir : GoString) (γ : GName) (tg : TailG) (x : ByteG)
    (xs : List ByteG) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ walTailKey (W := W) dir γ -∗
      tailVar (W := W) γ tg -∗
      osBytes (L := L) tg.2.2.2.2.1 0 (DFrac.own (1 : Qp).half) (x :: xs) -∗
      ∃ (F : GMap Ino SegFl) (d : WalDur) (lay : WalLay) (pre : List SegG) (g0 : SegG),
        ⌜s.wal !! dir = some d ∧ lay.segs = pre ++ [g0] ∧ tg = tailG d lay g0.ino (F !! g0.ino) ∧
          (∃ ents, WalAbsD C Mr d lay ents) ∧ g0.om.cut = none⌝ ∗
        segResF (L := L) F g0 ∗ walTailKey (W := W) dir γ ∗ tailVar (W := W) γ tg ∗
        tailVar (W := W) γ tg ∗ osBytes (L := L) tg.2.2.2.2.1 0 (DFrac.own (1 : Qp).half) (x :: xs) ∗
        (∀ (g : SegG) (wr' : Nat) (F' : GMap Ino SegFl),
          ⌜g.ino = g0.ino ∧ g.name = g0.name ∧ g.om.cut = none ∧ g.bs.length = g0.bs.length ∧
            (∀ z, g0.om.zf = some z → g0.bs.length ≤ z) ∧
            (∀ ents, WalAbsD C Mr d lay ents → WalAbsD C Mr d (tailLay lay pre g wr') ents) ∧
            (∀ i, i ≠ g0.ino → F' !! i = F !! i)⌝ -∗
          segResF (L := L) F' g -∗
          tailVar (W := W) γ (tailG d (tailLay lay pre g wr') g.ino (F' !! g.ino)) -∗
          walInvBody (L := L) (W := W) C Mr R jr r s) := by
  letI := walAllG (W := W)
  unfold tailVar
  iintro Hb Hk Hv Hx
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl, Hn, Hlays, %HW, %HWC, HCR, Htl, %Hab, %Hnm, Hpk⟩
  unfold walTailsRes
  icases Htl with ⟨%T, HTa, HTm⟩
  icases walTailKey_lookup T dir γ $$ HTa Hk with %HT
  ihave ⟨Hent, HTm⟩ := (BigSepM.bigSepM_delete (Φ := fun (dir : GoString) (γ : GName) =>
    iprop(∃ (d : WalDur) (lay : WalLay) (g : SegG),
      ⌜s.wal !! dir = some d ∧ Ls !! dir = some lay ∧ lay.segs.getLast? = some g ∧ TailZeros lay ∧
        TailBound C Mr d lay⌝ ∗
      ghostVar γ (1 : Qp).half (tailG d lay g.ino (F !! g.ino)))) HT).1 $$ HTm
  icases Hent with ⟨%d, %lay, %g0, %hp, Hv'⟩
  obtain ⟨hd, hl, hg, hZ, hB⟩ := hp
  obtain ⟨pre, hs⟩ := List.getLast?_eq_some_iff.1 hg
  icases ghostVar_agree _ _ _ _ _ $$ Hv Hv' with %Htg
  obtain ⟨hW1, hW2, hW3, hW4, hW5, hW6⟩ := HW
  obtain ⟨lay1, nm, hj, hl1, hA, hjr, hnm, hc, habs, hcr⟩ := hW1 dir d hd
  rw [hl] at hl1; cases hl1
  have hnd := (segsAll_nodup_iff Ls).1 hW3
  have hg0m : g0 ∈ lay.segs := by rw [hs]; simp
  have hcut0 : g0.om.cut = none := hW4 g0 (mem_segsAll hl hg0m)
  icases (laysResF_del (L := L) F Ls dir lay hl).1 $$ Hlays with ⟨Hsegs, Hrest⟩
  rw [hs]
  icases (BigSepL.bigSepL_append (PROP := IProp GF)).1 $$ Hsegs with ⟨Hpre, Hlast⟩
  icases (BigSepL.bigSepL_singleton (PROP := IProp GF)).1 $$ Hlast with Hlast
  -- the tail's inode is among those the program took out (`walParked`'s `O`): else three
  -- halves of its byte 0 (the program's, the invariant's, the parked one)
  have hbs0 : g0.bs ≠ [] := by
    have h1 := walAbsD_so_pos habs
    obtain ⟨h2, -, h3, h4, -⟩ := habs.last g0 hg
    intro he; rw [he] at h3; simp at h3; omega
  ihave Hx := (show osBytes (L := L) tg.2.2.2.2.1 0 (DFrac.own (1 : Qp).half) (x :: xs) ⊢
      osBytes (L := L) g0.ino 0 (DFrac.own (1 : Qp).half) (x :: xs) by rw [Htg]; exact .rfl) $$ Hx
  unfold walParked
  icases Hpk with ⟨%b, %O, %D, Hpa, %HbO, Hps, Hpc⟩
  by_cases hO : g0.ino ∈ O
  rotate_left
  · iexfalso
    icases (BigSepL.bigSepL_mem_acc (mem_segsAll hl hg0m)) $$ Hps with ⟨Hp0, -⟩
    ihave Hp0 := (show (if g0.ino ∈ O then (emp : IProp GF) else segRes (L := L) g0) ⊢
      segRes (L := L) g0 by rw [if_neg hO]) $$ Hp0
    iapply segResF_parked_false F g0 x xs hbs0 $$ Hlast Hp0 Hx
  iexists F, d, lay, pre, g0
  isplitr
  · ipureintro; exact ⟨hd, hs, Htg, ⟨_, habs⟩, hcut0⟩
  rw [Htg, show (tailG d lay g0.ino (F !! g0.ino)).2.2.2.2.1 = g0.ino from rfl]
  iframe Hlast Hk Hv Hv' Hx
  iintro %g %wr' %F' %hp Hseg Hvn
  obtain ⟨hino, hname, hcut, hlen, hzf, habs', hF'⟩ := hp
  -- the other segments' parts, unchanged
  have hpre_ne : ∀ g' ∈ pre, g'.ino ≠ g0.ino := by
    intro g' hg' he
    have h := hnd.1 dir lay hl
    rw [hs, List.map_append, List.nodup_append] at h
    exact h.2.2 g'.ino (List.mem_map_of_mem hg') g0.ino (by simp) he
  have hrest_ne : ∀ g' ∈ segsAll (Iris.Std.delete Ls dir), g'.ino ≠ g0.ino := by
    intro g' hg' he
    obtain ⟨dir', lay', hl', hg''⟩ := segsAll_mem hg'
    change GMap.delete dir Ls !! dir' = some lay' at hl'
    have hne : dir' ≠ dir := by rintro rfl; rw [GMap.lookup_delete_eq] at hl'; cases hl'
    have hl'' : Ls !! dir' = some lay' := by rwa [GMap.lookup_delete_ne _ (Ne.symm hne)] at hl'
    exact hnd.2 dir' dir lay' lay hne hl'' hl g' hg'' g0 hg0m he
  ihave Hrest := laysResF_congr (L := L) F F' _ (fun g' hg' => hF' _ (hrest_ne g' hg')) $$ Hrest
  ihave Hpre : [∗list] g' ∈ pre, segResF (L := L) F' g' $$ [Hpre]
  · iapply BigSepL.bigSepL_mono (fun {k g'} hk => ?_) $$ Hpre
    have e := hF' _ (hpre_ne g' (List.mem_of_getElem? hk))
    unfold segResF; rw [e]
  iexists (<[dir := tailLay lay pre g wr']> Ls), cl, n, F'
  iframe Hg Hcl Hn HCR
  isplitr
  · ipureintro; exact Har
  isplitl [Hpre Hseg Hrest]
  · iapply (laysResF_map (L := L) F' _).2
    iapply (BigSepM.bigSepM_insert_delete (Φ := fun (_ : GoString) (lay : WalLay) =>
      iprop([∗list] g ∈ lay.segs, segResF (L := L) F' g))).2
    isplitl [Hpre Hseg]
    · simp only [tailLay]
      iapply (BigSepL.bigSepL_append (PROP := IProp GF)).2
      iframe Hpre
      iapply (BigSepL.bigSepL_singleton (PROP := IProp GF)).2
      iexact Hseg
    · iapply (laysResF_map (L := L) F' _).1 $$ Hrest
  isplitr
  · ipureintro
    exact walsOk_tail hC ⟨hW1, hW2, hW3, hW4, hW5, hW6⟩ hd hl hs hino hcut hlen hzf hZ hB habs'
  isplitr
  · ipureintro; exact HWC
  isplitl [HTa HTm Hvn]
  · iexists T
    iframe HTa
    iapply (BigSepM.bigSepM_delete (Φ := fun (k : GoString) (γ' : GName) =>
      iprop(∃ (d' : WalDur) (la : WalLay) (g' : SegG),
        ⌜s.wal !! k = some d' ∧ (<[dir := tailLay lay pre g wr']> Ls) !! k = some la ∧
          la.segs.getLast? = some g' ∧ TailZeros la ∧ TailBound C Mr d' la⌝ ∗
        ghostVar γ' (1 : Qp).half (tailG d' la g'.ino (F' !! g'.ino)))) HT).2
    isplitl [Hvn]
    · iexists d, (tailLay lay pre g wr'), g
      iframe Hvn
      ipureintro
      exact ⟨hd, GMap.lookup_insert _ _ _, by simp [tailLay], hZ, hB⟩
    · iapply BigSepM.bigSepM_mono (fun {k γ'} hk => ?_) $$ HTm
      have hne : k ≠ dir := by
        change GMap.delete dir T !! k = some γ' at hk
        rintro rfl; rw [GMap.lookup_delete_eq] at hk; cases hk
      iintro ⟨%d', %lay', %g', %hp', Hv''⟩
      obtain ⟨hd', hl', hg', hZ', hB'⟩ := hp'
      have hg'm : g' ∈ lay'.segs := List.mem_of_getLast? hg'
      have he : F' !! g'.ino = F !! g'.ino :=
        hF' _ (hnd.2 k dir lay' lay hne hl' hl g' hg'm g0 hg0m)
      iexists d', lay', g'
      rw [he]
      iframe Hv''
      ipureintro
      exact ⟨hd', by rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)]; exact hl', hg', hZ', hB'⟩
  isplitr
  · ipureintro; exact Hab
  isplitr
  · ipureintro; exact walsNamed_tail wr' Hnm hl hs hname hino
  -- the parked halves: the tail's inode stays out
  iexists b, O, D
  iframe Hpa
  isplitr
  · ipureintro; exact HbO
  isplitl [Hps]
  · icases segsAll_swap (fun g => if g.ino ∈ O then (emp : IProp GF) else segRes (L := L) g) Ls dir
      lay (tailLay lay pre g wr') hl $$ Hps with ⟨Hd, Hback⟩
    iapply Hback
    ihave Hd := (show ([∗list] g' ∈ lay.segs, if g'.ino ∈ O then (emp : IProp GF) else
        segRes (L := L) g') ⊢ [∗list] g' ∈ pre ++ [g0], if g'.ino ∈ O then (emp : IProp GF) else
        segRes (L := L) g' by rw [hs]) $$ Hd
    icases (BigSepL.bigSepL_append (PROP := IProp GF)).1 $$ Hd with ⟨Hdp, -⟩
    simp only [tailLay]
    iapply (BigSepL.bigSepL_append (PROP := IProp GF)).2
    iframe Hdp
    iapply (BigSepL.bigSepL_singleton (PROP := IProp GF)).2
    rw [if_pos (by rw [hino]; exact hO)]
    iempintro
  · iapply BigSepL.bigSepL_mono (fun {k c} _ => ?_) $$ Hpc
    have e := walDirClaimOf_tail pre g wr' hl c
    by_cases hc : ParkedClaim Ls D c
    · rw [if_pos hc, if_pos (show ParkedClaim _ D c from ⟨e.2 hc.1, hc.2⟩)]
    · rw [if_neg hc, if_neg (show ¬ ParkedClaim (<[dir := tailLay lay pre g wr']> Ls) D c from
        fun h => hc ⟨e.1 h.1, h.2⟩)]

end iris

end WalFs
end EtcdGrove
end Perennial

end
