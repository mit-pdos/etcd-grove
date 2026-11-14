/- Lean-first (no Rocq counterpart).

# The pure facts of a cut's rename commit (W2, `notes/wal-fsext-plan.md`, "W2 implementation log")

`cut`'s rename (`os.Rename(N.tmp, fpath)`, `os.Rename.specFileSnc`) of the pipeline's file `tmp` (in
its claim `(j, .only [tmp], ht)`) onto the free `.wal` name `bt` of the WAL directory `j` (the
invariant's claim `(j, .except X, hj)`, `tmp ∈ X`), the new segment `g`. The WAL state `s` is
unchanged; the claim is replaced by its logged successor (`cutClaim`), the WAL's layout by
`cutLay lay |H| g wr` (`Cut.lean`), with the old layout as the crash alternative, and the pending-cut
flag goes to `some dir` (`DirKeysOk … (some dir)`: the other WALs keep `alt = none`).

`cutCommit_pure` bundles what `walInvBody`'s pure conjuncts need after the commit (`CutAu.lean`'s
`walCut_osAUnc`). Proved, per conjunct (the framed ones in `CutCommitLemmas.lean`):
- `WalsOk`, the cut WAL: `WalDirClaim` at the new claim (`claimCoh_log`, the rename writes only `tmp`,
  in `X`, and `bt`); `cutLay_abs` (the old `WalAbsD` over `hj.cur`: the WAL's claim is the key's, since
  no other claim of `j` holds a `.wal` name; `hents`: `bt` the largest `.wal` name of `hj.cur`, from
  `nm0 < bt` and `nm0` the last segment's name: `walInos` of the sorted `.wal` names, the inodes
  `Nodup`); `CrashOkW` at `alt = some lay` (`altOk_cut`, `crashOkA_cut` from `DirKeysOk`'s `CrashOkA
  … none`, `c = none`). The other WALs: their directories are not `j` (their claims would be the key's,
  and their segments would share inodes); their crash conditions over the replaced claims as
  `crashOkW_create_other` (a crash keeping the rename is one of `cl` on `treeDel m' j bt`, which their
  directories and `jr` do not see). The inodes stay `Nodup` (`hino`). `AbsentOk` from `AbsentNone`
  (`absentOk_of_absentNone`); `DirsOk`: a lookup succeeding in `treeDel m' j bt` reads no `(j, bt)`.
- `WalsCreateOk`, `CreatingOk`, `AbsentNone`: claims of `jr` unchanged (`j ≠ jr`); a creating entry's
  `J` is not `j` (`CreatingNew`: no claim of `J` holds a `.wal` name).
- `WalsNamed`: the new segment at `bt` in the new claim; in a crash keeping the rename, the names as
  the new claim has them; in one dropping it, `g.ino` is in no `.wal` entry of `j` (`SegsNamedC`'s
  last clause, added for this: a crash names only segments at `.wal` names; the old crash condition
  would give it too, but only for crashes whose files exist, `FileCrashedR`, which the pure
  conjunct cannot produce: the segments' `zf` is not recorded).
- The history ends at a cut position (`hcpos`, `walCutPos`): `cut` runs after a `Save` that wrote a
  record, a premise the caller (`cut.spec`) carries.
- `DirKeysOk`: the key's claim replaced, once (`claimOnce_repl`), coherent, still exclusive; the
  other WALs' `CrashOkA … none` as above.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutCommitLemmas

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Fs WalEnc

section pure
variable [GooseExts]

/-- **The WAL directory's claim after the cut's rename** (logged at `x` by a call begun at `s0`):
`bt` now holds the new segment `i`. -/
def cutClaim (j : Ino) (X : List GoString) (hj : NamesH) (tmp bt : GoString) (i : Ino) (x s0 : Nat) :
    Claim :=
  (j, .except X, hj.log x (renFileEnt j tmp j bt i hj s0) (<[bt := .file i]> hj.cur))

/-- **`Create`'s claim of the area survives a claim of another directory replaced.** -/
theorem walsCreateOk_cut {jr : Ino} {cl : List Claim} {c0 c1 : Claim} (h0 : c0.1 ≠ jr)
    (h : WalsCreateOk jr cl) : WalsCreateOk jr (replClaim c0 c1 cl) := by
  classical
  intro nm hnm
  obtain ⟨N, hN, hm, hMem⟩ := h nm hnm
  refine ⟨N, hN, ?_, hMem⟩
  have := mem_replClaim (c0 := c0) (c1 := c1) hm
  rwa [if_neg (fun e => h0 (by rw [← e]))] at this

/-- **The pure facts after a cut's rename commit** (see the file header). The old state: the
invariant's pure conjuncts (`hW` … `hDK`, no cut pending), the WAL `d` of `dir` with its layout `lay`
(the last segment `g0`), its key `(j, X)` and claim `(j, .except X, hj)`. The old tail synced and
truncated (`hm`, `hlast0`), the cuts below `|H|`. The names: `nm0` holds the old tail, `bt` (free, a
`.wal` name past `nm0`, its index past the history's) the new segment. The new segment `g`: its bytes
the stream of the new segment (`wr` bytes) then zeros, durable, its `OsMeta` sized to them, a fresh
inode. The rename: `tmp ∈ X`, begun after the claim's last entry. -/
theorem cutCommit_pure {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat}
    {CR : GMap GoString (NameSet × NamesH × Ino)} {K : GMap GoString (Ino × List GoString)}
    {dir : GoString} {d : WalDur} {lay : WalLay} {g0 g : SegG} {j : Ino} {X : List GoString}
    {hj : NamesH} {tmp bt nm0 : GoString} {x s0 wr sq ix : Nat}
    (hW : WalsOk C Mr R jr s Ls cl n) (hWC : WalsCreateOk jr cl) (hCO : CreatingOk jr cl CR)
    (hAN : AbsentNone s jr cl n) (_hDA : DirsAvoid R jr s) (hNm : WalsNamed Ls cl n)
    (hDK : DirKeysOk C Mr jr s Ls cl n K none) (hK : K !! dir = some (j, X))
    (hd : s.wal !! dir = some d) (hl : Ls !! dir = some lay) (hg0 : lay.segs.getLast? = some g0)
    (hc0 : ClaimOnce (j, .except X, hj) cl)
    (hm : d.m = d.H.length) (_hnamed : d.named = true)
    (hlast0 : g0.bs = (segStream C Mr d lay.cuts lay.cuts.length).map durB) (hex0 : SegExact g0)
    (hcuts : ∀ b ∈ lay.cuts, b < d.H.length) (hcpos : walCutPos (histM d) d.H.length)
    (hnm0 : walNameP nm0 = true ∧ hj.cur !! nm0 = some (.file g0.ino))
    (hbt : bt = walFileName sq ix ∧ walLastIdx (histM d) + 1 ≤ ix ∧ go.GoStringLt nm0 bt)
    (hbtw : walNameP bt = true) (hcur : hj.cur !! bt = none)
    (hwr : wr = (segStream C Mr d (lay.cuts ++ [d.H.length]) (lay.cuts.length + 1)).length)
    (hbs : g.bs = ((segStream C Mr d (lay.cuts ++ [d.H.length]) (lay.cuts.length + 1)) ++
      List.replicate (g.bs.length - wr) 0).map durB ∧ wr ≤ g.bs.length)
    (hmeta : g.om.size = g.bs.length ∧ g.om.cut = none ∧ g.om.lo = g.bs.length ∧
      g.om.hi = g.bs.length)
    (hfit : RecsFit C (recsOfSegs C Mr d.metadata (segsOf (histM d) (lay.cuts ++ [d.H.length]))))
    (hz : g.bs.length - wr = 0 ∨ 8 ≤ g.bs.length - wr)
    (hino : ∀ g' ∈ segsAll Ls, g'.ino ≠ g.ino) (hgname : g.name = bt)
    (htmpX : tmp ∈ X) (hs0 : hj.next ≤ s0) (hsx : s0 ≤ x) :
    WalsOk C Mr R jr s (<[dir := cutLay lay d.H.length g wr]> Ls)
        (replClaim (j, .except X, hj) (cutClaim j X hj tmp bt g.ino x s0) cl) n ∧
      WalsCreateOk jr (replClaim (j, .except X, hj) (cutClaim j X hj tmp bt g.ino x s0) cl) ∧
      CreatingOk jr (replClaim (j, .except X, hj) (cutClaim j X hj tmp bt g.ino x s0) cl) CR ∧
      AbsentNone s jr (replClaim (j, .except X, hj) (cutClaim j X hj tmp bt g.ino x s0) cl) n ∧
      WalsNamed (<[dir := cutLay lay d.H.length g wr]> Ls)
        (replClaim (j, .except X, hj) (cutClaim j X hj tmp bt g.ino x s0) cl) n ∧
      DirKeysOk C Mr jr s (<[dir := cutLay lay d.H.length g wr]> Ls)
        (replClaim (j, .except X, hj) (cutClaim j X hj tmp bt g.ino x s0) cl) n K (some dir) := by
  classical
  unfold cutClaim
  obtain ⟨lay1, hj1, hl1, hlj, hjjr, hX, -, hcoh1, hexcl1⟩ := hDK.1 dir j X hK
  rw [hl] at hl1
  cases hl1
  subst hlj
  have hcl : (lay.j, NameSet.except X, hj) ∈ cl := claimOnce_mem hc0
  have hj1e := walClaim_eq hexcl1 hX hcl
  simp only [Prod.mk.injEq, true_and] at hj1e
  subst hj1e
  have hs : hj.next ≤ (renFileEnt lay.j tmp lay.j bt g.ino hj s0).start := hs0
  have hbt' : ∀ b, (NameSet.except X).Mem b →
      (renFileEnt lay.j tmp lay.j bt g.ino hj s0).op.Writes lay.j b → b = bt := by
    intro b hb hw
    rcases ((renFileEnt_writes _ _ _ _ _ _ _ _).1 hw).2 with hbe | hbe
    · rw [hbe] at hb; exact absurd htmpX hb
    · exact hbe
  have hothers : ∀ c' ∈ cl, c' ≠ (lay.j, NameSet.except X, hj) → c'.1 = lay.j →
      ¬ c'.2.1.Mem bt := fun c' hc hne hcj => hexcl1 c' hc hne hcj bt hbtw
  have hcoh' : ClaimCoh (hj.log x (renFileEnt lay.j tmp lay.j bt g.ino hj s0)
      (<[bt := Node.file g.ino]> hj.cur)) lay.j (.except X) := by
    refine claimCoh_log _ _ _ _ _ _ hcoh1 (Nat.le_trans hs0 hsx) (fun b _ hw => ?_)
    have hne : bt ≠ b := fun e => hw ((renFileEnt_writes _ _ _ _ _ _ _ _).2 ⟨rfl, Or.inr e.symm⟩)
    exact GMap.lookup_insert_ne _ _ hne
  -- the old static relation, over the claim's names
  obtain ⟨la, nm, hja, hla, hin, hjr, hnm, ⟨Xa, hXa, hma, -⟩, habs, -⟩ := hW.1 dir d hd
  rw [hl] at hla
  cases hla
  have hjae := walClaim_eq hexcl1 hXa hma
  simp only [Prod.mk.injEq, true_and] at hjae
  rw [hjae.2] at habs
  have hnodup := (segsAll_nodup_iff Ls).1 hW.2.2.1
  have hnd0 : (walInos hj.cur).Nodup := by rw [habs.names.1]; exact hnodup.1 dir lay hl
  have hsn : SegsNamed lay.segs hj.cur := (hNm dir lay hl).1 hj ⟨X, hX, hcl, hcoh1⟩
  have hg0mem : g0 ∈ lay.segs := List.mem_of_getLast? hg0
  have hnm0e : nm0 = g0.name :=
    walName_unique_nd hnd0 hnm0.1 (hsn.1 g0 hg0mem).1 hnm0.2 (hsn.1 g0 hg0mem).2
  -- `bt` is the largest `.wal` name
  have hlt : ∀ g' ∈ lay.segs, go.GoStringLt g'.name bt := by
    intro g' hg'
    rcases pairwise_last_name habs.names.2 hg0 g' hg' with h | h
    · rw [h, ← hnm0e]; exact hbt.2.2
    · rw [hnm0e] at hbt; exact go.goStringLt_trans h hbt.2.2
  have hents : walInos (<[bt := Node.file g.ino]> hj.cur) = walInos hj.cur ++ [g.ino] := by
    refine walInos_insert_last hbtw hcur (fun b e hb he => ?_)
    obtain ⟨i, rfl⟩ := hsn.2 b e hb he
    have hi := mem_walInos hb he
    rw [habs.names.1] at hi
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hi
    have : b = g'.name := walName_unique_nd hnd0 hb (hsn.1 g' hg').1 he (hsn.1 g' hg').2
    rw [this]; exact hlt g' hg'
  have hexL : TailExact lay := fun g1 hg1 => by rw [hg0] at hg1; exact Option.some.inj hg1 ▸ hex0
  have habs' : WalAbsD C Mr d (cutLay lay d.H.length g wr) (<[bt := Node.file g.ino]> hj.cur) :=
    cutLay_abs C Mr d lay hj.cur _ g wr sq ix habs hexL hm
      (fun g0' h => by rw [hg0] at h; cases h; exact hlast0) ⟨hcpos, hcuts⟩
      ⟨hgname.trans hbt.1, hbt.2.1, fun g' hg' => by rw [hgname]; exact hlt g' hg'⟩ hwr hbs hmeta
      hfit hents hz
  -- every byte durable
  have hdur : ∀ g' ∈ lay.segs, ∀ y ∈ g'.bs, y = durB y.1 := by
    intro g' hg' y hy
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hg'
    by_cases hk1 : k + 1 < lay.segs.length
    · rw [habs.intact k g' hk1 hk] at hy
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hy
      rfl
    · have hkl : k < lay.segs.length := (List.getElem?_eq_some_iff.1 hk).1
      have hlast : lay.segs.getLast? = some g' := by
        rw [List.getLast?_eq_getElem?, show lay.segs.length - 1 = k by omega]; exact hk
      rw [hg0] at hlast
      cases hlast
      rw [hlast0] at hy
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hy
      rfl
  have hdurg : ∀ y ∈ g.bs, y = durB y.1 := by
    intro y hy
    rw [hbs.1] at hy
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hy
    rfl
  -- the cut WAL's crash condition, with the old layout as the alternative
  have hok0 : CrashOk C Mr d lay cl n :=
    (crashOkA_none_iff C Mr d lay cl n).1 (hDK.2.1 dir d lay hd hl (fun h => by cases h))
  have hcr' := crashOkA_cut C Mr d lay hj.cur cl n X hj x (renFileEnt lay.j tmp lay.j bt g.ino hj s0)
    (<[bt := Node.file g.ino]> hj.cur) bt g wr hok0 habs hexL habs' hmeta.2.2 hm hdur hdurg hwr hz hX hcl hcoh1
    hcoh' hs hbt' hcur hothers (Or.inl (by rw [hjr]; exact Ne.symm hjjr))
  have hWnew : WalsOk C Mr R jr s (<[dir := cutLay lay d.H.length g wr]> Ls)
      (replClaim (lay.j, NameSet.except X, hj) (lay.j, NameSet.except X, hj.log x
        (renFileEnt lay.j tmp lay.j bt g.ino hj s0) (<[bt := Node.file g.ino]> hj.cur)) cl) n := by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hW
    refine ⟨fun dir' d' hd' => ?_, fun dir' hn' => ?_, ?_, ?_,
      absentOk_of_absentNone (absentNone_cut hAN hjjr hcl hcoh1 hs hbt' hcur hothers),
      dirsOk_cut h6 hcl hcoh1 hs hbt' hcur hothers⟩
    · by_cases hdd : dir' = dir
      · subst hdd
        rw [hd] at hd'
        cases hd'
        exact ⟨cutLay lay d.H.length g wr, nm, _, GMap.lookup_insert_eq .., hin, hjr, hnm,
          ⟨X, hX, mem_replClaim_new hcl, hcoh'⟩, habs', some lay,
          fun lay0 h => by cases h; exact altOk_cut C Mr d lay hj.cur _ g wr habs, hcr'⟩
      · obtain ⟨lay', nm', hj', hl', hin', hjr', hnm', ⟨X', hX', hm', hc'⟩, habs'', alt, halt, hcr⟩ :=
          h1 dir' d' hd'
        have hne := walsOk_dir_ne ⟨h1, h2, h3, h4, h5, h6⟩ hexcl1 hd hl rfl hdd hl'
        refine ⟨lay', nm', hj', by rw [GMap.lookup_insert_ne _ _ (Ne.symm hdd)]; exact hl', hin',
          hjr', hnm', ⟨X', hX', mem_replClaim_of_ne hm' (fun e => hne (by
            simp only [Prod.mk.injEq] at e; exact e.1)), hc'⟩, habs'', alt, halt,
          crashOkA_cut_other hcr (fun l0 h0 => ⟨(halt l0 h0).2.1, (halt l0 h0).2.2.1,
            (halt l0 h0).2.2.2.1⟩) hne (by rw [hjr']; exact Ne.symm hjjr) hcl hcoh1 hs hbt' hcur
            hothers⟩
    · have hdd : dir' ≠ dir := by
        intro e; rw [e, hd] at hn'; cases hn'
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hdd)]
      exact h2 dir' hn'
    · have hseg : ∀ dd ll, (<[dir := cutLay lay d.H.length g wr]> Ls) !! dd = some ll →
          ∀ g' ∈ ll.segs, (dd = dir ∧ g' = g) ∨ ∃ ll', Ls !! dd = some ll' ∧ g' ∈ ll'.segs := by
        intro dd ll hll g' hg'
        by_cases hdd : dd = dir
        · rw [hdd, GMap.lookup_insert_eq] at hll
          cases hll
          simp only [cutLay, List.mem_append, List.mem_singleton] at hg'
          rcases hg' with hg' | hg'
          · exact Or.inr ⟨lay, by rw [hdd]; exact hl, hg'⟩
          · exact Or.inl ⟨hdd, hg'⟩
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm hdd)] at hll
          exact Or.inr ⟨ll, hll, hg'⟩
      refine (segsAll_nodup_iff _).2 ⟨fun dir' lay' hl' => ?_,
        fun d1 d2 l1 l2 hne' hl1 hl2 g1 hg1 g2 hg2 => ?_⟩
      · by_cases hdd : dir' = dir
        · rw [hdd, GMap.lookup_insert_eq] at hl'
          cases hl'
          simp only [cutLay, List.map_append, List.map_cons, List.map_nil]
          refine List.nodup_append.2 ⟨hnodup.1 dir lay hl, by simp, fun a ha b hb => ?_⟩
          simp only [List.mem_singleton] at hb
          obtain ⟨g', hg', rfl⟩ := List.mem_map.1 ha
          rw [hb]; exact hino g' (mem_segsAll hl hg')
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm hdd)] at hl'
          exact hnodup.1 dir' lay' hl'
      · rcases hseg d1 l1 hl1 g1 hg1 with ⟨e1, e1'⟩ | ⟨k1, hk1, hg1'⟩ <;>
          rcases hseg d2 l2 hl2 g2 hg2 with ⟨e2, e2'⟩ | ⟨k2, hk2, hg2'⟩
        · exact absurd (e1.trans e2.symm) hne'
        · rw [e1']; exact (hino g2 (mem_segsAll hk2 hg2')).symm
        · rw [e2']; exact hino g1 (mem_segsAll hk1 hg1')
        · exact hnodup.2 d1 d2 k1 k2 hne' hk1 hk2 g1 hg1' g2 hg2'
    · intro g' hg'
      obtain ⟨dd, ll, hll, hg''⟩ := segsAll_mem hg'
      by_cases hdd : dd = dir
      · rw [hdd, GMap.lookup_insert_eq] at hll
        cases hll
        simp only [cutLay, List.mem_append, List.mem_singleton] at hg''
        rcases hg'' with hg'' | hg''
        · exact h4 g' (mem_segsAll hl hg'')
        · rw [hg'']; exact hmeta.2.1
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hdd)] at hll
        exact h4 g' (mem_segsAll hll hg'')
  refine ⟨hWnew, walsCreateOk_cut hjjr hWC,
    creatingOk_cut hCO hjjr hcl ⟨_, walNameP_wal, except_mem_wal hX⟩,
    absentNone_cut hAN hjjr hcl hcoh1 hs hbt' hcur hothers,
    walsNamed_cut hW hNm hd hl hcl hX hcoh1 hcoh' hexcl1 hs hbt' hcur hbtw hgname hino
      (by rw [hents, habs.names.1]),
    dirKeysOk_cut hW hDK hK hd hl rfl hjjr hX hc0 hcoh1 hcoh' hexcl1 hs hbt' hcur hbtw⟩

end pure

end WalFs
end EtcdGrove
end Perennial

end
