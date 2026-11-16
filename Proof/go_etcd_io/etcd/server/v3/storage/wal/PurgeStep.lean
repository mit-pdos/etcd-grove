/- Lean-first (no Rocq counterpart).

# A purge's removal keeps the crash condition (unit `locks`, session 8; `notes/wal-units/locks.md`)

Pure. The purge's `os.Remove` of the first named segment `g0` (at index `t` of the full layout `F`, the
layout with this generation's removed segments back, `unpurge`) logs, on the WAL directory's claim, an entry
writing only its name `bt`. The crash condition stays stated on `F`, which the purge does not move
(`unpurge_purge`); `crashOkA_purgeF` re-proves it over the logged claim, `pur` raised past `g0`'s end:

* a crash dropping the removal is a crash of the claims before it (`regionCrashedK_unlog`): the old condition;
* a crash keeping it keeps every earlier entry of the claim, so the WAL directory's `.wal` names are the
  claim's current ones, without `bt` (`walInos c = gs`); with `bt` set back to `g0` (`treeSetE`) it is a
  crash of the claims before it (`regionCrashedK_keptSet`), whose `.wal` names are `g0 :: gs`. The old
  condition applies there, with `g0`'s file its durable image (`syncImg`; `FileCrashedR` needs its zeros known
  from its size on, `hzf0`, which the invariant's `WalFullOk` records) and W1 with `g0`'s file in front
  (`w1G_cons_durable`, `PurgeW1.lean`), and gives `CrashTo` of `F` keeping the segments from `t` on; the
  crash keeps them from `t + 1` on (`crashTo_dropFirst`), and reads no file of `g0` (`crashTo_congr_kept`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.PurgeW1

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- A segment before the last is exact (its inode not the last one's). -/
theorem WalAbsD.exact_of_lt {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    (habs : WalAbsD C Mr d lay ents) (hnd : (lay.segs.map (·.ino)).Nodup) {k : Nat} {g : SegG}
    (hk : k + 1 < lay.segs.length) (hg : lay.segs[k]? = some g) : SegExact g := by
  rcases (habs.metas g (List.mem_of_getElem? hg)).2.2.2.2 with hl | hx
  · exfalso
    have h1 : (lay.segs.map (·.ino))[k]? = some g.ino := by rw [List.getElem?_map, hg]; rfl
    have h2 : (lay.segs.map (·.ino))[lay.segs.length - 1]? = some g.ino := by
      rw [List.getElem?_map, ← List.getLast?_eq_getElem?, hl]; rfl
    have := hnd.eq_of_getElem?_eq (by simp only [List.length_map]; omega) (h1.trans h2.symm)
    omega
  · exact hx

/-- The image of a durable segment as of its last sync is its bytes. -/
theorem syncImg_durable {bs : List ByteG} (hdur : ∀ y ∈ bs, y = durB y.1) :
    (syncImg bs bs.length).contents = bs.map (·.1) := by
  apply List.ext_getElem (by rw [syncImg_length, List.length_map])
  intro k h1 h2
  have hk : k < bs.length := by simpa using h2
  have := syncImg_getD bs bs.length k hk
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some] at this
  rw [this, List.getElem_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  rw [hdur _ (List.getElem_mem hk)]
  exact valAt_durB _

/-- **A durable exact segment's image as of its last sync is a crash its halves allow**, its zeros known
from its size on. -/
theorem fileCrashedR_durSeg {g : SegG} (hsz : g.om.size = g.bs.length) (hex : SegExact g)
    (hdur : ∀ y ∈ g.bs, y = durB y.1) (hzf : ∀ z, g.om.zf = some z → g.om.size ≤ z) (dq : DFrac) :
    FileCrashedR g.om [(0, dq, g.bs)] (some (syncImg g.bs g.bs.length)) := by
  intro f' hf'
  cases hf'
  have hsz' : (syncImg g.bs g.bs.length).size = g.bs.length := rfl
  refine ⟨⟨_, rfl⟩, by rw [hsz', hex.1]; exact Nat.le_refl _, by rw [hsz', hex.2]; exact Nat.le_refl _, ?_, ?_, fun b c hb _ hb2 => by omega⟩
  · intro r hr k hk hks
    rw [List.mem_singleton] at hr; subst hr
    simp only [Nat.zero_add] at hks ⊢
    left
    rw [syncImg_cache g.bs g.bs.length k (by simpa using hk)]
    have e : g.bs.getD k (0, []) = g.bs[k]'hk := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    rw [e]
    have hy := hdur _ (List.getElem_mem hk)
    refine ⟨0, ?_⟩
    rw [hy, valAt_durB]
    exact List.mem_singleton_self _
  · intro z hz b hzb hb
    have := hzf z hz; omega

/-- `CrashTo` bounds the first kept segment's start by `pur` only from above. -/
theorem crashTo_pur {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {m' : Tree}
    {fo : Ino → Option Fs.OsFile} {P : Nat} (hP : d.pur ≤ P) (h : CrashTo C Mr d lay m' fo) :
    CrashTo C Mr { d with pur := P } lay m' fo := by
  rcases h with ⟨hn, h⟩ | ⟨q, I, hent, hq, hinos, hI, hlen, hst, hk, hlast⟩
  · exact Or.inl ⟨hn, h⟩
  refine Or.inr ⟨q, I, hent, hq, hinos, hI, hlen, ?_, hk, hlast⟩
  show _ ≤ min P I.length
  omega

/-- `CrashTo` reads the files only at the segments the crashed directory lists. -/
theorem crashTo_congr_kept {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {m' : Tree}
    {fo fo' : Ino → Option Fs.OsFile}
    (hfo : ∀ g ∈ lay.segs, g.ino ∈ walInos (entsOf m' lay.j) → fo g.ino = fo' g.ino)
    (h : CrashTo C Mr d lay m' fo) : CrashTo C Mr d lay m' fo' := by
  rcases h with h | ⟨q, I, h1, h2, h3, h4, h5, h6, h7, h8⟩
  · exact Or.inl h
  refine Or.inr ⟨q, I, h1, h2, h3, h4, h5, h6, fun k g hk hkc => ?_, fun g hg => ?_⟩
  · have hm := List.mem_of_getElem? hk
    rw [← hfo g (List.mem_of_mem_drop hm) (by rw [h3]; exact List.mem_map_of_mem hm)]
    exact h7 k g hk hkc
  · have hm : g ∈ lay.segs.drop q := by
      apply List.mem_of_getLast?; rw [List.getLast?_drop, if_neg (by omega), hg]
    rw [← hfo g (List.mem_of_getLast? hg) (by rw [h3]; exact List.mem_map_of_mem hm)]
    exact h8 g hg

/-- **A purge's removal keeps the crash condition** (see the file header). The full layout `F` (static
relation `hF`, inodes `Nodup`) lists `g0 :: gs` from index `t` on (`gs` nonempty: `g0` is not the last); the
claim `(j, except X, h)` (coherent, `X` no `.wal` name) holds `g0` at `bt`, its `.wal` names `g0 :: gs`; the
removal (the entry `e` at `x`, by a call begun after the claim's last entry) writes only `bt`, the names after
it `c` (`.wal` names `gs`); `pur` raised to `P`, past `g0`'s end. -/
theorem crashOkA_purgeF {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {D : WalDur} {F : WalLay}
    {ents0 : Ents} (hF : WalAbsD C Mr D F ents0) (hnd : (F.segs.map (·.ino)).Nodup)
    {t : Nat} {g0 : SegG} {gs : List SegG} (hFs : F.segs.drop t = g0 :: gs) (hgs : gs ≠ [])
    (hzf0 : ∀ z, g0.om.zf = some z → g0.om.size ≤ z)
    {cl : List Claim} {n : Nat} {X : List GoString} {h : NamesH} {x : Nat} {e : LogEntry} {c : Ents}
    {bt : GoString} (hX : ∀ b ∈ X, walNameP b = false)
    (hcl : (F.j, NameSet.except X, h) ∈ cl) (hcoh : ClaimCoh h F.j (.except X))
    (hcoh' : ClaimCoh (h.log x e c) F.j (.except X)) (hs : h.next ≤ e.start)
    (hbt : ∀ b, (NameSet.except X).Mem b → e.op.Writes F.j b → b = bt)
    (hothers : ∀ c' ∈ cl, c' ≠ (F.j, NameSet.except X, h) → c'.1 = F.j → ¬ c'.2.1.Mem bt)
    (hcur0 : h.cur !! bt = some (.file g0.ino))
    (hwal : walInos h.cur = (g0 :: gs).map (·.ino)) (hwal' : walInos c = gs.map (·.ino))
    {P : Nat} (hP : D.pur ≤ P) (hpur : segStart F.cuts (F.first + (t + 1)) ≤ P)
    (hok : CrashOkA C Mr D F none cl n) :
    CrashOkA C Mr { D with pur := P } F none
      (replClaim (F.j, NameSet.except X, h) (F.j, NameSet.except X, h.log x e c) cl) n := by
  classical
  intro m' fo hr hf hn hw
  obtain ⟨K, hK⟩ := (regionCrashed_iff _ _ _).1 hr
  have hnone : ∀ {m : Tree} {fo : Ino → Option Fs.OsFile}, (CrashTo C Mr D F m fo ∨
      ∃ lay0, (none : Option WalLay) = some lay0 ∧ CrashTo C Mr D lay0 m fo) → CrashTo C Mr D F m fo := by
    intro m fo h
    rcases h with h | ⟨_, h, _⟩
    · exact h
    · cases h
  by_cases hx : K x
  rotate_left
  · -- the removal dropped: a crash of the claims before it
    left
    exact crashTo_pur hP (hnone (hok m' fo ((regionCrashed_iff _ _ _).2
      ⟨K, regionCrashedK_unlog cl n m' K F.j _ h x e c hK hx⟩) hf hn hw))
  -- the removal kept: every entry of the claim kept
  left
  obtain ⟨hold, hK''⟩ := regionCrashedK_keptSet cl n m' K F.j _ h x e c bt hK hx hcl hcoh hs hbt
    hothers
  generalize hm'' : treeSetE m' F.j bt (h.cur !! bt) = m'' at hK''
  have hc1 : (F.j, NameSet.except X, h.log x e c) ∈
      replClaim (F.j, NameSet.except X, h) (F.j, NameSet.except X, h.log x e c) cl := by
    simpa using mem_replClaim (c0 := (F.j, NameSet.except X, h))
      (c1 := (F.j, NameSet.except X, h.log x e c)) hcl
  have hwN : ∀ b, walNameP b = true → (NameSet.except X).Mem b := fun b hb hbX => by
    rw [hX b hbX] at hb; cases hb
  -- the crashed directory's `.wal` files: without `g0`, and with it back
  have hwi' : walInos (entsOf m' F.j) = gs.map (·.ino) := by
    rw [← hwal']
    refine walInos_congr (fun b hb => ?_)
    rw [entsOf_lookup_entry, hK.2.2 _ hc1 b (hwN b hb)]
    refine hcoh'.2 K (fun xe hxe => ?_) b (hwN b hb)
    simp only [NamesH.log, List.mem_append, List.mem_singleton] at hxe
    rcases hxe with hxe | rfl
    · exact hold xe hxe
    · exact hx
  have hwi'' : walInos (entsOf m'' F.j) = (g0 :: gs).map (·.ino) := by
    rw [← hwal]
    refine walInos_congr (fun b hb => ?_)
    rw [entsOf_lookup_entry, hK''.2.2 _ hcl b (hwN b hb), hcoh.2 K hold b (hwN b hb)]
  -- `g0`: intact, exact, durable
  have hlen : F.segs.length = t + (gs.length + 1) := by
    have := congrArg List.length hFs
    simp only [List.length_drop, List.length_cons] at this
    omega
  have hgsl : 0 < gs.length := List.length_pos_iff.2 hgs
  have hg0t : F.segs[t]? = some g0 := by
    have := congrArg (·[0]?) hFs
    simp only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] at this
    exact this
  have hg0m : g0 ∈ F.segs := List.mem_of_getElem? hg0t
  have hex0 : SegExact g0 := hF.exact_of_lt hnd (by omega) hg0t
  have hint0 := hF.intact t g0 (by omega) hg0t
  have hdur0 : ∀ y ∈ g0.bs, y = durB y.1 := by
    intro y hy
    rw [hint0] at hy
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 hy
    rfl
  have hsz0 : g0.om.size = g0.bs.length := (hF.metas g0 hg0m).1
  have hnd' : ((g0 :: gs).map (·.ino)).Nodup := by
    rw [← hFs, List.map_drop]; exact hnd.sublist (List.drop_sublist _ _)
  have hni : g0.ino ∉ gs.map (·.ino) := (List.nodup_cons.1 hnd').1
  -- the files with `g0`'s durable image
  generalize hfo'' : (fun i => if i = g0.ino then some (syncImg g0.bs g0.bs.length) else fo i) = fo''
  have hfo0 : fo'' g0.ino = some (syncImg g0.bs g0.bs.length) := by rw [← hfo'']; simp
  have hfoi : ∀ i, i ≠ g0.ino → fo'' i = fo i := fun i hi => by rw [← hfo'']; simp [hi]
  have hsame : ∀ g ∈ F.segs, g.ino = g0.ino → g = g0 := fun g hg he =>
    Fs.eq_of_nodup_map hnd hg hg0m he
  -- the old condition at the tree with `g0` back
  have hct := hnone (hok m'' fo'' ((regionCrashed_iff _ _ _).2 ⟨K, hK''⟩)
    (fun g hg => by
      by_cases he : g.ino = g0.ino
      · obtain rfl := hsame g hg he
        rw [hfo0]
        exact fileCrashedR_durSeg hsz0 hex0 hdur0 hzf0 _
      · rw [hfoi _ he]; exact hf g hg)
    (fun g hg hin => by
      by_cases he : g.ino = g0.ino
      · rw [he, hfo0]; rfl
      · rw [hfoi _ he]
        refine hn g hg ?_
        rw [hwi''] at hin
        rw [hwi']
        rcases List.mem_cons.1 hin with h1 | h1
        · exact absurd h1 he
        · exact h1)
    (by
      rw [hwi'']
      rw [hwi'] at hw
      refine w1G_cons_durable (img := fun i => imgOf (fo i)) hw (fun i hi => ?_)
        (segBytesOf_mem_ex hnd hg0m (Nat.le_of_eq hex0.2)) hdur0
        (by simp only [hfo0, imgOf, Option.map_some, Option.getD_some]; exact syncImg_durable hdur0)
        (fun i1 js' hij => ?_)
      · have hne : i ≠ g0.ino := fun he => hni (he ▸ hi)
        simp only [hfoi i hne]
      · -- the next file starts with its CRC record
        obtain ⟨g1, gs', rfl, rfl, -⟩ : ∃ g1 gs', gs = g1 :: gs' ∧ g1.ino = i1 ∧ gs'.map (·.ino) = js' := by
          cases gs with
          | nil => exact absurd rfl hgs
          | cons g1 gs' =>
            simp only [List.map_cons, List.cons.injEq] at hij
            exact ⟨g1, gs', rfl, hij.1, hij.2⟩
        have hg1t : F.segs[t + 1]? = some g1 := by
          have := congrArg (·[1]?) hFs
          simp only [List.getElem?_drop, List.getElem?_cons_succ, List.getElem?_cons_zero] at this
          exact this
        have hg1m : g1 ∈ F.segs := List.mem_of_getElem? hg1t
        have hin1 : g1.ino ∈ walInos (entsOf m' F.j) := by rw [hwi']; simp
        obtain ⟨f1, hf1⟩ := Option.isSome_iff_exists.1 (hn g1 hg1m hin1)
        have hfc1 := hf g1 hg1m
        rw [hf1] at hfc1
        simp only [imgOf, hf1, Option.map_some, Option.getD_some]
        by_cases hlast : t + 2 < F.segs.length
        · exact intact_head hC hF (k := t + 1) hlast hg1t (hF.exact_of_lt hnd hlast hg1t) hfc1 _
        · have hg1l : F.segs.getLast? = some g1 := by
            rw [List.getLast?_eq_getElem?, show F.segs.length - 1 = t + 1 by omega, hg1t]
          have hcne : F.cuts ≠ [] := by
            intro h0
            have := hF.cuts.2.2
            rw [h0] at this
            simp only [List.length_nil] at this
            omega
          exact tail_head hC hF hg1l hcne hfc1 _))
  have hct' := crashTo_pur hP hct
  -- `CrashTo` from `t + 1` on, at `m'`
  have hentE : ∀ jr nm, ¬ (jr = F.j ∧ nm = bt) → m''.entry jr nm = m'.entry jr nm :=
    fun jr nm hne => by rw [← hm'', treeSetE_entry, if_neg hne]
  have hentB : m''.entry F.j bt = some (.file g0.ino) := by
    rw [← hm'', treeSetE_entry, if_pos ⟨rfl, rfl⟩, hcur0]
  refine crashTo_congr_kept (fo := fo'') (fun g hg hin => ?_) ?_
  · have he : g.ino ≠ g0.ino := by
      intro he; rw [hwi', he] at hin; exact hni hin
    exact hfoi _ he
  rcases hct' with ⟨hnamed, hab⟩ | hpres
  · have hne : ¬ (F.jr = F.j ∧ F.nm = bt) := fun ⟨h1, h2⟩ => by
      rw [h1, h2, hentB] at hab; cases hab
    exact Or.inl ⟨hnamed, by rw [← hentE _ _ hne]; exact hab⟩
  · obtain ⟨q, I, hentF, -⟩ := id hpres
    have hne : ¬ (F.jr = F.j ∧ F.nm = bt) := fun ⟨h1, h2⟩ => by
      rw [h1, h2, hentB] at hentF; cases hentF
    have hdrop1 : F.segs.drop (t + 1) = gs := by
      rw [← List.drop_drop, hFs]; rfl
    exact crashTo_dropFirst (t := t) (Or.inr hpres) hF.cuts.2.1 hF.cuts.2.2
      (by rw [← hentE _ _ hne]; exact hentF) hentF (by rw [hwi'', hFs])
      (by rw [hwi', hdrop1]) (by omega) hpur

end pure

end WalFs
end EtcdGrove
end Perennial

end
