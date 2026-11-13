/- Lean-first (no Rocq counterpart).

# The tail's fdatasync: the invariant's pure part (W6 of `notes/wal-fsext-plan.md`, "W6 implementation log")

`sync` (S/wal.go:967-992) flushes the encoder, then `fdatasync`s the tail. The fdatasync's commit (every
record encoded and flushed: the write position `wr` at the end of the tail's stream, no write in flight)
raises the WAL's synced mark to its whole history (`d.m := |H|`), and the layout's tail becomes
`syncTail g0` (its `OsMeta` synced, every byte durable): `syncLay lay pre g0` (`SaveAbs.lean`).

* `tailBound_sync`: the record boundary of the synced layout is the end of the stream.
* `crashOk_sync`: the crash condition of the synced WAL (as `crashOkA_tail`, the tail imaged as of the
  last sync for the old condition, then `crashTo_tailM` at the raised mark).
* `walsOk_sync`, `dirKeysOk_sync`, `absentNone_sync`, `dirsAvoid_sync`, `walsNamed_relay`,
  `walsAt_relay`: the invariant's pure conjuncts at the new state `walSyncS s dir d` and layouts.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailAcc
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.SaveAbs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

section pure
variable [GooseExts]

/-- **The WAL state after `dir`'s sync**: its synced mark at its whole history. -/
def walSyncS (s : AbsDiskState) (dir : GoString) (d : WalDur) : AbsDiskState :=
  { s with wal := <[dir := { d with m := d.H.length }]> s.wal }

theorem walSyncS_lookup_ne (s : AbsDiskState) (dir : GoString) (d : WalDur) {k : GoString}
    (h : k ≠ dir) : (walSyncS s dir d).wal !! k = s.wal !! k :=
  GMap.lookup_insert_ne _ _ (Ne.symm h)

theorem walSyncS_lookup (s : AbsDiskState) (dir : GoString) (d : WalDur) :
    (walSyncS s dir d).wal !! dir = some { d with m := d.H.length } :=
  GMap.lookup_insert _ _ _

/-- The z0 of a layout is below its write position. -/
theorem tailBound_sync {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    {pre : List SegG} {g0 : SegG} (habs : WalAbsD C Mr d lay ents) (hs : lay.segs = pre ++ [g0])
    (htail : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length) :
    TailBound C Mr { d with m := d.H.length } (syncLay lay pre g0) := by
  have hg0 : lay.segs.getLast? = some g0 := by rw [hs]; simp
  obtain ⟨-, -, -, -, -, hz0, -, -⟩ := habs.last g0 hg0
  refine ⟨((segRecs C Mr { d with m := d.H.length } lay.cuts).getD lay.cuts.length []).length,
    Nat.le_refl _, ?_⟩
  show (recFrames C (((segRecs C Mr d lay.cuts).getD lay.cuts.length []).take
    ((segRecs C Mr d lay.cuts).getD lay.cuts.length []).length)).length = max lay.wr lay.z0
  rw [List.take_length]
  show (segStream C Mr d lay.cuts lay.cuts.length).length = max lay.wr lay.z0
  rw [← htail]; omega

/-- **The crash condition after the tail's fdatasync** (see the file header). -/
theorem crashOk_sync {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {ents : Ents} {cl : List Claim} {n : Nat} {pre : List SegG} {g0 : SegG}
    (habs0 : WalAbsD C Mr d lay ents) (hs0 : lay.segs = pre ++ [g0])
    (htail : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length)
    (hZ : TailZeros lay) (hnd0 : (lay.segs.map (·.ino)).Nodup)
    (hzf : ∀ z, g0.om.zf = some z → g0.bs.length ≤ z)
    (hok : CrashOk C Mr d lay cl n) :
    CrashOk C Mr { d with m := d.H.length } (syncLay lay pre g0) cl n := by
  have habs := walAbsD_sync habs0 hs0 htail
  have hB := tailBound_sync habs0 hs0 htail
  intro m' fo hr hf hnmd hw
  have hs : (syncLay lay pre g0).segs = pre ++ [syncTail g0] := rfl
  have hgm : syncTail g0 ∈ (syncLay lay pre g0).segs := by rw [hs]; simp
  have hg : (syncLay lay pre g0).segs.getLast? = some (syncTail g0) := by rw [hs]; simp
  have hg0 : lay.segs.getLast? = some g0 := by rw [hs0]; simp
  have hino : (syncTail g0).ino = g0.ino := rfl
  have hinos : (syncLay lay pre g0).segs.map (·.ino) = lay.segs.map (·.ino) := by
    rw [hs, hs0]; simp [hino]
  have hnd : ((syncLay lay pre g0).segs.map (·.ino)).Nodup := by rw [hinos]; exact hnd0
  have hpre : ∀ g' ∈ pre, g'.ino ≠ g0.ino := by
    intro g' hg' he
    rw [hs0, List.map_append, List.nodup_append] at hnd0
    exact hnd0.2.2 _ (List.mem_map_of_mem hg') _ (by simp) he
  let fo0 : Ino → Option Fs.OsFile := fun i =>
    if i = g0.ino then (fo i).map (fun f => syncImg g0.bs f.size) else fo i
  have hfo : ∀ i, i ≠ g0.ino → fo0 i = fo i := fun i hi => by simp [fo0, hi]
  have hfo0g : fo0 g0.ino = (fo g0.ino).map (fun f => syncImg g0.bs f.size) := by simp [fo0]
  have hlen0 : (syncTail g0).bs.length = g0.bs.length := by simp [syncTail]
  -- the old tail's crash, imaged as of the last sync
  have hfc0 : FileCrashedR g0.om [(0, DFrac.own (1 : Qp).half, g0.bs)] (fo0 g0.ino) := by
    rw [hfo0g]
    intro f' hf'
    obtain ⟨f, hf1, rfl⟩ := Option.map_eq_some_iff.1 hf'
    obtain ⟨-, hlo, hhi, -, -⟩ := hf (syncTail g0) hgm f hf1
    obtain ⟨-, -, hmlo, hmhi⟩ := habs.metas (syncTail g0) hgm
    obtain ⟨-, -, hmlo0, hmhi0⟩ := habs0.metas g0 (List.mem_of_getLast? hg0)
    rw [hlen0] at hmlo hmhi
    have hsz : f.size = g0.bs.length := by omega
    have hsz' : (syncImg g0.bs f.size).size = g0.bs.length := hsz
    refine ⟨⟨_, rfl⟩, by omega, by omega, ?_, ?_⟩
    · intro r hr k hk hks
      rw [List.mem_singleton] at hr; subst hr
      simp only [Nat.zero_add] at hks ⊢
      rw [syncImg_cache g0.bs f.size k (show k < f.size from hks)]
      obtain ⟨-, -, -, -, hbytes, -⟩ := habs0.last g0 hg0
      have hb := hbytes k (g0.bs[k]'hk) (List.getElem?_eq_getElem hk)
      have e : g0.bs.getD k (0, []) = g0.bs[k]'hk := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
      rw [e]
      exact .inl (valAt_mem0 hb.head0)
    · intro z hz b hzb hb
      have := hzf z hz; omega
  have hf0 : ∀ g' ∈ lay.segs, FileCrashedR g'.om [(0, DFrac.own (1 : Qp).half, g'.bs)]
      (fo0 g'.ino) := by
    intro g' hg'
    rw [hs0, List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hg' | rfl
    · rw [hfo _ (hpre g' hg')]; exact hf g' (by rw [hs]; simp [hg'])
    · exact hfc0
  have hn0 : ∀ g' ∈ lay.segs, g'.ino ∈ walInos (entsOf m' lay.j) → (fo0 g'.ino).isSome := by
    intro g' hg' hnd'
    rw [hs0, List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hg' | rfl
    · rw [hfo _ (hpre g' hg')]; exact hnmd g' (by rw [hs]; simp [hg']) hnd'
    · rw [hfo0g, Option.isSome_map]; exact hnmd (syncTail g') (by rw [hs]; simp) hnd'
  have hw0 : W1G C (walInos (entsOf m' lay.j)) (fun i => imgOf (fo0 i)) (segBytesOf lay) := by
    apply w1G_sync
    intro i bs hbs b hb
    obtain ⟨g', hg', rfl, rfl⟩ := segBytesOf_some hbs
    have hg'' := hg'
    rw [hs0, List.mem_append, List.mem_singleton] at hg''
    rcases hg'' with hgp | rfl
    · rw [hfo _ (hpre g' hgp)] at hb ⊢
      obtain ⟨k, hk⟩ := List.getElem?_of_mem hgp
      have hk' : lay.segs[k]? = some g' := by
        rw [hs0, List.getElem?_append_left ((List.getElem?_eq_some_iff.1 hk).1)]; exact hk
      have hkl : k + 1 < lay.segs.length := by
        have := (List.getElem?_eq_some_iff.1 hk).1; rw [hs0]; simp; omega
      have hint := habs0.intact k g' hkl hk'
      have hdur : ∀ y ∈ g'.bs, y = durB y.1 := by
        rw [hint]; intro y hy; obtain ⟨x, -, rfl⟩ := List.mem_map.1 hy; rfl
      cases hfg : fo g'.ino with
      | none => simp [imgOf, hfg] at hb
      | some f' =>
        have hm := habs0.metas g' hg'
        have hfc := hf g' (by rw [hs]; simp [hgp])
        rw [hfg] at hfc
        have hc := img_durable hfc hdur hm.2.2.1 hm.2.2.2
        simp only [imgOf, hfg, Option.map_some, Option.getD_some, hc] at hb ⊢
        simp only [List.length_map] at hb
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hb,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb]
        simp only [Option.map_some, Option.getD_some]
        rw [hdur _ (List.getElem_mem hb)]
        exact (valAt_durB _).symm
    · rw [hfo0g] at hb ⊢
      cases hfg : fo g'.ino with
      | none => simp [imgOf, hfg] at hb
      | some f' =>
        simp only [imgOf, hfg, Option.map_some, Option.getD_some, syncImg_length] at hb ⊢
        exact syncImg_getD _ _ _ hb
  have h0 := hok m' fo0 hr hf0 hn0 hw0
  have h' : CrashTo C Mr d (syncLay lay pre g0) m' fo0 :=
    crashTo_congr_lay (lay := lay) (lay' := syncLay lay pre g0) rfl rfl rfl rfl rfl hinos h0
  exact crashTo_tailM hC habs hZ hB hnd hg d.m habs0.lastSynced h' hfo (hf _ hgm) (hnmd _ hgm) hw

end pure

end WalFs
end EtcdGrove
end Perennial

end
