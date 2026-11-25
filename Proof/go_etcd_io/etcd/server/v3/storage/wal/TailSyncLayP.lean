/- Lean-first (no Rocq counterpart).

# The fdatasync of a lent tail `ZeroToEnd` left partway (unit `synclent`; W4c U5 log, fifth session, "E6"; pure)

`ReadAll`'s `ZeroToEnd` may fail after its first step (`walLentRes_pendStop`) with the tail in any state
(`TailMetaE`: nothing changed, a truncate to `wr` announced that did not land, or one that landed and a
growth that did not): its bytes past `wr` are a torn frame's, zero only on the length word at `wr`. Its
layout has F-Z or `TailPend` (`walLentRes_lookup`); with F-Z the fdatasync is `syncLay_any`'s; with
`TailPend` and no F-Z, no `WinZero` holds, and the synced layout keeps the synced values past `wr` as
its `old` (`syncLayP`): the tail exact, every byte durable, `TailPend` again (the length word at `wr`).

* `syncLayP`, `walAbsD_syncP`, `tailPend_syncP`, `tailBound_syncP`: the static relation, `TailPend` and the
  record boundary after it;
* `crashOk_syncP`: the crash condition at the raised mark (`crashOkA_tailPend`'s proof: the old
  condition at the old mark, then `crashTo_tailP` over `walAbsD_syncP` with the input mark `d.m`);
* `walsOk_syncP`, `dirKeysOk_syncP`: the invariant's pure conjuncts after it;
* `syncLay_anyE`: the synced layout, F-Z or `TailPend`, either case.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.TailSyncWin
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.TailCrashRep

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

section syncp
variable [GooseExts]

/-- **The layout after the fdatasync of a tail with a torn frame past `wr`** (see the file header):
`syncLay`, and `old` the synced values from `wr` on; below it `old`'s bytes, zero past `old`'s end. -/
def syncLayP (lay : WalLay) (pre : List SegG) (g : SegG) : WalLay :=
  { syncLay lay pre g with
    old := (lay.old ++ List.replicate lay.wr 0).take lay.wr ++ (g.bs.drop lay.wr).map Prod.fst }

theorem syncLayP_unpurge (pg : List SegG) (lay : WalLay) (pre : List SegG) (g : SegG) :
    syncLayP (unpurge pg lay) (pg ++ pre) g = unpurge pg (syncLayP lay pre g) := by
  simp [syncLayP, syncLay, unpurge, List.append_assoc]

@[simp] theorem syncLayP_pg (lay : WalLay) (pre : List SegG) (g : SegG) :
    (syncLayP lay pre g).pg = lay.pg := rfl

theorem syncOldP_length (old : List w8) (wr : Nat) (bs : List ByteG) :
    ((old ++ List.replicate wr 0).take wr ++ (bs.drop wr).map Prod.fst).length =
      wr + (bs.length - wr) := by
  simp

theorem syncOldP_getD_lt (old : List w8) (wr : Nat) (t : List w8) (b : Nat) (hb : b < wr) :
    ((old ++ List.replicate wr 0).take wr ++ t).getD b 0 = old.getD b 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by simp; omega), List.getElem?_take, if_pos hb]
  by_cases hbo : b < old.length
  · rw [List.getElem?_append_left hbo]
  · rw [List.getElem?_append_right (by omega), List.getElem?_replicate, if_pos (by omega),
      List.getElem?_eq_none (show old.length ≤ b by omega)]
    rfl

theorem syncOldP_getD_ge (old : List w8) (wr : Nat) (bs : List ByteG) (b : Nat) (hb : wr ≤ b) :
    ((old ++ List.replicate wr 0).take wr ++ (bs.drop wr).map Prod.fst).getD b 0 =
      (bs.getD b (0, [])).1 := by
  have hl : ((old ++ List.replicate wr 0).take wr).length = wr := by simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hl, List.getElem?_map,
    List.getElem?_drop, show wr + (b - wr) = b by omega, List.getD_eq_getElem?_getD]
  cases bs[b]? <;> rfl

/-- **The fdatasync of a tail with a torn frame past `wr` keeps the static relation** (the history
synced, every record flushed), the layout `syncLayP`, given `TailPend` and the handle's zero length word
at `wr`. -/
theorem walAbsD_syncP {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    {pre : List SegG} {g0 : SegG} (h : WalAbsD C Mr d lay ents) (hs : lay.segs = pre ++ [g0])
    (htail : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length) (hP : TailPend lay)
    (hpv : PendStop C Mr (g0.bs.map (·.1)) lay.wr
      (WalEnc.chainEnd C 0#32 (recsOfSegs C Mr d.metadata (segsOf (histM d) lay.cuts)))) :
    WalAbsD C Mr { d with m := d.H.length } (syncLayP lay pre g0) ents := by
  have hc : ∀ b ∈ lay.cuts, b ≤ d.H.length := fun b hb => by
    have := walCutPos_le (h.cuts.1 b hb); simpa [histM] using this
  have hmapI : (syncLayP lay pre g0).segs.map (·.ino) = lay.segs.map (·.ino) := by
    simp [syncLayP, syncLay, hs, syncTail]
  have hmapN : (syncLayP lay pre g0).segs.map (·.name) = lay.segs.map (·.name) := by
    simp [syncLayP, syncLay, hs, syncTail]
  have hlen : (syncLayP lay pre g0).segs.length = lay.segs.length := by simp [syncLayP, syncLay, hs]
  have hg0 : lay.segs.getLast? = some g0 := by rw [hs]; simp
  have hlast' : (syncLayP lay pre g0).segs.getLast? = some (syncTail g0) := by
    simp [syncLayP, syncLay]
  have hget : ∀ k, (syncLayP lay pre g0).segs[k]? =
      (lay.segs[k]?).map (fun g => if k = pre.length then syncTail g else g) :=
    syncLay_getElem? hs
  have hSm : ∀ k, segStream C Mr { d with m := d.H.length } lay.cuts k =
      segStream C Mr d lay.cuts k := fun _ => rfl
  obtain ⟨h1, h2, h3, h4, -, h6, h7, h8, -⟩ := h.lastWin g0 hg0
  refine { names := ?_, cuts := ?_, nameBound := ?_, cut := h.cut, metas := ?_, intact := ?_,
           last := ?_, synced := ?_, lastSynced := ?_, fit := h.fit, tailStop := ?_,
           nonempty := ?_, cutPos := h.cutPos, seqName := fun k g hk => by
             rw [hget] at hk
             obtain ⟨g1, hg1, rfl⟩ := Option.map_eq_some_iff.1 hk
             obtain ⟨ix, hn⟩ := h.seqName k g1 hg1
             refine ⟨ix, ?_⟩
             show _ = walFileName (lay.first + k) ix
             split <;> simp [syncTail, hn] }
  · rw [hmapI, hmapN]; exact h.names
  · exact ⟨h.cuts.1, h.cuts.2.1, by rw [hlen]; exact h.cuts.2.2⟩
  · intro k g hk
    rw [hget] at hk
    obtain ⟨g1, hg1, rfl⟩ := Option.map_eq_some_iff.1 hk
    obtain ⟨sq, ix, hn, hb⟩ := h.nameBound k g1 hg1
    refine ⟨sq, ix, ?_, hb⟩
    split <;> simp [syncTail, hn]
  · intro g hg
    simp only [syncLayP, syncLay, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · obtain ⟨k1, k2, k3, k4, k5⟩ := h.metas g (by rw [hs]; simp [hg])
      refine ⟨k1, k2, k3, k4, Or.inr ?_⟩
      rcases k5 with k5 | k5
      · obtain rfl := Option.some.inj (hg0.symm.trans k5)
        exfalso
        have hn := h.names.2
        rw [hs, List.map_append, List.pairwise_append] at hn
        exact go.goStringLt_irrefl _ (hn.2.2 _ (List.mem_map_of_mem hg) _ (by simp))
      · exact k5
    · have := h.metas g0 (by rw [hs]; simp)
      refine ⟨?_, ?_, ?_, ?_, Or.inl hlast'⟩ <;>
        simp [syncTail, OsMeta.synced, this.1, this.2.1]
  · intro k g hk hg
    rw [hget] at hg
    obtain ⟨g1, hg1, rfl⟩ := Option.map_eq_some_iff.1 hg
    have hk' : k + 1 < lay.segs.length := hlen ▸ hk
    have hkp : k ≠ pre.length := by rw [hs] at hk'; simp at hk'; omega
    simp only [if_neg hkp]
    exact h.intact k g1 hk' hg1
  · intro g hg
    rw [hlast'] at hg; cases hg
    have hxs : SegExact (syncTail g0) := by
      simp [SegExact, syncTail, OsMeta.synced, (h.metas g0 (by rw [hs]; simp)).1]
    refine ⟨fun _ => ?_, fun hx' => absurd hxs hx'⟩
    unfold TailLast
    simp only [syncLayP, syncLay, hSm] at h1 h2 h3 h4 h6 h7 h8 ⊢
    refine ⟨Nat.le_refl _, h2, ?_, by rw [syncOldP_length]; omega, fun b x hb => ?_, h6,
      ?_, fun hz b hb1 hb2 => ?_⟩
    · rw [syncOldP_length]; simp [syncTail]; omega
    · simp only [syncTail, List.getElem?_map] at hb
      cases hb0 : g0.bs[b]? with
      | none => rw [hb0] at hb; cases hb
      | some y =>
        rw [hb0] at hb; simp only [Option.map_some, Option.some.injEq] at hb; subst hb
        by_cases hbw : b < lay.wr
        · rw [syncOldP_getD_lt _ _ _ _ hbw]
          rcases h.low g0 hg0 b y hb0 hbw with ⟨-, hB⟩ | ⟨-, -, hW⟩
          · exact byteOk_sync hB (fun _ => decide_eq_true hbw)
          · simp [ByteOk, hbw, hW.1]
        · rw [syncOldP_getD_ge _ _ _ _ (by omega),
            show g0.bs.getD b (0, []) = y by rw [List.getD_eq_getElem?_getD, hb0]; rfl]
          exact byteOk_durB (decide_eq_false hbw) (decide_eq_false hbw)
    · rw [List.take_append_of_le_length (by simp; omega), List.take_take,
        Nat.min_eq_left h6, List.take_append_of_le_length h3]
      exact h7
    · exfalso; have := hP.1; omega
  · refine ⟨Nat.le_refl _, ?_⟩
    simp only [syncLayP, syncLay, List.take_length]
    rw [htail]; exact Nat.le_refl _
  · exact segStart_le hc _
  · intro _
    simp only [syncLayP, syncLay, hSm]
    rw [← hP.1]
    refine pendStop_congr ?_ (by simp <;> omega) (by simp <;> omega) hpv
    rw [List.drop_append_of_le_length (by simp), List.drop_eq_nil_of_le (by simp), List.nil_append,
      List.map_drop]
  · simp [syncLayP, syncLay]


/-- `syncLayP` keeps the inodes. -/
theorem syncLayP_inos (lay : WalLay) (pre : List SegG) (g0 : SegG) (hs : lay.segs = pre ++ [g0]) :
    (syncLayP lay pre g0).segs.map (·.ino) = lay.segs.map (·.ino) :=
  syncLay_inos lay pre g0 hs

/-- **`TailPend` after the fdatasync** (`RepOld`: the synced tail exact, its values `old`'s from `wr` on). -/
theorem tailPend_syncP {lay : WalLay} {pre : List SegG} {g0 : SegG} (hP : TailPend lay)
    (hsz : g0.om.size = g0.bs.length) :
    TailPend (syncLayP lay pre g0) := by
  refine ⟨hP.1, fun g hg b hb1 hb2 => ?_⟩
  simp only [syncLayP, syncLay, List.getLast?_append, List.getLast?_singleton, Option.some_or,
    Option.some.injEq] at hg
  subst hg
  have hX : segBytesX (syncTail g0) = (syncTail g0).bs :=
    segBytesX_of_hi (by simp [syncTail, OsMeta.synced, hsz])
  rw [hX] at hb2 ⊢
  simp only [syncTail, List.length_map] at hb2
  have hb1' : lay.wr ≤ b := hb1
  refine ⟨by simp only [syncLayP, syncLay, syncOldP_length]; omega, ?_⟩
  simp only [syncLayP, syncLay, syncTail]
  rw [syncOldP_getD_ge _ _ _ _ hb1', List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hb2, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb2]
  simp only [Option.map_some, Option.getD_some]
  exact valAt_durB _

/-- **The record boundary after the fdatasync** (`tailBound_sync`: it does not read `old`). -/
theorem tailBound_syncP {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    {pre : List SegG} {g0 : SegG} (habs : WalAbsD C Mr d lay ents) (hs : lay.segs = pre ++ [g0])
    (htail : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length) :
    TailBound C Mr { d with m := d.H.length } (syncLayP lay pre g0) :=
  by have := tailBound_sync (pre := pre) habs hs htail; exact this

/-- **The crash condition after the fdatasync** (see the file header). -/
theorem crashOk_syncP {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {ents : Ents} {cl : List Claim} {n : Nat} {pre : List SegG} {g0 : SegG}
    (habs0 : WalAbsD C Mr d lay ents) (hs0 : lay.segs = pre ++ [g0])
    (htail : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length) (hP0 : TailPend lay)
    (hpv : PendStop C Mr (g0.bs.map (·.1)) lay.wr
      (WalEnc.chainEnd C 0#32 (recsOfSegs C Mr d.metadata (segsOf (histM d) lay.cuts))))
    (hnd0 : (lay.segs.map (·.ino)).Nodup)
    (hzf0 : ∀ z, g0.om.zf = some z → g0.bs.length ≤ z)
    (hok : CrashOk C Mr d lay cl n) :
    CrashOk C Mr { d with m := d.H.length } (syncLayP lay pre g0) cl n := by
  have habs := walAbsD_syncP habs0 hs0 htail hP0 hpv
  have hP := tailPend_syncP (pre := pre) hP0 (habs0.metas g0 (by rw [hs0]; simp)).1
  have hS : (segStream C Mr { d with m := d.H.length } (syncLayP lay pre g0).cuts
      (syncLayP lay pre g0).cuts.length).length = (syncLayP lay pre g0).wr := htail.symm
  intro m' fo hr hf hnmd hw
  have hs : (syncLayP lay pre g0).segs = pre ++ [syncTail g0] := rfl
  have hgm : syncTail g0 ∈ (syncLayP lay pre g0).segs := by rw [hs]; simp
  have hg : (syncLayP lay pre g0).segs.getLast? = some (syncTail g0) := by rw [hs]; simp
  have hg0 : lay.segs.getLast? = some g0 := by rw [hs0]; simp
  have hino : (syncTail g0).ino = g0.ino := rfl
  have hinos : (syncLayP lay pre g0).segs.map (·.ino) = lay.segs.map (·.ino) := by
    rw [hs, hs0]; simp [hino]
  have hnd : ((syncLayP lay pre g0).segs.map (·.ino)).Nodup := by rw [hinos]; exact hnd0
  have hpre : ∀ g' ∈ pre, g'.ino ≠ g0.ino := by
    intro g' hg' he
    rw [hs0, List.map_append, List.nodup_append] at hnd0
    exact hnd0.2.2 _ (List.mem_map_of_mem hg') _ (by simp) he
  have hpreX : ∀ g' ∈ pre, SegExact g' := by
    intro g' hg'
    obtain ⟨-, -, -, -, h5⟩ := habs0.metas g' (by rw [hs0]; simp [hg'])
    rcases h5 with h5 | h5
    · rw [hg0] at h5; cases h5; exact absurd rfl (hpre _ hg')
    · exact h5
  let fo0 : Ino → Option Fs.OsFile := fun i =>
    if i = g0.ino then (fo i).map (fun _ => syncImg g0.bs g0.bs.length) else fo i
  have hfo : ∀ i, i ≠ g0.ino → fo0 i = fo i := fun i hi => by simp [fo0, hi]
  have hfo0g : fo0 g0.ino = (fo g0.ino).map (fun _ => syncImg g0.bs g0.bs.length) := by simp [fo0]
  have hfc0 : FileCrashedR g0.om [(0, DFrac.own (1 : Qp).half, g0.bs)] (fo0 g0.ino) := by
    rw [hfo0g]
    refine fileCrashedR_syncImg habs0 hg0 hzf0 (fun f hf' => ?_)
    obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 hf'
    rfl
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
    · rw [hfo0g, Option.isSome_map]; exact hnmd (syncTail g') hgm hnd'
  have hw0 : W1G C (walInos (entsOf m' lay.j)) (fun i => imgOf (fo0 i)) (segBytesOf lay)
      (segRzOf lay) := by
    apply w1G_sync
    intro i bs hbs b hb
    obtain ⟨g', hg', rfl, rfl⟩ := segBytesOf_some hbs
    have hg'' := hg'
    rw [hs0, List.mem_append, List.mem_singleton] at hg''
    rcases hg'' with hgp | rfl
    · have hX := hpreX g' hgp
      rw [segBytesX_of_hi (Nat.le_of_eq hX.2)]
      rw [hfo _ (hpre g' hgp)] at hb ⊢
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
        have hfc := hf g' (by rw [hs]; simp [hgp])
        rw [hfg] at hfc
        have hc := img_durable hfc hdur hX.1 hX.2
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
        rw [syncImg_getD _ _ _ hb, segBytesX_getD_lt hb]
  have h0 := hok m' fo0 hr hf0 hn0 hw0
  have h' : CrashTo C Mr d (syncLayP lay pre g0) m' fo0 :=
    crashTo_congr_lay (lay := lay) (lay' := syncLayP lay pre g0) rfl rfl rfl rfl rfl hinos h0
  have h'' : CrashTo C Mr { { d with m := d.H.length } with m := d.m } (syncLayP lay pre g0) m' fo0 := by
    cases d; exact h'
  have hsz := (habs.metas (syncTail g0) hgm).1
  have hzf : ∀ z, (syncTail g0).om.zf = some z →
      max (syncLayP lay pre g0).so (syncLayP lay pre g0).z0 ≤ z := by
    intro z hz
    simp only [syncTail, OsMeta.synced, Option.some.injEq] at hz
    have h1 : g0.om.size ≤ g0.om.syncZ := by
      unfold OsMeta.syncZ; have := le_pageEnd g0.om.size; split <;> omega
    have h2 := (habs0.metas g0 (List.mem_of_getLast? hg0)).1
    obtain ⟨-, -, -, h4, -⟩ := habs0.lastWin g0 hg0
    have h5 := hP0.1
    simp only [syncLayP, syncLay]
    omega
  have hsz0 : g0.om.size = g0.bs.length := (habs0.metas g0 (by rw [hs0]; simp)).1
  have hX : segBytesX (syncTail g0) = (syncTail g0).bs :=
    segBytesX_of_hi (by simp [syncTail, OsMeta.synced, hsz0])
  have hTL := (habs.last (syncTail g0) hg).1
    (by simp [SegExact, syncTail, OsMeta.synced, hsz0])
  obtain ⟨-, -, -, -, hBy, -⟩ := hTL
  refine crashTo_tailR hC habs hnd hg hP hS d.m habs0.lastSynced h'' hfo (fun f hf1 => ?_) (hnmd _ hgm) hw
  obtain ⟨h1, h2, h3⟩ := crashImg_tail (by rw [← hf1]; exact hf _ hgm) hsz (habs.winLo_any _ hg)
    hzf (habs.hiX hg)
  have hmx : max (syncLayP lay pre g0).so (syncLayP lay pre g0).z0 = (syncLayP lay pre g0).wr := by
    have := hP.1; simp only [syncLayP, syncLay] at this ⊢; omega
  -- a candidate of the synced tail's byte `b` is its value
  have hval : ∀ b, b < f.size → ∀ s, (f.cache b, s) ∈ ((segBytesX (syncTail g0)).getD b (0, [])).2 →
      ∃ hb : b < g0.bs.length, f.cache b = (g0.bs[b]'hb).1 := by
    intro b hb s hs'
    have hbl : b < g0.bs.length := by
      have := h2; rw [hX] at this; simp [syncTail] at this; omega
    refine ⟨hbl, ?_⟩
    rw [hX, List.getD_eq_getElem?_getD] at hs'
    simp only [syncTail, List.getElem?_map, List.getElem?_eq_getElem hbl, Option.map_some,
      Option.getD_some, List.mem_singleton, Prod.mk.injEq] at hs'
    exact hs'.1
  refine ⟨by rw [← hmx]; exact h1, h2, fun b hb => ?_, fun b hb hbs => ?_⟩
  · have hbf : b < f.size := by have := h1; rw [hmx] at this; omega
    rcases h3 b hbf with ⟨s, hs'⟩ | ⟨hb1, -⟩
    · obtain ⟨hbl, e⟩ := hval b hbf s hs'
      rw [e]
      have hB := hBy b (durB (g0.bs[b]'hbl).1) (by simp [syncTail, List.getElem?_map, List.getElem?_eq_getElem hbl])
      have hso : (syncLayP lay pre g0).so = lay.wr := rfl
      rw [decide_eq_true (show b < (syncLayP lay pre g0).so by rw [hso]; exact hb)] at hB
      have := congrArg Prod.fst hB
      simp only at this
      exact this
    · rw [hmx] at hb1; exact absurd hb1 (by omega)
  · rcases h3 b hbs with ⟨s, hs'⟩ | ⟨-, h0⟩
    · obtain ⟨hbl, e⟩ := hval b hbs s hs'
      left
      rw [e]
      simp only [syncLayP, syncLay]
      rw [syncOldP_getD_ge lay.old lay.wr g0.bs b hb, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbl]
      rfl
    · exact .inr h0

/-- **`WalsOk` after the fdatasync** (`walsOk_syncW`'s `TailPend` form). -/
theorem walsOk_syncP {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {R : Roots} {jr : Ino}
    {s : AbsDiskState} {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} {dir : GoString}
    {d : WalDur} {lay : WalLay} {pre : List SegG} {g0 : SegG}
    (hW : WalsOk C Mr R jr s Ls cl n) (hd : s.wal !! dir = some d) (hl : Ls !! dir = some lay)
    (hs : lay.segs = pre ++ [g0])
    (htail : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length) (hP : TailPend lay)
    (hpv : PendStop C Mr (g0.bs.map (·.1)) lay.wr
      (WalEnc.chainEnd C 0#32 (recsOfSegs C Mr d.metadata (segsOf (histM d) lay.cuts))))
    (hzf : ∀ z, g0.om.zf = some z → g0.bs.length ≤ z)
    (hok : CrashOk C Mr (walFullD d lay.pg lay) (unpurge lay.pg lay) cl n) :
    WalsOk C Mr R jr (walSyncS s dir d) (<[dir := syncLayP lay pre g0]> Ls) cl n := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hW
  have hsub : ∀ dir' lay', (<[dir := syncLayP lay pre g0]> Ls) !! dir' = some lay' →
      ∃ lay1, Ls !! dir' = some lay1 ∧
        ((lay'.pg ++ lay'.segs).map (·.ino)).Sublist ((lay1.pg ++ lay1.segs).map (·.ino)) := by
    intro dir' lay' h
    by_cases e : dir' = dir
    · subst e
      rw [GMap.lookup_insert] at h; cases h
      exact ⟨lay, hl, sub_pg rfl (by rw [syncLayP_inos lay pre g0 hs]; exact List.Sublist.refl _)⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at h
      exact ⟨lay', h, List.Sublist.refl _⟩
  refine ⟨fun dir' d' hd' => ?_, fun dir' hn => ?_, segsAll_nodup_sub h3 hsub, fun g' hg' => ?_,
    fun dir' nm hin hn => ?_, h6⟩
  · by_cases e : dir' = dir
    · subst e
      rw [walSyncS_lookup] at hd'; cases hd'
      obtain ⟨lay1, nm, hj, hl1, hA, hjr, hnm, hc, habs, hcr⟩ := h1 dir' d hd
      have e : lay1 = lay := by rw [hl] at hl1; exact (Option.some.inj hl1).symm
      rw [e] at hjr hnm hc habs hcr
      obtain ⟨⟨e0, hF⟩, -, hz⟩ := hcr
      have hzS : SegsZf (lay.pg ++ (syncLayP lay pre g0).segs.dropLast) := by
        have e : (syncLayP lay pre g0).segs.dropLast = lay.segs.dropLast := by simp [syncLayP, syncLay, hs]
        rw [e]; exact hz
      have hnd := ((segsAll_nodup_iff Ls).1 h3).1 dir' lay hl
      have hsF : (unpurge lay.pg lay).segs = (lay.pg ++ pre) ++ [g0] := by simp [hs]
      refine ⟨syncLayP lay pre g0, nm, hj, GMap.lookup_insert _ _ _, hA, hjr, hnm, hc,
        walAbsD_syncP habs hs htail hP hpv, ?_⟩
      have hPu : TailPend (unpurge lay.pg lay) := (repOld_unpurge _ habs.nonempty).2 hP
      unfold WalFullOk
      simp only [syncLayP_pg]
      rw [← syncLayP_unpurge]
      exact ⟨⟨e0, walAbsD_syncP (d := walFullD d lay.pg lay) hF hsF htail hPu hpv⟩,
        ⟨none, (fun _ h => nomatch h), (crashOkA_none_iff _ _ _ _ _ _).2
          (crashOk_syncP hC (d := walFullD d lay.pg lay) hF hsF htail hPu hpv hnd hzf hok)⟩, hzS⟩
    · rw [walSyncS_lookup_ne s dir d e] at hd'
      obtain ⟨lay1, nm, hj, hl1, rest⟩ := h1 dir' d' hd'
      exact ⟨lay1, nm, hj, by rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact hl1, rest⟩
  · have e : dir' ≠ dir := by rintro rfl; rw [walSyncS_lookup] at hn; cases hn
    rw [walSyncS_lookup_ne s dir d e] at hn
    rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact h2 dir' hn
  · obtain ⟨dir', lay', hl', hg''⟩ := segsAll_mem hg'
    by_cases e : dir' = dir
    · subst e
      rw [GMap.lookup_insert] at hl'; cases hl'
      simp only [syncLayP, syncLay, List.mem_append, List.mem_singleton] at hg''
      rcases hg'' with hg'' | hg'' | rfl
      · exact h4 g' (mem_segsAll_pg hl hg'')
      · exact h4 g' (mem_segsAll hl (by rw [hs]; exact List.mem_append_left _ hg''))
      · exact h4 g0 (mem_segsAll hl (by rw [hs]; simp))
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hl'
      exact h4 g' (mem_segsAll_all hl' hg'')
  · have e : dir' ≠ dir := by rintro rfl; rw [walSyncS_lookup] at hn; cases hn
    rw [walSyncS_lookup_ne s dir d e] at hn
    exact h5 dir' nm hin hn

/-- **The directory keys after the fdatasync**, no cut pending. -/
theorem dirKeysOk_syncP {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {R : Roots} {jr : Ino}
    {s : AbsDiskState} {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat}
    {K : GMap GoString (Ino × List GoString)} {dir : GoString}
    {d : WalDur} {lay : WalLay} {pre : List SegG} {g0 : SegG}
    (hW : WalsOk C Mr R jr s Ls cl n) (hd : s.wal !! dir = some d) (hl : Ls !! dir = some lay)
    (hs : lay.segs = pre ++ [g0])
    (htail : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length) (hP : TailPend lay)
    (hpv : PendStop C Mr (g0.bs.map (·.1)) lay.wr
      (WalEnc.chainEnd C 0#32 (recsOfSegs C Mr d.metadata (segsOf (histM d) lay.cuts))))
    (hzf : ∀ z, g0.om.zf = some z → g0.bs.length ≤ z)
    (h : DirKeysOk C Mr jr s Ls cl n K none) :
    DirKeysOk C Mr jr (walSyncS s dir d) (<[dir := syncLayP lay pre g0]> Ls) cl n K none := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun dir' j X hk => ?_, fun dir' d' lay' hd' hl' hc => ?_, h3.insert hl rfl⟩
  · obtain ⟨lay1, hj, hl1, rest⟩ := h1 dir' j X hk
    by_cases e : dir' = dir
    · subst e; rw [hl] at hl1; cases hl1
      exact ⟨syncLayP lay pre g0, hj, GMap.lookup_insert _ _ _, rest⟩
    · exact ⟨lay1, hj, by rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact hl1, rest⟩
  · by_cases e : dir' = dir
    · subst e
      rw [GMap.lookup_insert] at hl'; cases hl'
      rw [walSyncS_lookup] at hd'; cases hd'
      obtain ⟨lay1, nm1, hj1, hl1, -, -, -, -, habs, ⟨⟨e0, hF⟩, -⟩⟩ := hW.1 dir' d hd
      rw [hl] at hl1; cases hl1
      have hnd := ((segsAll_nodup_iff Ls).1 hW.2.2.1).1 dir' lay hl
      have hok := (crashOkA_none_iff _ _ _ _ _ _).1 (h2 dir' d lay hd hl (by simp))
      simp only [syncLayP_pg]
      rw [← syncLayP_unpurge]
      exact (crashOkA_none_iff _ _ _ _ _ _).2
        (crashOk_syncP hC (d := walFullD d lay.pg lay) hF (by simp [hs]) htail
          ((repOld_unpurge _ habs.nonempty).2 hP) hpv hnd hzf hok)
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hl'
      rw [walSyncS_lookup_ne s dir d e] at hd'
      exact h2 dir' d' lay' hd' hl' hc

/-- **The layout after the fdatasync of a lent tail, F-Z or `TailPend`** (see the file header): its
segments `pre` then the synced tail, the directory, cuts and write position kept, F-Z or `TailPend`, the
record boundary, `WalsOk` and the directory keys at the synced state. -/
theorem syncLay_anyE {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {R : Roots} {jr : Ino}
    {s : AbsDiskState} {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat}
    {K : GMap GoString (Ino × List GoString)} {dir : GoString}
    {d : WalDur} {lay : WalLay} {ents : Ents} {pre : List SegG} {g0 : SegG}
    (hW : WalsOk C Mr R jr s Ls cl n) (hd : s.wal !! dir = some d) (hl : Ls !! dir = some lay)
    (hs : lay.segs = pre ++ [g0])
    (htail : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length)
    (hZ : TailZeros lay ∨ TailPend lay)
    (hpv : PendStop C Mr (g0.bs.map (·.1)) lay.wr
      (WalEnc.chainEnd C 0#32 (recsOfSegs C Mr d.metadata (segsOf (histM d) lay.cuts))))
    (hzf : ∀ z, g0.om.zf = some z → g0.bs.length ≤ z) (hK : DirKeysOk C Mr jr s Ls cl n K none)
    (habs : WalAbsD C Mr d lay ents) :
    ∃ L : WalLay, L.segs = pre ++ [syncTail g0] ∧ L.j = lay.j ∧ L.nm = lay.nm ∧
      L.cuts = lay.cuts ∧ L.wr = lay.wr ∧ L.pg = lay.pg ∧ (TailZeros L ∨ TailPend L) ∧
      TailBound C Mr { d with m := d.H.length } L ∧
      WalsOk C Mr R jr (walSyncS s dir d) (<[dir := L]> Ls) cl n ∧
      DirKeysOk C Mr jr (walSyncS s dir d) (<[dir := L]> Ls) cl n K none := by
  by_cases hz : TailZeros lay
  · obtain ⟨L, h1, h2, h3, h4, h5, h5', h6, h7, h8, h9⟩ := syncLay_any hC hW hd hl hs htail hz hzf hK habs
    exact ⟨L, h1, h2, h3, h4, h5, h5', Or.inl h6, h7, h8, h9⟩
  · have hP : TailPend lay := hZ.resolve_left hz
    exact ⟨syncLayP lay pre g0, rfl, rfl, rfl, rfl, rfl, rfl,
      Or.inr (tailPend_syncP hP (habs.metas g0 (by rw [hs]; simp)).1),
      tailBound_syncP habs hs htail,
      walsOk_syncP hC hW hd hl hs htail hP hpv hzf
        ((crashOkA_none_iff _ _ _ _ _ _).1 (hK.2.1 dir d lay hd hl (by simp))),
      dirKeysOk_syncP hC hW hd hl hs htail hP hpv hzf hK⟩

end syncp

end WalFs
end EtcdGrove
end Perennial

end
