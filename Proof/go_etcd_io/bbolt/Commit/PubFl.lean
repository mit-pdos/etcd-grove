/-
`Commit`'s publish facts at the `commitFreelist` join (U10l of `notes/bbolt-proof-plan.md`):
`cmPubPre` of the records after `commitFreelist` (the spilled records with the root page in the
meta copy, `allocate`'s page added and the freelist page written into it, `tx.meta.freelist` its
id), from spill's post, `allocRes` and the writer sides' facts. The new synced freelist page is a
buffer that reloads the freelist after the allocation (`Commit/FlPageIds.flCurOK_flPgB`).

As at the `NoFreelistSync` join, two premises are not in spill's post (reported): the new tree's
slots not pending (`hnp`) and `markCov` of the spilled records (`hmc`, decision D-K).
-/
module

public import Proof.go_etcd_io.bbolt.Commit.PubPre
public import Proof.go_etcd_io.bbolt.Commit.PubFlBuf
public import Proof.go_etcd_io.bbolt.Commit.FlPageIds

@[expose] public section

noncomputable section

set_option maxRecDepth 20000

namespace Perennial
namespace EtcdGrove
namespace bbolt


open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- The freelist's ids (distinct, below the mark) are at most the mark. -/
theorem allIds_le_hwm (w : WDb) (hok : wdbOK w) (hwf : w.fl.WF) :
    w.fl.allIds.length ≤ w.C.hwm := by
  have c11 := hok.2.2.2.2.2.2.2.2.2.2.1
  have c12 := hok.2.2.2.2.2.2.2.2.2.2.2.1
  have hlt : ∀ x ∈ w.fl.allIds, x.toNat < w.C.hwm := by
    intro x hx
    rcases List.mem_append.1 hx with h | h
    · exact c12 x h
    · exact c11 _ (Or.inr (List.mem_map.2 ⟨x, h, rfl⟩))
  have hnd' : (w.fl.allIds.map BitVec.toNat).Nodup :=
    List.Pairwise.map BitVec.toNat (fun a b hab h => hab (BitVec.eq_of_toNat_eq h)) hwf.1
  have hsub : w.fl.allIds.map BitVec.toNat ⊆ List.range w.C.hwm := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact List.mem_range.2 (hlt x hx)
  have := (List.subperm_of_subset hnd' hsub).length_le
  simp only [List.length_map, List.length_range] at this
  exact this

/-- A free id is not pending (the ids are distinct). -/
theorem free_not_pend (fl : FLPg) (hwf : fl.WF) : ∀ x ∈ fl.free, x.toNat ∉ pendSlots fl := by
  intro x hx hp
  obtain ⟨y, hy, hyx⟩ := List.mem_map.1 hp
  have : y = x := BitVec.eq_of_toNat_eq hyx
  subst this
  exact (List.nodup_append.1 hwf.1).2.2 _ hx _ hy rfl

/-- `allocate` changes the meta copy's mark only. -/
theorem allocRes_mv (X X4 : WX) (fl2 fl4 : FLPg) (txid : w64) (cnt : Nat) (p : Loc) (id : w64)
    (hal : allocRes X X4 fl2 fl4 txid cnt p id) :
    X4.t.mv = { X.t.mv with pgid' := X4.t.mv.pgid' } := by
  obtain ⟨-, -, Xr, hr, hc⟩ := hal
  have hXr : Xr.t.mv = X.t.mv := by
    rcases hr with rfl | ⟨Xd, b, hd, rfl⟩
    · rfl
    · exact hd.2.2.2.2.2.2.1
  rcases hc with ⟨-, -, e⟩ | ⟨-, -, -, e⟩ <;>
  · subst e
    unfold WX.addPage
    dsimp only
    rw [hXr]

theorem pf_W64_toNat (s : Nat) (h : s < 2 ^ 64) : (W64 (s : Int)).toNat = s := by
  simp only [W64, BitVec.toNat_ofInt]; omega

/-- **`cmPubPre` at the `commitFreelist` join** (see the file header). -/
theorem cmPubPre_commitFl (D : Data) (X1 X2 X3 X4 : WX) (w2 w4 : WDb) (fl1 : FLPg) (txid0 : w64)
    (p4 : Loc) (id4 : w64)
    (hsp : spillOK X1 X2 w2.C fl1 w2.fl txid0) (hD : D = wtxData X1)
    (hbufs : spillBufs X2 w2.C w2.fl)
    (hX3pm : X3.t.pm = X2.t.pm) (hX3bf : X3.t.bufs = X2.t.bufs)
    (hX3pg : X3.t.mv.pgid' = X2.t.mv.pgid')
    (hroot3 : X3.t.mv.root'.root'.toNat = X2.rootPage) (htxid3 : X3.t.mv.txid' = X2.t.mv.txid')
    (hmg : X3.t.mv.magic'.toNat = boltMagic) (hvr : X3.t.mv.version'.toNat = boltVersion)
    (hps : X3.t.mv.pageSize'.toNat = 4096)
    (hal : allocRes X3 X4 w2.fl w4.fl w2.wtxid (flCount w2.fl) p4 id4) (hC4 : w4.C = w2.C)
    (htxC : X3.t.mv.txid'.toNat = w2.C.txid + 1)
    (hCh : w2.C.hwm ≤ X2.t.mv.pgid'.toNat)
    (hml : X4.t.mv.pgid'.toNat * 4096 ≤ 0xFFFFFFFFFFFF)
    (hh48 : w2.C.hwm * 4096 ≤ 0xFFFFFFFFFFFF)
    (htC : treeOK w2.C) (hok2 : wdbOK w2) (hwf2 : w2.fl.WF) (hok4 : wdbOK w4)
    (hwf4 : w4.fl.WF) (hfb4 : flBelow w4.fl w4.C (some (w4.C.txid + 1)))
    (htx2 : w2.C.txid + 2 < 2 ^ 64)
    (hnp : ∀ s ∈ treeSlots (spillC X2 w2.C.pages), s ∉ pendSlots w2.fl)
    (hmc : markCov X2 w2.C.hwm)
    (hal4 : ∀ x a, w4.fl.allocs !! x = some a → a.toNat ≤ w4.C.txid + 1) :
    cmPubPre D (X4.setFlPage id4 (flPageBytes w4.fl id4 (flCount w2.fl))) w4 := by
  -- the run's facts
  have hft2 : ∀ x ∈ w2.fl.free, x.toNat ∉ treeSlots w2.C := hok2.2.2.2.2.1
  have hfp2 := free_not_pend w2.fl hwf2
  have hf2 : ∀ x ∈ w2.fl.free, 2 ≤ x.toNat := fun x hx => hwf2.2.1 x (List.mem_append_left _ hx)
  have hpgE : X3.t.mv.pgid'.toNat = X2.t.mv.pgid'.toNat := by rw [hX3pg]
  have hr2C : 2 ≤ w2.C.hwm := by
    obtain ⟨⟨hwf, -⟩, -⟩ := htC
    cases hwf with
    | page _ _ h2 hlt _ _ _ _ => omega
  have hlt3 : ∀ s, s ∈ treeSlots w2.C ∨ s ∈ pendSlots w2.fl → s < X3.t.mv.pgid'.toNat := by
    intro s hs; have := hok2.2.2.2.2.2.2.2.2.2.2.1 s hs; omega
  have hflt3 : ∀ x ∈ w2.fl.free, x.toNat < X3.t.mv.pgid'.toNat := by
    intro x hx; have := hok2.2.2.2.2.2.2.2.2.2.2.2.1 x hx; omega
  have hb3 : spillBufs X3 w2.C w2.fl := by
    unfold spillBufs at *; rw [hX3pm, hX3bf, hX3pg]; exact hbufs
  obtain ⟨hfsub, hpd, hle, hc, hr2, hrend, hrs⟩ :=
    allocRes_run X3 X4 w2.C w2.fl w4.fl _ (flCount w2.fl) p4 id4 hb3 hal hft2 hfp2 hf2 hlt3 hflt3
      (by omega)
  have hpendE : pendSlots w4.fl = pendSlots w2.fl := by
    unfold pendSlots FLPg.pendingIds; rw [hpd]
  have hpidsE : w4.fl.pendingIds = w2.fl.pendingIds := by
    unfold FLPg.pendingIds; rw [hpd]
  -- the page count's bounds
  have hn2 := allIds_le_hwm w2 hok2 hwf2
  have hcnt32 : flCount w2.fl - 1 < 2 ^ 32 := by
    unfold flCount; split <;> omega
  have hlen4 : w4.fl.allIds.length ≤ w2.fl.allIds.length := by
    obtain ⟨-, -, -, hcase⟩ := allocRes_shape X3 X4 w2.fl w4.fl _ (flCount w2.fl) p4 id4 [] hal
    rcases hcase with ⟨hfl, -⟩ | ⟨-, hfl, -⟩
    · rw [hfl]; exact alloc_allIds_le _ _ _ _
    · rw [hfl]; exact Nat.le_refl _
  have hroom := flCount_room w2.fl.allIds.length w4.fl.allIds.length hlen4
  have hov := flPgB_overflow w4.fl id4 (flCount w2.fl) hcnt32
  have hlen := flPgB_length w4.fl id4 (flCount w2.fl) hroom
  have hb5 := spillBufs_setFlPage X3 X4 w2.C w2.fl w4.fl _ (flCount w2.fl) p4 id4
    (flPgB w4.fl id4 (flCount w2.fl)) hb3 hal hft2 hfp2 hf2 hlt3 hflt3 (by omega) hov hlen
    (flPgB_id _ _ _)
  obtain ⟨-, hlk, -, hcase⟩ := allocRes_shape X3 X4 w2.fl w4.fl _ (flCount w2.fl) p4 id4
    (flPgB w4.fl id4 (flCount w2.fl)) hal
  -- `X2`'s buffers stay, the freelist page's id is none of them
  have hX2none : X2.t.bufs !! id4 = none := by
    cases h : X2.t.bufs !! id4 with
    | none => rfl
    | some pg =>
      exfalso
      have := (hrs 0 hc).2.2.2 id4 pg (by rw [hX3bf]; exact h) 0 (by omega)
      exact this rfl
  have hbuf : ∀ id pg, X2.t.bufs !! id = some pg →
      (X4.setFlPage id4 (flPgB w4.fl id4 (flCount w2.fl))).t.bufs !! id = some pg := by
    intro id pg h
    rw [hlk]
    by_cases e : id4 = id
    · subst e; rw [hX2none] at h; cases h
    · rw [if_neg e, hX3bf]; exact h
  -- the meta copy
  have hmv4 := allocRes_mv X3 X4 w2.fl w4.fl _ _ p4 id4 hal
  have hroot5 : (X4.setFlPage id4 (flPgB w4.fl id4 (flCount w2.fl))).t.mv.root'.root'.toNat =
      X2.rootPage := by
    show X4.t.mv.root'.root'.toNat = _; rw [hmv4]; exact hroot3
  have htxid5 : (X4.setFlPage id4 (flPgB w4.fl id4 (flCount w2.fl))).t.mv.txid' =
      X2.t.mv.txid' := by
    show X4.t.mv.txid' = _; rw [hmv4]; exact htxid3
  have htxC5 : (X4.setFlPage id4 (flPgB w4.fl id4 (flCount w2.fl))).t.mv.txid'.toNat =
      w4.C.txid + 1 := by
    show X4.t.mv.txid'.toNat = _; rw [hmv4, hC4]; exact htxC
  have hpg5 : (X4.setFlPage id4 (flPgB w4.fl id4 (flCount w2.fl))).t.mv.pgid' = X4.t.mv.pgid' :=
    rfl
  have hfl5 : (X4.setFlPage id4 (flPgB w4.fl id4 (flCount w2.fl))).t.mv.freelist' = id4 := rfl
  have hid62 : id4.toNat < 2 ^ 62 := by omega
  have hroot2 := spillC_root_lt X2 w2.C.pages hsp.1
  -- the new tree's facts
  have hspill4 : spillOK X1 X2 w4.C fl1 w2.fl txid0 := by rw [hC4]; exact hsp
  have hpg : cmPubPg D (X4.setFlPage id4 (flPgB w4.fl id4 (flCount w2.fl))) w4
      (spillC X2 w4.C.pages).pages := by
    refine cmPubPg_of_spill D X1 X2 _ w4 fl1 w2.fl txid0 hspill4 hD
      (fun s h => by rw [hpendE]; exact h) hbuf hroot5 (by rw [hpg5]; omega) (by rw [hC4]; exact hCh)
      htxid5 htxC5 (by rw [hpg5]; omega) hok4 hfb4 (by rw [hC4]; exact htx2)
      (by rw [hC4, hpendE]; exact hnp) (fun f hf => ?_) (fun s h1 h2 => ?_)
    · -- the synced freelist page: the buffer at `id4`, `flCurOK`
      rw [pubC_flpg] at hf
      unfold metaFlpg at hf
      rw [hfl5] at hf
      rw [if_neg (by unfold pgidNoFreelist; omega)] at hf
      cases hf
      refine ⟨flPgB w4.fl id4 (flCount w2.fl), ?_, ?_⟩
      · rw [hlk, show W64 ((id4.toNat : Nat) : Int) = id4 by simp [W64], if_pos rfl]
      · have hcovC : ∀ s, coversSlot (spillC X2 w4.C.pages).pages s →
            s ∈ treeSlots w2.C ∨ ∃ id pg j, X2.t.bufs !! id = some pg ∧ j < 1 + pageOverflow pg ∧
              id.toNat + j = s := by
          intro s hcs
          obtain ⟨id, pg, hp, a, b⟩ := hcs
          have hext := hspill4.1.2.2.2.1 id pg hp
          have hlt : id < 2 ^ 64 := by
            have : (spillC X2 w4.C.pages).hwm = X2.t.mv.pgid'.toNat := rfl
            have := X2.t.mv.pgid'.isLt
            omega
          rcases hspill4.2.2.2.2.2.2 id pg hp with h | h
          · left
            rw [← hC4]
            exact (mem_pagesSlots_iff _ _).2 ⟨id, pg, h, a, b⟩
          · right
            refine ⟨_, pg, s - id, h, ?_, ?_⟩ <;> (try rw [pf_W64_toNat id hlt]) <;> omega
        have hflpgE : (pubC w4.C (X4.setFlPage id4 (flPgB w4.fl id4 (flCount w2.fl))).t.mv
            (spillC X2 w4.C.pages).pages).flpg = some id4.toNat := by
          rw [pubC_flpg]; unfold metaFlpg; rw [hfl5, if_neg (by unfold pgidNoFreelist; omega)]
        have hhwm5 : (pubC w4.C (X4.setFlPage id4 (flPgB w4.fl id4 (flCount w2.fl))).t.mv
            (spillC X2 w4.C.pages).pages).hwm = X4.t.mv.pgid'.toNat := by
          rw [pubC_hwm, hpg5]
        refine flCurOK_flPgB w4.fl (pubC w4.C (X4.setFlPage id4 (flPgB w4.fl id4 (flCount w2.fl))).t.mv
            (spillC X2 w4.C.pages).pages) id4 (flCount w2.fl) hflpgE hr2 hc
          (by rw [hhwm5]; exact hrend) (by rw [hhwm5]; have := X4.t.mv.pgid'.isLt; omega)
          hcnt32 hroom hwf4
          (fun s a b => ⟨fun hcs => ?_, fun x hx => ?_⟩) (fun t pd hp => ?_) (fun x hx => ?_)
          (fun a ha => by
            rw [pubC_txid]
            show a.toNat ≤ (X4.setFlPage id4 _).t.mv.txid'.toNat
            rw [htxC5]; exact hal4 id4 a ha)
        · obtain ⟨c1, -, -, c4⟩ := hrs (s - id4.toNat) (by omega)
          rw [show id4.toNat + (s - id4.toNat) = s by omega] at c1 c4
          rcases hcovC s hcs with h | ⟨id, pg, j, h, hj, he⟩
          · exact c1 h
          · exact c4 id pg (by rw [hX3bf]; exact h) j hj he
        · obtain ⟨-, c2, c3, -⟩ := hrs (s - id4.toNat) (by omega)
          rw [show id4.toNat + (s - id4.toNat) = s by omega] at c2 c3
          rcases List.mem_append.1 hx with h | h
          · exact c3 x h
          · intro e
            apply c2
            rw [← e, ← hpendE]
            exact List.mem_map.2 ⟨x, h, rfl⟩
        · rw [pubC_txid]
          show t.toNat ≤ (X4.setFlPage id4 _).t.mv.txid'.toNat
          rw [htxC5]
          rcases hfb4.2.2.1 t pd hp with h | ⟨h, -⟩
          · omega
          · simp only [Option.some.injEq] at h; omega
        · refine ⟨?_, hfb4.2.2.2.2.1 x hx, fun hcs => ?_⟩
          · rw [pubC_hwm]
            have := hfb4.1 x hx
            rw [hC4] at this
            show x.toNat < (X4.setFlPage id4 _).t.mv.pgid'.toNat
            rw [hpg5]; omega
          · rcases hcovC _ hcs with h | ⟨id, pg, j, h, hj, he⟩
            · exact hok4.2.2.2.2.1 x hx (by rw [hC4]; exact h)
            · exact ((hbufs.2 id pg h).2.2.2.2 j hj).2.2.1 x (hfsub x hx) he.symm
    · -- `markCov`: the spilled records' and the run's at the mark
      rw [hC4] at h1
      by_cases hs : s < X2.t.mv.pgid'.toNat
      · obtain ⟨id, pg, h, a, b⟩ := (mem_bufSlots _ s).1 (hmc s h1 hs)
        exact (mem_bufSlots _ s).2 ⟨id, pg, hbuf id pg h, a, b⟩
      · rw [hpg5] at h2
        rcases hcase with ⟨-, e, -⟩ | ⟨hid, -, -, e⟩
        · rw [e] at h2; omega
        · refine (mem_bufSlots _ s).2 ⟨id4, flPgB w4.fl id4 (flCount w2.fl), (by rw [hlk, if_pos rfl]),
            (by rw [hid]; omega), (by rw [hov]; rw [hid] at e ⊢; omega)⟩
  show cmPubPre D (X4.setFlPage id4 (flPgB w4.fl id4 (flCount w2.fl))) w4
  refine cmPubPre_of D _ w4 _ (by rw [hC4]; exact hb5) (by rw [hC4]; exact htC)
    (by rw [hroot5, hpg5]; omega) (Or.inl (by rw [hfl5, hpg5]; omega))
    (by show X4.t.mv.magic'.toNat = _; rw [hmv4]; exact hmg)
    (by show X4.t.mv.version'.toNat = _; rw [hmv4]; exact hvr)
    (by show X4.t.mv.pageSize'.toNat = _; rw [hmv4]; exact hps) hpg

end pure

end bbolt
end EtcdGrove
end Perennial
