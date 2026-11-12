/-
`Commit`'s publish facts at the freelist's joins (U10l of `notes/bbolt-proof-plan.md`): `cmPubPg`
and `cmPubPre` from `spill`'s post (`spillOK`, `spillBufs`), the meta copy and the writer side's
facts, for the records `Xt` the join holds (the spilled records `X2` with the root page and the
freelist page set in the meta copy, and possibly the freelist page's buffer added). The new tree's
pages are the spilled tree's, `(spillC X2 C.pages).pages`.

One premise is not a consequence of `spill`'s post as stated (reported, U10l): the new tree's
slots are not pending (`hnp`; `cpOK`'s clause): a base page the new tree keeps is not pending for
the writer's txid (the spill frees only the pages of the nodes it rewrites).
-/
module

public import Proof.go_etcd_io.bbolt.Commit.TailPub
public import Proof.go_etcd_io.bbolt.Commit.TreeHwm
public import Spec.go_etcd_io.bbolt.Bucket__spill

@[expose] public section

noncomputable section

set_option maxRecDepth 20000

namespace Perennial
namespace EtcdGrove
namespace bbolt


open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

theorem pp_mem_pendSlots (fl : FLPg) (s : Nat) :
    s ∈ pendSlots fl ↔ ∃ t pd x, fl.pending !! t = some pd ∧ x ∈ pd.ids ∧ x.toNat = s := by
  simp only [pendSlots, FLPg.pendingIds, List.mem_map, List.mem_flatMap]
  constructor
  · rintro ⟨x, ⟨⟨t, pd⟩, hkv, hx⟩, rfl⟩
    exact ⟨t, pd, x, (GMap.mem_toList _ _ _).1 hkv, hx, rfl⟩
  · rintro ⟨t, pd, x, hp, hx, rfl⟩
    exact ⟨x, ⟨(t, pd), (GMap.mem_toList _ _ _).2 hp, hx⟩, rfl⟩

theorem pp_W64_toNat (s : Nat) (h : s < 2 ^ 64) : (W64 (s : Int)).toNat = s := by
  simp only [W64, BitVec.toNat_ofInt]; omega

theorem pp_mem_pagesSlots (P : Pages) (s : Nat) :
    s ∈ pagesSlots P ↔ ∃ id pg, P !! id = some pg ∧ id ≤ s ∧ s < id + (1 + pageOverflow pg) := by
  simp only [pagesSlots, List.mem_flatMap, List.mem_range']
  constructor
  · rintro ⟨⟨id, pg⟩, hip, j, hj, rfl⟩
    exact ⟨id, pg, (GMap.mem_toList _ _ _).1 hip, by omega, by simp only at hj; omega⟩
  · rintro ⟨id, pg, hp, h1, h2⟩
    exact ⟨(id, pg), (GMap.mem_toList _ _ _).2 hp, s - id, by simp only; omega, by omega⟩

/-- **`cmPubPg` from the spill** (see the file header), for the writer side `w` at the join and
the records `Xt`. -/
theorem cmPubPg_of_spill (D : Data) (X1 X2 Xt : WX) (w : WDb) (fl1 fl2 : FLPg) (txid : w64)
    (hsp : spillOK X1 X2 w.C fl1 fl2 txid) (hD : D = wtxData X1)
    (hpend : ∀ s, s ∈ pendSlots fl2 → s ∈ pendSlots w.fl)
    (hbuf : ∀ id pg, X2.t.bufs !! id = some pg → Xt.t.bufs !! id = some pg)
    (hroot : Xt.t.mv.root'.root'.toNat = X2.rootPage)
    (hhwm : X2.t.mv.pgid'.toNat ≤ Xt.t.mv.pgid'.toNat)
    (hCh : w.C.hwm ≤ X2.t.mv.pgid'.toNat)
    (htxid : Xt.t.mv.txid' = X2.t.mv.txid')
    (htxC : Xt.t.mv.txid'.toNat = w.C.txid + 1)
    (h62 : Xt.t.mv.pgid'.toNat ≤ 2 ^ 62)
    (hok : wdbOK w) (hfb : flBelow w.fl w.C (some (w.C.txid + 1)))
    (htx2 : w.C.txid + 2 < 2 ^ 64)
    (hnp : ∀ s ∈ treeSlots (spillC X2 w.C.pages), s ∉ pendSlots w.fl)
    (hflpg : ∀ f, (pubC w.C Xt.t.mv (spillC X2 w.C.pages).pages).flpg = some f → ∃ pg,
      Xt.t.bufs !! W64 (f : Int) = some pg ∧
      flCurOK w.fl (pubC w.C Xt.t.mv (spillC X2 w.C.pages).pages) pg)
    (hmc : markCov Xt w.C.hwm) :
    cmPubPg D Xt w (spillC X2 w.C.pages).pages := by
  obtain ⟨htree, hdata, -, -, hdrop, -, hpages⟩ := hsp
  have ep : (pubC w.C Xt.t.mv (spillC X2 w.C.pages).pages).pages =
      (spillC X2 w.C.pages).pages := rfl
  have er : (pubC w.C Xt.t.mv (spillC X2 w.C.pages).pages).root =
      (spillC X2 w.C.pages).root := by
    rw [pubC_root]; exact hroot
  have eh : (pubC w.C Xt.t.mv (spillC X2 w.C.pages).pages).hwm = Xt.t.mv.pgid'.toNat :=
    pubC_hwm _ _ _
  have et : (pubC w.C Xt.t.mv (spillC X2 w.C.pages).pages).txid = Xt.t.mv.txid'.toNat :=
    pubC_txid _ _ _
  have eslots : treeSlots (pubC w.C Xt.t.mv (spillC X2 w.C.pages).pages) =
      treeSlots (spillC X2 w.C.pages) := rfl
  have hc11 := hok.2.2.2.2.2.2.2.2.2.2.1
  have hc12 := hok.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hf1, hf2, hf3, -, hf5, hf6⟩ := hfb
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hflpg, hmc⟩
  · rw [treeData_congr ep er, hdata, hD]
  · refine treeOK_mono htree ep er ?_ ?_
    · rw [eh]; exact hhwm
    · rw [et, htxid]; rfl
  · rw [eh]; exact h62
  · intro s hs hn
    rw [eslots] at hn
    exact hpend s (hdrop s hs hn)
  · rw [eslots]; exact hnp
  · refine ⟨fun x hx => ?_, fun t pd x hp hx _ => ?_, fun t pd hp => ?_, ?_, hf5, hf6⟩
    · rw [eh]; have := hf1 x hx; omega
    · rw [eh]
      have := hc11 x.toNat (Or.inr ((pp_mem_pendSlots _ _).2 ⟨t, pd, x, hp, hx, rfl⟩))
      omega
    · left; rw [et, htxC]
      rcases hf3 t pd hp with h | ⟨h, -⟩
      · omega
      · simp only [Option.some.injEq] at h; omega
    · rw [et, htxC]; omega
  · intro id pg hp
    rcases hpages id pg hp with h | h
    · exact Or.inl h
    · exact Or.inr (hbuf _ _ h)
  · intro s hs
    rw [eslots] at hs
    obtain ⟨id, pg, hp, h1, h2⟩ := (pp_mem_pagesSlots _ _).1 hs
    have hext := htree.2.2.2.1 id pg hp
    have hlt : id < 2 ^ 64 := by
      have := Xt.t.mv.pgid'.isLt
      have : (spillC X2 w.C.pages).hwm = X2.t.mv.pgid'.toNat := rfl
      have := X2.t.mv.pgid'.isLt
      omega
    rcases hpages id pg hp with h | h
    · left
      rw [mem_slotsOf]
      left
      exact (pp_mem_pagesSlots _ _).2 ⟨id, pg, h, h1, h2⟩
    · right
      refine (mem_bufSlots _ s).2 ⟨_, pg, hbuf _ _ h, ?_, ?_⟩ <;>
        rw [pp_W64_toNat id hlt] <;> omega

theorem pp_metaSummed_pageSize (mv : Meta) : (metaSummed mv).pageSize' = mv.pageSize' := by
  unfold metaSummed; rfl

/-- **`cmPubPre` from the buffers' facts** (`spillBufs` of the records at the join), the root page
below the mark, the freelist page's id, the meta copy's constants and the new tree's `cmPubPg`. -/
theorem cmPubPre_of (D : Data) (Xt : WX) (w : WDb) (Pg : Pages)
    (hb : spillBufs Xt w.C w.fl) (htC : treeOK w.C)
    (hroot : Xt.t.mv.root'.root'.toNat < Xt.t.mv.pgid'.toNat)
    (hfl : Xt.t.mv.freelist'.toNat < Xt.t.mv.pgid'.toNat ∨
      Xt.t.mv.freelist'.toNat = pgidNoFreelist)
    (hmg : Xt.t.mv.magic'.toNat = boltMagic) (hvr : Xt.t.mv.version'.toNat = boltVersion)
    (hps : Xt.t.mv.pageSize'.toNat = 4096) (hpg : cmPubPg D Xt w Pg) :
    cmPubPre D Xt w := by
  obtain ⟨hpm, hbs⟩ := hb
  have hr2 : 2 ≤ w.C.hwm := by
    obtain ⟨⟨hwf, -⟩, -⟩ := htC
    cases hwf with
    | page _ _ h2 hlt _ _ _ _ => omega
  refine ⟨hpm, fun id pg h => ?_, ?_, fun s hs => ?_, ?_, ?_, hr2,
    metaValid_metaSummed _ hmg hvr, by rw [pp_metaSummed_pageSize]; exact hps, Pg, hpg⟩
  · obtain ⟨h1, h2, h3, h4, -⟩ := hbs id pg h
    exact ⟨h1, h2, h3, h4⟩
  · exact bufSlots_nodup_of_disj _ fun id pg h j hj id' pg' h' j' hj' he =>
      ((hbs id pg h).2.2.2.2 j hj).2.2.2 id' pg' h' j' hj' he
  · obtain ⟨id, pg, h, h1, h2⟩ := (mem_bufSlots _ s).1 hs
    have hj : s - id.toNat < 1 + pageOverflow pg := by omega
    obtain ⟨-, -, -, h4, hs'⟩ := hbs id pg h
    obtain ⟨c1, c2, c3, -⟩ := hs' (s - id.toNat) hj
    have e : id.toNat + (s - id.toNat) = s := by omega
    rw [e] at c1 c2 c3
    refine ⟨c1, c2, fun hm => c3 _ hm ?_⟩
    have := Xt.t.mv.pgid'.isLt
    exact pp_W64_toNat s (by omega)
  · simp only [uint.Z]; omega
  · rcases hfl with h | h
    · left; simp only [uint.Z]; omega
    · right; exact h

/-- `spill`'s tree's root page lies below its mark (`treeOK`). -/
theorem spillC_root_lt (X2 : WX) (base : Pages) (h : treeOK (spillC X2 base)) :
    X2.rootPage < X2.t.mv.pgid'.toNat := by
  obtain ⟨⟨hwf, -⟩, -⟩ := h
  cases hwf with
  | page _ _ h2 hlt _ _ _ _ => exact hlt

/-- **`cmPubPre` at the `NoFreelistSync` join** (`Tx__Commit_err`): the records `Xt` the spilled
`X2` with the root page and `PgidNoFreelist` in the meta copy. `hnp` and `hmc` are not in
`spill`'s post (reported). -/
theorem cmPubPre_noSync (D : Data) (X1 X2 Xt : WX) (w2 : WDb) (fl1 : FLPg) (txid : w64)
    (hsp : spillOK X1 X2 w2.C fl1 w2.fl txid) (hD : D = wtxData X1)
    (hbufs : spillBufs X2 w2.C w2.fl)
    (hpm : Xt.t.pm = X2.t.pm) (hbf : Xt.t.bufs = X2.t.bufs) (hpg : Xt.t.mv.pgid' = X2.t.mv.pgid')
    (hroot : Xt.t.mv.root'.root'.toNat = X2.rootPage) (htxid : Xt.t.mv.txid' = X2.t.mv.txid')
    (htxC : Xt.t.mv.txid'.toNat = w2.C.txid + 1)
    (hfl : Xt.t.mv.freelist'.toNat = pgidNoFreelist)
    (hmg : Xt.t.mv.magic'.toNat = boltMagic) (hvr : Xt.t.mv.version'.toNat = boltVersion)
    (hps : Xt.t.mv.pageSize'.toNat = 4096) (hCh : w2.C.hwm ≤ X2.t.mv.pgid'.toNat)
    (hml : Xt.t.mv.pgid'.toNat * 4096 ≤ 0xFFFFFFFFFFFF) (htC : treeOK w2.C) (hok : wdbOK w2)
    (hfb : flBelow w2.fl w2.C (some (w2.C.txid + 1))) (htx2 : w2.C.txid + 2 < 2 ^ 64)
    (hnp : ∀ s ∈ treeSlots (spillC X2 w2.C.pages), s ∉ pendSlots w2.fl)
    (hmc : markCov X2 w2.C.hwm) :
    cmPubPre D Xt w2 := by
  have hb : spillBufs Xt w2.C w2.fl := by
    unfold spillBufs at *; rw [hpm, hbf, hpg]; exact hbufs
  have hr2 := spillC_root_lt X2 w2.C.pages hsp.1
  apply cmPubPre_of D Xt w2 _ hb htC (by rw [hroot, hpg]; exact hr2) (Or.inr hfl) hmg hvr hps
  refine cmPubPg_of_spill D X1 X2 Xt w2 fl1 w2.fl txid hsp hD (fun s h => h)
    (fun id pg h => by rw [hbf]; exact h) hroot (by rw [hpg]; exact Nat.le_refl _) hCh htxid htxC
    (by omega) hok hfb htx2 hnp (fun f hf => ?_) (by unfold markCov at *; rw [hbf, hpg]; exact hmc)
  rw [pubC_flpg] at hf
  unfold metaFlpg at hf
  rw [if_pos hfl] at hf
  cases hf

end pure

end bbolt
end EtcdGrove
end Perennial
