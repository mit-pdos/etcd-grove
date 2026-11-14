/- Lean-first (no Rocq counterpart).

# The crash condition across a resize window on the tail (I3b, `wal-tc6`; pure)

`cut` truncates the tail at its write position `wr`; the window stays open until its fdatasync
(`TailMetaW`). While the truncate is in flight (`rzMeta`, `rsAnn`) and after it landed (`rsPostK
true`, its cut-off bytes' candidates known past the size), the layout's last segment `g` knows each
byte from `wr` on as the exact tail's `g0` did, or with the truncate's zero (stamped `n > 0`, one of
`g.om.rz`) appended (`RzCands`), over `segBytesX g` (its bytes, then those its `OsMeta` knows past
them). A crash then leaves an image of the tail no longer than `g0`'s bytes whose bytes are `g0`'s
candidates: below `wr` the bytes are unchanged; from `wr` on a byte is one of `g0`'s candidates or a
zero, and zero is one of them there (`TailLast`'s `ByteOk` with the byte neither synced nor written
gives `(old b, 0)` first; `old b = 0` by F-Z, `z0 ≤ wr`).

* `crashOkA_win`: `CrashOkA` of the exact layout `lay0` gives `CrashOkA` of the window layout `lay`
  (the `crashOkA_tail` pattern: the old condition at images as of the last sync, then
  `crashTo_tailL` on `lay0` with `W1G.drop_rz`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailCrash
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.RzW1

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc go_etcd_io.raft.v3

section win
variable [GooseExts]

/-- A segment of distinct inodes is the one `segRzOf` finds. -/
theorem segRzOf_of_mem {lay : WalLay} {g : SegG} (hnd : (lay.segs.map (·.ino)).Nodup)
    (hg : g ∈ lay.segs) : segRzOf lay g.ino = g.om.rz := by
  unfold segRzOf
  cases hf : lay.segs.find? (fun g' => decide (g'.ino = g.ino)) with
  | none =>
    exfalso
    have := List.find?_eq_none.1 hf g hg
    simp at this
  | some g' =>
    have hg' := List.mem_of_find?_eq_some hf
    have hi : g'.ino = g.ino := by simpa using List.find?_some hf
    have : g' = g := Fs.eq_of_nodup_map hnd hg' hg hi
    subst this; rfl

/-- Zero is a candidate, stamped 0, of each byte of the exact tail from the write position on. -/
theorem tail_zero_cand {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {g : SegG}
    (hT : TailLast C Mr d lay g) (hZ : TailZeros lay) {b : Nat} (hwb : lay.wr ≤ b)
    (hb : b < g.bs.length) : ∃ s, ((0 : w8), s) ∈ (g.bs.getD b (0, [])).2 := by
  obtain ⟨hso, -, hlen, -, hbytes, hz0, -, -⟩ := hT
  have hx := hbytes b (g.bs[b]'hb) (List.getElem?_eq_getElem hb)
  have hs' : decide (b < lay.so) = false := by simp; omega
  rw [hs'] at hx
  unfold ByteOk at hx
  simp only [Bool.false_eq_true, ↓reduceIte] at hx
  obtain ⟨ex, he, -⟩ := hx
  refine ⟨0, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb, Option.getD_some, he,
    hZ b (by omega) (by omega)]
  exact List.mem_cons_self ..

/-- **The crash condition across a resize window on the tail** (see the file header): the layout
`lay0` with the exact tail `g0` and `lay` with the window's tail `g` (same inode) differ only in the
tail's ghost; `g` is at least `wr` long, its `OsMeta` bounds a crash's size to `[wr, |g0.bs|]`, and
`segBytesX g` covers `g0`'s bytes: unchanged below `wr`, each with the known resizes' zeros
(`RzCands`); no alternative layout holds the tail. -/
theorem crashOkA_win {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {d : WalDur}
    {lay0 lay : WalLay} {ents0 : Ents} {alt : Option WalLay} {cl : List Claim} {n : Nat}
    {pre : List SegG} {g0 g : SegG}
    (habs0 : WalAbsD C Mr d lay0 ents0) (hZ : TailZeros lay0) (hB : TailBound C Mr d lay0)
    (hnd : (lay0.segs.map (·.ino)).Nodup)
    (hs0 : lay0.segs = pre ++ [g0]) (hs : lay.segs = pre ++ [g]) (hino : g.ino = g0.ino)
    (hjr : lay.jr = lay0.jr) (hnm : lay.nm = lay0.nm) (hj : lay.j = lay0.j)
    (hcuts : lay.cuts = lay0.cuts) (hfirst : lay.first = lay0.first)
    (hex0 : SegExact g0) (hzf : ∀ z, g0.om.zf = some z → g0.bs.length ≤ z)
    (hsz : g.om.size = g.bs.length) (hwrg : lay0.wr ≤ g.bs.length) (hwr : lay0.wr ≤ g.om.lo)
    (hhi : g.om.hi ≤ g0.bs.length) (hlenX : g0.bs.length ≤ (segBytesX g).length)
    (hlow : ∀ b, b < lay0.wr → ((segBytesX g).getD b (0, [])).2 = (g0.bs.getD b (0, [])).2)
    (hrz : ∀ b, b < g0.bs.length →
      RzCands g.om.rz (g0.bs.getD b (0, [])).2 ((segBytesX g).getD b (0, [])).2)
    (halt : ∀ la, alt = some la → ∀ g' ∈ la.segs, g'.ino ≠ g.ino)
    (hok : CrashOkA C Mr d lay0 alt cl n) : CrashOkA C Mr d lay alt cl n := by
  intro m' fo hr hf hnmd hw
  have hgm : g ∈ lay.segs := by rw [hs]; simp
  have hg0 : lay0.segs.getLast? = some g0 := by rw [hs0]; simp
  have hg0m : g0 ∈ lay0.segs := List.mem_of_getLast? hg0
  have hTE0 : TailExact lay0 := fun g1 hg1 => by rw [hg0] at hg1; cases hg1; exact hex0
  have hexall : ∀ g1 ∈ lay0.segs, g1.om.hi ≤ g1.bs.length := fun g1 hg1 =>
    Nat.le_of_eq (habs0.metasEx hTE0 g1 hg1).2.2.2
  have hT0 : TailLast C Mr d lay0 g0 := (habs0.last g0 hg0).1 hex0
  have hpre : ∀ g' ∈ pre, g'.ino ≠ g.ino := by
    intro g' hg' he
    have hnd' := hnd
    rw [hs0, List.map_append, List.nodup_append] at hnd'
    exact hnd'.2.2 _ (List.mem_map_of_mem hg') _ (by simp) (he.trans hino)
  have hinos : lay.segs.map (·.ino) = lay0.segs.map (·.ino) := by
    rw [hs, hs0]; simp [hino]
  have hndl : (lay.segs.map (·.ino)).Nodup := by rw [hinos]; exact hnd
  let fo0 : Ino → Option Fs.OsFile := fun i =>
    if i = g.ino then (fo i).map (fun _ => syncImg g0.bs g0.bs.length) else fo i
  have hfo : ∀ i, i ≠ g.ino → fo0 i = fo i := fun i hi => by simp [fo0, hi]
  have hfo0g : fo0 g.ino = (fo g.ino).map (fun _ => syncImg g0.bs g0.bs.length) := by simp [fo0]
  -- the old tail's crash, imaged as of the last sync
  have hfc0 : FileCrashedR g0.om [(0, DFrac.own (1 : Qp).half, g0.bs)] (fo0 g0.ino) := by
    rw [← hino, hfo0g]
    intro f' hf'
    obtain ⟨f, -, rfl⟩ := Option.map_eq_some_iff.1 hf'
    have hmlo0 := hex0.1
    have hmhi0 := hex0.2
    have hsz0 := (habs0.metas g0 hg0m).1
    have hsz' : (syncImg g0.bs g0.bs.length).size = g0.bs.length := rfl
    refine ⟨⟨_, rfl⟩, by omega, by omega, ?_, ?_, fun b c hb _ hb2 => absurd hb2 (by omega)⟩
    · intro r hr k hk hks
      rw [List.mem_singleton] at hr; subst hr
      simp only [Nat.zero_add] at hks ⊢
      rw [syncImg_cache g0.bs g0.bs.length k (show k < g0.bs.length by omega)]
      obtain ⟨-, -, -, -, hbytes, -⟩ := hT0
      have hb := hbytes k (g0.bs[k]'hk) (List.getElem?_eq_getElem hk)
      have e : g0.bs.getD k (0, []) = g0.bs[k]'hk := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
      rw [e]
      exact .inl (valAt_mem0 hb.head0)
    · intro z hz b hzb hb
      have := hzf z hz; omega
  have hf0 : ∀ g' ∈ lay0.segs, FileCrashedR g'.om [(0, DFrac.own (1 : Qp).half, g'.bs)]
      (fo0 g'.ino) := by
    intro g' hg'
    rw [hs0, List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hg' | rfl
    · rw [hfo _ (hpre g' hg')]; exact hf g' (by rw [hs]; simp [hg'])
    · exact hfc0
  have hn0 : ∀ g' ∈ lay0.segs, g'.ino ∈ walInos (entsOf m' lay0.j) → (fo0 g'.ino).isSome := by
    intro g' hg' hnd'
    rw [hs0, List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hg' | rfl
    · rw [hfo _ (hpre g' hg')]; exact hnmd g' (by rw [hs]; simp [hg']) (by rw [hj]; exact hnd')
    · rw [← hino, hfo0g, Option.isSome_map]; exact hnmd g hgm (by rw [hino, hj]; exact hnd')
  have hw0 : W1G C (walInos (entsOf m' lay0.j)) (fun i => imgOf (fo0 i)) (segBytesOf lay0)
      (segRzOf lay0) := by
    apply w1G_sync
    intro i bs hbs b hb
    obtain ⟨g', hg', rfl, rfl⟩ := segBytesOf_some_ex hexall hbs
    have hg'' := hg'
    rw [hs0, List.mem_append, List.mem_singleton] at hg''
    rcases hg'' with hgp | rfl
    · -- an intact segment: durable, its image its bytes
      rw [hfo _ (hpre g' hgp)] at hb ⊢
      obtain ⟨k, hk⟩ := List.getElem?_of_mem hgp
      have hk' : lay0.segs[k]? = some g' := by
        rw [hs0, List.getElem?_append_left ((List.getElem?_eq_some_iff.1 hk).1)]; exact hk
      have hkl : k + 1 < lay0.segs.length := by
        have := (List.getElem?_eq_some_iff.1 hk).1; rw [hs0]; simp; omega
      have hint := habs0.intact k g' hkl hk'
      have hdur : ∀ y ∈ g'.bs, y = durB y.1 := by
        rw [hint]; intro y hy; obtain ⟨x, -, rfl⟩ := List.mem_map.1 hy; rfl
      cases hfg : fo g'.ino with
      | none => simp [imgOf, hfg] at hb
      | some f' =>
        have hm := habs0.metasEx hTE0 g' hg'
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
    · -- the tail: as of the last sync
      rw [← hino, hfo0g] at hb ⊢
      cases hfg : fo g.ino with
      | none => simp [imgOf, hfg] at hb
      | some f' =>
        simp only [imgOf, hfg, Option.map_some, Option.getD_some, syncImg_length] at hb ⊢
        exact syncImg_getD _ _ _ hb
  -- the window's image of the tail: no longer than `g0`'s bytes, each byte one of their candidates
  have himg0 : ∀ f, fo g0.ino = some f → max lay0.so lay0.z0 ≤ f.size ∧ f.size ≤ g0.bs.length ∧
      ∀ b, b < f.size → ∃ s, (f.cache b, s) ∈ (g0.bs.getD b (0, [])).2 := by
    intro f hfg
    rw [← hino] at hfg
    obtain ⟨-, hlo, hhi', hrun, hzfc, htc⟩ := hf g hgm f hfg
    obtain ⟨hso, -, -, -, -, hz0, -, -⟩ := hT0
    refine ⟨by omega, by omega, fun b hb => ?_⟩
    have hcase : (∃ s, (f.cache b, s) ∈ ((segBytesX g).getD b (0, [])).2) ∨
        (lay0.wr ≤ b ∧ f.cache b = 0) := by
      by_cases hbg : b < g.bs.length
      · have := hrun (0, DFrac.own (1 : Qp).half, g.bs) (List.mem_singleton_self _) b hbg
          (by simp only [Nat.zero_add]; exact hb)
        simp only [Nat.zero_add] at this
        rcases this with ⟨s, hs'⟩ | ⟨h1, h2⟩
        · left; refine ⟨s, ?_⟩
          rw [segBytesX_getD_lt hbg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbg,
            Option.getD_some]
          exact hs'
        · right; exact ⟨by omega, h2⟩
      · have hbX : b < (segBytesX g).length := by omega
        have hy := segBytesX_getElem?_ge (g := g) (by omega) (List.getElem?_eq_getElem hbX)
        rcases OsMeta.pc_some hy.2 with ht | ⟨z, hz, hzb, -⟩
        · rcases htc b _ (by omega) ht hb with ⟨s, hs'⟩ | ⟨h1, h2⟩
          · left; refine ⟨s, ?_⟩
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbX, Option.getD_some]
            exact hs'
          · right; exact ⟨by omega, h2⟩
        · right; exact ⟨by omega, hzfc z hz b hzb hb⟩
    rcases hcase with ⟨s, hs'⟩ | ⟨hwb, h0⟩
    · by_cases hwb : b < lay0.wr
      · rw [hlow b hwb] at hs'; exact ⟨s, hs'⟩
      · rcases hrz b (by omega) with he | ⟨k, -, -, he⟩
        · rw [he] at hs'; exact ⟨s, hs'⟩
        · rw [he] at hs'
          rcases List.mem_append.1 hs' with hs' | hs'
          · exact ⟨s, hs'⟩
          · simp only [List.mem_singleton, Prod.mk.injEq] at hs'
            rw [hs'.1]; exact tail_zero_cand ((habs0.last g0 hg0).1 hex0) hZ (by omega) (by omega)
    · rw [h0]; exact tail_zero_cand ((habs0.last g0 hg0).1 hex0) hZ hwb (by omega)
  -- W1 over `g0`'s bytes, from the window's (the known resizes' zeros dropped)
  have hw' : W1G C (walInos (entsOf m' lay0.j)) (fun i => imgOf (fo i)) (segBytesOf lay0)
      (segRzOf lay) := by
    rw [← hj]
    refine W1G.drop_rz hw (fun i bs hbs => ?_)
    obtain ⟨g', hg', rfl, rfl⟩ := segBytesOf_some_ex hexall hbs
    rw [hs0, List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hgp | rfl
    · refine ⟨segBytesX g', segBytesOf_mem hndl (by rw [hs]; simp [hgp]), segBytesX_length_le,
        fun b hb => .inl ?_⟩
      rw [segBytesX_getD_lt hb]
    · refine ⟨segBytesX g, by rw [← hino]; exact segBytesOf_mem hndl hgm, hlenX, fun b hb => ?_⟩
      rw [← hino, segRzOf_of_mem hndl hgm]
      exact hrz b hb
  rcases hok m' fo0 hr hf0 hn0 hw0 with h | ⟨la, hla, h⟩
  · left
    have h1 : CrashTo C Mr d lay0 m' fo :=
      crashTo_tailL hC habs0 hZ hB hnd hg0 hex0 d.m habs0.lastSynced h
        (fun i hi => hfo i (by rw [hino]; exact hi)) himg0
        (fun h' => by rw [← hino]; exact hnmd g hgm (by rw [hj, hino]; exact h')) hw'
    exact crashTo_congr_lay hjr hnm hj hcuts hfirst hinos h1
  · right
    exact ⟨la, hla, crashTo_congr_fo (fun g' hg' => hfo _ (halt la hla g' hg')) h⟩

end win

end WalFs
end EtcdGrove
end Perennial

end
