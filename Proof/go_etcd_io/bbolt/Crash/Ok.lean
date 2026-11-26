/- Lean-first (no Rocq counterpart).

# bbolt's crash invariant: every crash image of a `BDur` state is good

`bDur_okS`: a state of bbolt's file satisfying the durability predicate `BDur a s`
(`Crash/Dur.lean`) meets its crash obligation `FileOkS` under the premise `BoltCrashWhole` of its
inode, with `Good` the phase's good images (`bOk a`: `cur`'s data while idle, `cur`'s or `prev`'s
while committing, a file `needsInit` accepts or `init`'s image during `init`); an idle state in
`DB.grow`'s window needs `bDur_okSU` (no whole pages, `Crash/Dur.lean`'s header).

The proof is per phase (`idle_view`, `commit_view`, `init_view`), on the crash's file as `BView`
gives it (`Crash/View.lean`): the protected bytes are the reference images' (`view_psync`), so the
file is an image of the same committed state with its own meta slots (`fileOK_transfer`); while
committing, the slot being written validates only as the old slot, all 64 of its bytes (its
checksum bytes are as of the fields' change or older: `BoltCrashWhole`), whose meta `prev`'s
`metaOk` makes older, so the image is `prev`'s; or as the new meta (the image is `cur`'s).
-/
module

public import Proof.go_etcd_io.bbolt.Crash.Dur

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs
open go_etcd_io.bbolt.internal.common

section ok
variable [GooseExts]

omit [GooseExts] in
theorem xb_some (X : List w8) (b : Nat) (hb : b < X.length) : some (xb X b) = X[b]? := by
  show some (X.getD b 0) = _
  rw [List.getElem?_eq_getElem hb, getD_eq_getElem' _ _ _ hb]

theorem maxBytes_bounds (n : Nat) (h : n ≤ maxBytes) : n < 2 ^ 62 ∧ n ≤ 0xFFFFFFFFFFFF := by
  unfold maxBytes at h; constructor <;> omega

/-- A reference image's meta tail byte is zero. -/
theorem refImg_tail {X : List w8} {C : CommitSt} (hR : RefImg X C) {j k : Nat} (hj : j < 2)
    (hk1 : 80 ≤ k) (hk2 : k < 4096) : xb X (4096 * j + k) = 0 := by
  have := hR.len; have := refImg_hwm hR
  have hb : 4096 * j + k < X.length := by omega
  exact hR.tails j hj k hk1 hk2 _ (xb_some X _ hb).symm

/-! ## The crashed file's txid -/

/-- **Every committed state a file's metas name has txid at most `t`** (what `fileRcpt` needs). -/
def txidLe (f : OsFile) (t : Nat) : Prop :=
  ∀ C', fileImage f.contents C' → C'.metaOk → C'.txid ≤ t

/-- Two committed states with the same metas, both `metaOk`, have the same txid. -/
theorem metaOk_txid_eq {C1 C2 : CommitSt} (h1 : C1.metaOk) (h2 : C2.metaOk) (e0 : C1.m0 = C2.m0)
    (e1 : C1.m1 = C2.m1) : C1.txid = C2.txid := by
  have hs : ∀ i, C1.slot i = C2.slot i := fun i => by unfold CommitSt.slot; rw [e0, e1]
  have key : ∀ i j, i % 2 = j % 2 → C1.slot i = C1.slot j := by
    intro i j h; unfold CommitSt.slot; rw [h]
  have key2 : ∀ i j, i % 2 = j % 2 → C2.slot i = C2.slot j := by
    intro i j h; unfold CommitSt.slot; rw [h]
  obtain ⟨-, -, -, -, -, hv1, hm1, ho1⟩ := h1
  obtain ⟨-, -, -, -, -, hv2, hm2, ho2⟩ := h2
  by_cases hp : C1.txid % 2 = C2.txid % 2
  · have e : C1.slot C1.txid = C2.slot C2.txid := by rw [key _ _ hp, hs]
    have a1 := hm1.1
    have a2 := hm2.1
    rw [e] at a1
    omega
  · have e : C2.slot C2.txid = C1.slot (C1.txid + 1) := by rw [← hs]; exact key _ _ (by omega)
    have e' : C1.slot C1.txid = C2.slot (C2.txid + 1) := by rw [hs]; exact key2 _ _ (by omega)
    have l1 := ho1 (e ▸ hv2)
    have l2 := ho2 (e' ▸ hv1)
    have a1 := hm1.1
    have a2 := hm2.1
    rw [← e] at l1
    rw [← e'] at l2
    omega

/-- `txidLe` from a `metaOk` state with the file's metas. -/
theorem txidLe_of (f : OsFile) (C0 : CommitSt) {t : Nat}
    (hm : ({ C0 with m0 := bytesAt f.contents 0 4096, m1 := bytesAt f.contents 4096 4096 } :
      CommitSt).metaOk) (ht : C0.txid ≤ t) : txidLe f t := by
  intro C' hi hm'
  have := metaOk_txid_eq hm' hm hi.1 hi.2.1
  rw [this]; exact ht

/-! ## Idle -/

/-- **An idle state's crash image is an image of `cur`'s data**, of whole pages if the size has
not moved since the last sync. -/
theorem idle_view {C : CommitSt} {X : List w8} {s : CSt} {f : OsFile} (hW : BWf s)
    (hI : IdleOk C X s) (hV : BView s f) :
    bGoodU (treeData C) f ∧ (s.CrashSize f.size → f.size % 4096 = 0) ∧ txidLe f C.txid := by
  obtain ⟨hR, hmeta, hdata, hhwm, hal, hwr, hxa⟩ := hI
  have h3 := refImg_hwm hR
  have hXl := hR.len
  have hlo := vmeta_lo_of s hW
  have hfl := hV.lo
  have hyl := contents_length' f
  have hag : ∀ b, protData X C b → f.contents[b]? = X[b]? := by
    intro b hb
    obtain ⟨-, hb2⟩ := protData_range hR hb
    rw [view_psync hW hV (hdata b hb) (by omega), xb_some X b (by omega)]
  have hagm : ∀ b < 8192, f.contents[b]? = X[b]? := by
    intro b hb
    rw [view_psync hW hV (hmeta b hb) (by omega), xb_some X b (by omega)]
  have hm0 : bytesAt f.contents 0 4096 = C.m0 := by
    rw [hR.img.1]; exact bytesAt_congr X _ 0 4096 (by omega) (by omega)
      (fun b _ h2 => hagm b (by omega))
  have hm1 : bytesAt f.contents 4096 4096 = C.m1 := by
    rw [hR.img.2.1]; exact bytesAt_congr X _ 4096 4096 (by omega) (by omega)
      (fun b _ h2 => hagm b (by omega))
  have hok := fileOK_transfer X f.contents C hR (by omega) hag (by rw [hm0, hm1]; exact hR.mok)
  rw [hyl] at hok
  obtain ⟨hb1, hb2⟩ := maxBytes_bounds _ hV.max
  refine ⟨⟨hok, hb1, hb2⟩, fun hcs => ?_,
    txidLe_of f C (by rw [hm0, hm1]; exact hR.mok) (Nat.le_refl _)⟩
  obtain ⟨l, hl, hla, htr, hwone⟩ := hxa
  rcases hcs l hl with hin | hb
  · exact hla _ hin
  · revert hb
    rcases hbs : s.busy with _ | ⟨t, off, data, n⟩ | ⟨t, sz, n⟩ <;> intro hb
    · exact (hb : False).elim
    · rw [CSt.crashSize_write_in hbs (hwr t off data n hbs) hl (hwone t off data n hbs) hcs]
      exact hal
    · have hb' : f.size = sz := hb
      rw [hb']; exact htr t sz n hbs

/-! ## Committing -/

/-- **A committing state's crash image is an image of `cur`'s or `prev`'s data**, of whole pages. -/
theorem commit_view {C P : CommitSt} {Xc Xp : List w8} {s : CSt} {f : OsFile} (hW : BWf s)
    (hC : CommitOk C P Xc Xp s) (hV : BView s f) :
    (bGoodU (treeData C) f ∨ bGoodU (treeData P) f) ∧ f.size % 4096 = 0 ∧ txidLe f C.txid := by
  obtain ⟨hRp, hRc, htx, hsl, hslotp, ⟨N, hfl⟩, hdp, hdc, hhp, hhc, hal, hvlo, hvhi, -⟩ := hC
  have h3 := refImg_hwm hRp
  have hC3 := refImg_hwm hRc
  have hXpl := hRp.len
  have hXcl := hRc.len
  have hlo := vmeta_lo_of s hW
  have hfsz : f.size = s.m.lo := by have := hV.lo; have := hV.hi; omega
  have hyl := contents_length' f
  have hjp : (P.txid + 1) % 2 = C.txid % 2 := by rw [htx]
  have hpj : (C.txid + 1) % 2 = P.txid % 2 := by rw [htx]; omega
  have hj2 : C.txid % 2 < 2 := Nat.mod_lt _ (by omega)
  have hp2 : P.txid % 2 < 2 := Nat.mod_lt _ (by omega)
  -- the synced bytes
  have hagp : ∀ b, protData Xp P b → f.contents[b]? = Xp[b]? := by
    intro b hb
    obtain ⟨-, hb2⟩ := protData_range hRp hb
    rw [view_psync hW hV (hdp b hb) (by omega), xb_some Xp b (by omega)]
  have hagc : ∀ b, protData Xc C b → f.contents[b]? = Xc[b]? := by
    intro b hb
    obtain ⟨-, hb2⟩ := protData_range hRc hb
    rw [view_psync hW hV (hdc b hb) (by omega), xb_some Xc b (by omega)]
  have hagsp : ∀ k < 4096, f.contents[4096 * (P.txid % 2) + k]? =
      Xp[4096 * (P.txid % 2) + k]? := by
    intro k hk
    rw [view_psync hW hV (hslotp k hk) (by omega), xb_some Xp (4096 * (P.txid % 2) + k) (by omega)]
  -- the slot being written
  have hpgj : ∀ k < 4096, pageIn f.size (4096 * (C.txid % 2) + k) = true := by
    intro k hk; simp only [pageIn, decide_eq_true_eq]
    have := Nat.mul_div_le (4096 * (C.txid % 2) + k) 4096; omega
  have hsj : ∀ k < 4096, f.cache (4096 * (C.txid % 2) + k) = xb Xp (4096 * (C.txid % 2) + k) ∨
      f.cache (4096 * (C.txid % 2) + k) = xb Xc (4096 * (C.txid % 2) + k) := by
    intro k hk
    obtain ⟨c, hc, hov⟩ := hfl k hk
    rcases hV.byte _ c (hpgj k hk) hc with ⟨q, hq⟩ | ⟨h1, -⟩
    · exact candOV_mem hov hq
    · omega
  -- the meta tails
  have htz : metaTailsZero f.contents := by
    intro j hj k hk1 hk2 v hv
    have hb : 4096 * j + k < f.size := by omega
    rw [contents_getElem? f _ hb, Option.some.injEq] at hv
    subst hv
    have hcase : j = P.txid % 2 ∨ j = C.txid % 2 := by omega
    rcases hcase with rfl | rfl
    · have e := hagsp k hk2
      rw [contents_getElem? f (4096 * (P.txid % 2) + k) (by omega),
        ← xb_some Xp (4096 * (P.txid % 2) + k) (by omega),
        refImg_tail hRp hp2 hk1 hk2, Option.some.injEq] at e
      exact e
    · rcases hsj k hk2 with e | e
      · rw [refImg_tail hRp hj2 hk1 hk2] at e; exact e
      · rw [refImg_tail hRc hj2 hk1 hk2] at e; exact e
  -- the size bounds
  obtain ⟨hb1, hb2⟩ := maxBytes_bounds _ hV.max
  have hal' : f.size % 4096 = 0 := by rw [hfsz, ← hlo, hvlo]; exact hal
  suffices hsuf : (bGoodU (treeData C) f ∨ bGoodU (treeData P) f) ∧ txidLe f C.txid from
    ⟨hsuf.1, hal', hsuf.2⟩
  -- slot `p` holds `prev`'s current meta
  have hslp : bytesAt f.contents (4096 * (P.txid % 2)) 4096 = P.slot P.txid := by
    rw [refImg_slot hRp]
    exact bytesAt_congr Xp _ _ 4096 (by omega) (by omega) (fun b h1 h2 => by
      have := hagsp (b - 4096 * (P.txid % 2)) (by omega)
      rwa [show 4096 * (P.txid % 2) + (b - 4096 * (P.txid % 2)) = b by omega] at this)
  have hPm := hRp.mok
  obtain ⟨-, -, hPps, -, -, hPv, hPis, hPoth⟩ := hPm
  have hlen0 : (bytesAt f.contents 0 4096).length = 4096 := bytesAt_length' _ _ _ (by omega)
  have hlen1 : (bytesAt f.contents 4096 4096).length = 4096 := bytesAt_length' _ _ _ (by omega)
  -- the image of `prev`, if the slot being written is not a newer valid meta
  have hgoodP : (metaValid (metaOf (bytesAt f.contents (4096 * (C.txid % 2)) 4096)) →
      (metaOf (bytesAt f.contents (4096 * (C.txid % 2)) 4096)).pageSize'.toNat = 4096 ∧
        (metaOf (bytesAt f.contents (4096 * (C.txid % 2)) 4096)).txid'.toNat < P.txid) →
      bGoodU (treeData P) f ∧ txidLe f C.txid := by
    intro hoth
    have hm : ({ P with m0 := bytesAt f.contents 0 4096, m1 := bytesAt f.contents 4096 4096 } :
        CommitSt).metaOk := by
      apply metaOk_mk _ hlen0 hlen1
      · rw [slot_with]; show metaValid (metaOf (bytesAt f.contents (4096 * (P.txid % 2)) 4096))
        rw [hslp]; exact hPv
      · rw [slot_with]; show (metaOf (bytesAt f.contents (4096 * (P.txid % 2)) 4096)).pageSize'.toNat = 4096
        rw [hslp]; exact hPps _ hPv
      · rw [slot_with]; show P.isMeta (metaOf (bytesAt f.contents (4096 * (P.txid % 2)) 4096))
        rw [hslp]; exact hPis
      · rw [slot_with]; show metaValid (metaOf (bytesAt f.contents (4096 * ((P.txid + 1) % 2)) 4096)) → _
        rw [hjp]; exact hoth
      · exact metaTailsZero_slot _ htz 0 (by omega)
      · exact metaTailsZero_slot _ htz 1 (by omega)
    have hok := fileOK_transfer Xp f.contents P hRp (by rw [hyl, hfsz]; exact hhp) hagp hm
    rw [hyl] at hok
    exact ⟨⟨hok, hb1, hb2⟩, txidLe_of f P hm (by omega)⟩
  -- the meta of the slot being written
  have hraw := metaSlot_raw f (C.txid % 2) (by omega)
  by_cases hv : metaValid (metaOf (bytesAt f.contents (4096 * (C.txid % 2)) 4096))
  · have hv' : metaValid (decode (rawMeta f (C.txid % 2)) : Meta) := by
      unfold metaOf at hv; rwa [hraw] at hv
    have hval := metaValid_validates _ (rawMeta_length f _) hv'
    obtain ⟨n, hn, hncs⟩ := hV.slot (by rw [hvlo]) (by rw [hvhi]) _ hj2 (by omega) hval
      (fun k hk => by
        obtain ⟨c, hc, -⟩ := hfl (16 + k) (by omega)
        rw [← Nat.add_assoc] at hc; rw [hc]; rfl)
    have hk' : ∀ k < 64, ∃ c, crashCands s (4096 * (C.txid % 2) + 16 + k) = some c ∧
        CandOV c (xb Xp (4096 * (C.txid % 2) + 16 + k)) (xb Xc (4096 * (C.txid % 2) + 16 + k)) N := by
      intro k hk
      have := hfl (16 + k) (by omega)
      rwa [← Nat.add_assoc] at this
    -- the slot: all 64 bytes old, or the 56 field bytes new
    have hall : (∀ k < 64, f.cache (4096 * (C.txid % 2) + 16 + k) =
          xb Xp (4096 * (C.txid % 2) + 16 + k)) ∨
        (∀ k < 56, f.cache (4096 * (C.txid % 2) + 16 + k) =
          xb Xc (4096 * (C.txid % 2) + 16 + k)) := by
      -- a byte as of a stamp before the first new one is old
      have hold : ∀ k < 64, ∀ c, crashCands s (4096 * (C.txid % 2) + 16 + k) = some c →
          CandOV c (xb Xp (4096 * (C.txid % 2) + 16 + k)) (xb Xc (4096 * (C.txid % 2) + 16 + k)) N →
          ∀ m, (∀ N0, N = some N0 → m < N0) → valAt c m = xb Xp (4096 * (C.txid % 2) + 16 + k) := by
        intro k hk c hc hov m hm
        rw [valAt_candOV hov]
        cases N with
        | none => rfl
        | some N0 => exact if_neg (Nat.not_le.2 (hm N0 rfl))
      by_cases hnew : ∃ N0, N = some N0 ∧ N0 ≤ n
      · right; intro k hk
        obtain ⟨N0, rfl, hN⟩ := hnew
        obtain ⟨c, hc, hov⟩ := hk' k (by omega)
        rw [hn k hk c hc, valAt_candOV hov]; exact if_pos hN
      · left; intro k hk
        obtain ⟨c, hc, hov⟩ := hk' k hk
        have hlt : ∀ m, m ≤ n → ∀ N0, N = some N0 → m < N0 := fun m hm N0 hN0 =>
          Nat.lt_of_le_of_lt hm (Nat.lt_of_not_le fun h => hnew ⟨N0, hN0, h⟩)
        by_cases h56 : k < 56
        · rw [hn k h56 c hc]; exact hold k hk c hc hov n (hlt n (Nat.le_refl n))
        · obtain ⟨m, hm, e⟩ := hncs k (by omega) hk c hc
          rw [e]; exact hold k hk c hc hov m (hlt m hm)
    have htk : (encode (metaOf (bytesAt f.contents (4096 * (C.txid % 2)) 4096))).take 56 =
        (List.range 56).map fun k => f.cache (4096 * (C.txid % 2) + 16 + k) := by
      unfold metaOf; rw [hraw]; exact rawMeta_take56 f _
    rcases hall with hold | hnew
    · -- the old slot, whole: `prev`'s `metaOk` makes it older
      refine (fun h => ⟨Or.inr h.1, h.2⟩) (hgoodP fun hv2 => ?_)
      have hrawold : rawMeta f (C.txid % 2) = bytesAt (bytesAt Xp (4096 * (C.txid % 2)) 4096) 16 64 := by
        apply List.ext_getElem?
        intro k
        by_cases hk : k < 64
        · rw [bytesAt_getElem? _ 16 64 k hk,
            bytesAt_getElem? Xp (4096 * (C.txid % 2)) 4096 (16 + k) (by omega),
            ← xb_some Xp (4096 * (C.txid % 2) + (16 + k)) (by omega)]
          simp only [rawMeta, List.getElem?_map, List.getElem?_range hk, Option.map_some]
          rw [hold k hk, Nat.add_assoc]
        · rw [List.getElem?_eq_none (by rw [rawMeta_length]; omega),
            List.getElem?_eq_none (by simp [bytesAt]; omega)]
      have hmc : metaOf (bytesAt f.contents (4096 * (C.txid % 2)) 4096) =
          metaOf (P.slot (P.txid + 1)) := by
        rw [refImg_slot hRp, hjp]
        unfold metaOf; rw [hraw, hrawold]
      rw [hmc] at hv2 ⊢
      exact ⟨hPps _ hv2, hPoth hv2⟩
    · -- the new meta: the image is `cur`'s
      have hmnew : (encode (metaOf (C.slot C.txid))).take 56 =
          (List.range 56).map fun k => xb Xc (4096 * (C.txid % 2) + 16 + k) := by
        rw [refImg_slot hRc, metaOf_take56 _ (by
          rw [bytesAt_length' Xc (4096 * (C.txid % 2)) 4096 (by omega)]; omega)]
        apply List.map_congr_left; intro k hk; rw [List.mem_range] at hk
        rw [bytesAt_getD Xc (4096 * (C.txid % 2)) (16 + k) (by omega) (by omega)]; congr 1; omega
      have heq : (encode (metaOf (bytesAt f.contents (4096 * (C.txid % 2)) 4096))).take 56 =
          (encode (metaOf (C.slot C.txid))).take 56 := by
        rw [htk, hmnew]; apply List.map_congr_left; intro k hk; rw [List.mem_range] at hk
        exact hnew k hk
      have hCm := hRc.mok
      obtain ⟨-, -, hCps, -, -, hCv, hCis, -⟩ := hCm
      have hmeq : metaOf (bytesAt f.contents (4096 * (C.txid % 2)) 4096) = metaOf (C.slot C.txid) :=
        meta_eq_of_valid _ _ heq hv hCv
      have hslc : bytesAt f.contents (4096 * ((C.txid + 1) % 2)) 4096 = P.slot P.txid := by
        rw [hpj, hslp]
      have hm : ({ C with m0 := bytesAt f.contents 0 4096, m1 := bytesAt f.contents 4096 4096 } :
          CommitSt).metaOk := by
        apply metaOk_mk _ hlen0 hlen1
        · rw [slot_with]; show metaValid (metaOf (bytesAt f.contents (4096 * (C.txid % 2)) 4096))
          rw [hmeq]; exact hCv
        · rw [slot_with]
          show (metaOf (bytesAt f.contents (4096 * (C.txid % 2)) 4096)).pageSize'.toNat = 4096
          rw [hmeq]; exact hCps _ hCv
        · rw [slot_with]; show C.isMeta (metaOf (bytesAt f.contents (4096 * (C.txid % 2)) 4096))
          rw [hmeq]; exact hCis
        · rw [slot_with]
          show metaValid (metaOf (bytesAt f.contents (4096 * ((C.txid + 1) % 2)) 4096)) → _
          rw [hslc]; intro _
          exact ⟨hPps _ hPv, by show _ < C.txid; rw [hPis.1, htx]; omega⟩
        · exact metaTailsZero_slot _ htz 0 (by omega)
        · exact metaTailsZero_slot _ htz 1 (by omega)
      have hok := fileOK_transfer Xc f.contents C hRc (by rw [hyl, hfsz]; exact hhc) hagc hm
      rw [hyl] at hok
      exact ⟨Or.inl ⟨hok, hb1, hb2⟩, txidLe_of f C hm (Nat.le_refl _)⟩
  · exact (fun h => ⟨Or.inr h.1, h.2⟩) (hgoodP (fun h => absurd h hv))

/-! ## Init -/

/-- **`init`'s image has zero meta tails** (its metas' zero tails, `initC_metaOk`). -/
theorem initImg_tails : metaTailsZero initImg :=
  fileImage_tails _ _ initImg_ok.1 initImg_ok.2.1

/-- **`init`'s whole image is a good image of the empty data.** -/
theorem bGood_initImg (f : OsFile) (hsz : f.size = 16384)
    (hall : ∀ b < 16384, f.cache b = initByte b) : bGood ∅ f := by
  have hc : f.contents = initImg := by
    apply List.ext_getElem?; intro b
    by_cases hb : b < 16384
    · rw [contents_getElem? f b (by omega), hall b hb,
        ← xb_some initImg b (by rw [initImg_length]; exact hb)]
      rfl
    · rw [List.getElem?_eq_none (by rw [contents_length']; omega),
        List.getElem?_eq_none (by rw [initImg_length]; omega)]
  obtain ⟨hi, hm, ht, hfl, hh, h1, h2, hd⟩ := initImg_ok
  refine ⟨?_, ⟨by omega, by omega⟩, by omega⟩
  rw [hc, hsz]
  exact Or.inr ⟨initC, hi, hm, ht, hfl, by rw [initImg_length] at hh; exact hh, h1, h2, hd⟩

/-- **An init state's crash image is a file `needsInit` accepts, or `init`'s whole image.** -/
theorem init_view {s : CSt} {f : OsFile} (hI : InitOk s) (hV : BView s f) :
    bGoodInit f ∨ bGood ∅ f := by
  obtain ⟨hc, -, hhi⟩ := hI
  have hsz : f.size ≤ 16384 := by have := hV.hi; omega
  have hb : ∀ b, pageIn f.size b = true → f.cache b = 0 ∨ f.cache b = initByte b := by
    intro b hpg
    have hb16 : b < 16384 := by
      simp only [pageIn, decide_eq_true_eq] at hpg; omega
    obtain ⟨c, hcc, hq⟩ := hc b hb16
    rcases hV.byte b c hpg hcc with ⟨q, hm⟩ | ⟨-, h0⟩
    · exact hq _ hm
    · exact .inl h0
  by_cases hw : f.size = 16384 ∧ ∀ b < 16384, f.cache b = initByte b
  · exact .inr (bGood_initImg f hw.1 hw.2)
  · exact .inl ⟨hsz, hb, hw⟩

/-! ## The crash obligation -/

/-- **Every crash image of a `BDur` state is good** (whole pages but in `DB.grow`'s window). -/
theorem bDur_view {a : BAbs} {s : CSt} {f : OsFile} (h : BDur a s) (hV : BView s f) :
    bCrashU a f := by
  obtain ⟨hW, hP⟩ := h
  unfold bCrashU
  revert hP
  cases a.phase <;> intro hP <;> dsimp only at hP ⊢
  · exact (idle_view hW hP hV).1
  · exact (commit_view hW hP hV).1
  · exact init_view hP hV

/-- **Every crash image of a `BDur` state is good, of whole pages**, its size one the ghost state
knows a crash may leave (`CSt.CrashSize`). -/
theorem bDur_view_al {a : BAbs} {s : CSt} {f : OsFile} (h : BDur a s)
    (hcs : s.CrashSize f.size) (hV : BView s f) : bCrash a f := by
  obtain ⟨hW, hP⟩ := h
  unfold bCrash
  revert hP
  cases a.phase <;> intro hP <;> dsimp only at hP ⊢
  · obtain ⟨h1, h2, -⟩ := idle_view hW hP hV
    exact bGoodU_bGood h1 (h2 hcs)
  · obtain ⟨h1, h2, -⟩ := commit_view hW hP hV
    rcases h1 with h1 | h1
    · exact .inl (bGoodU_bGood h1 h2)
    · exact .inr (bGoodU_bGood h1 h2)
  · exact init_view hP hV

/-- **bbolt's crash obligation**: a `BDur` state meets `FileOkS` under `BoltCrashWhole` of its
inode, with the good images of its phase, of whole pages (`crashSeen_crashSize`). -/
theorem bDur_okS (i : Ino) (a : BAbs) (s : CSt) (h : BDur a s) :
    FileOkS (BoltCrashWhole (· = i)) (bOk a) i s := by
  intro hcut f hfc hseen g hg
  cases hg
  exact bDur_view_al h (crashSeen_crashSize hseen f rfl) (bview_of h.1.1 hcut h.1.2.1 hfc hseen)

/-- **bbolt's crash obligation in every state** (no whole pages in `DB.grow`'s window). -/
theorem bDur_okSU (i : Ino) (a : BAbs) (s : CSt) (h : BDur a s) :
    FileOkS (BoltCrashWhole (· = i)) (bOkU a) i s := by
  intro hcut f hfc hseen g hg
  cases hg
  exact bDur_view h (bview_of h.1.1 hcut h.1.2.1 hfc hseen)

/-- **The crash images' txid** (idle and committing): every state their metas name is at most the
current one's. -/
theorem bDur_view_txid {a : BAbs} {s : CSt} {f : OsFile} (h : BDur a s) (hni : a.phase ≠ .init)
    (hV : BView s f) : txidLe f a.cur.txid := by
  obtain ⟨hW, hP⟩ := h
  revert hP hni
  cases a.phase <;> intro hni hP <;> (try dsimp only at hP)
  · exact (idle_view hW hP hV).2.2
  · exact (commit_view hW hP hV).2.2
  · exact absurd rfl hni

/-- `bOk` with the crash images' txid bound (outside `init`). -/
def bOkT (a : BAbs) (fo : Option OsFile) : Prop :=
  ∀ f, fo = some f → bCrash a f ∧ (a.phase ≠ .init → txidLe f a.cur.txid ∧ 0 < f.size)

/-- **A crash image of a state past `init` is not empty** (W6): it is at least the size's crash
bound, which a reference image's high-water mark bounds from below (at least 3 pages). -/
theorem bDur_view_pos {a : BAbs} {s : CSt} {f : OsFile} (h : BDur a s) (hni : a.phase ≠ .init)
    (hV : BView s f) : 0 < f.size := by
  obtain ⟨hW, hP⟩ := h
  have hlo := vmeta_lo_of s hW
  have hfl := hV.lo
  revert hP hni
  cases a.phase <;> intro hni hP <;> (try dsimp only at hP)
  · have h3 := refImg_hwm hP.1
    have h4 := hP.2.2.2.1
    omega
  · have h3 := refImg_hwm hP.1
    have h4 := hP.2.2.2.2.2.2.2.2.1
    omega
  · exact absurd rfl hni

/-- **bbolt's crash obligation with the txid bound** (`bDur_okS`, and `bDur_view_txid`). -/
theorem bDur_okST (i : Ino) (a : BAbs) (s : CSt) (h : BDur a s) :
    FileOkS (BoltCrashWhole (· = i)) (bOkT a) i s := by
  intro hcut f hfc hseen g hg
  cases hg
  have hV := bview_of h.1.1 hcut h.1.2.1 hfc hseen
  exact ⟨bDur_view_al h (crashSeen_crashSize hseen f rfl) hV,
    fun hni => ⟨bDur_view_txid h hni hV, bDur_view_pos h hni hV⟩⟩

end ok

end bbolt
end EtcdGrove
end Perennial
