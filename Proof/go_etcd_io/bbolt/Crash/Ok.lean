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
committing, the slot being written validates only as the old slot's first 56 bytes (`metaPre`: an
older txid, so the image is `prev`'s) or as the new meta (the image is `cur`'s).
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

/-! ## Idle -/

/-- **An idle state's crash image is an image of `cur`'s data**, of whole pages if the size has
not moved since the last sync. -/
theorem idle_view {C : CommitSt} {X : List w8} {s : CSt} {f : OsFile} (hW : BWf s)
    (hI : IdleOk C X s) (hV : BView s f) :
    bGoodU (treeData C) f ∧ (s.vmeta.lo = s.vmeta.hi → f.size % 4096 = 0) := by
  obtain ⟨hR, -, hmeta, hdata, hhwm, hal, -⟩ := hI
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
  have htz : metaTailsZero f.contents := by
    intro j hj k hk1 hk2 v hv
    rw [hagm _ (by omega)] at hv
    exact hR.tails j hj k hk1 hk2 v hv
  obtain ⟨hb1, hb2⟩ := maxBytes_bounds _ hV.max
  refine ⟨⟨hok, hb1, hb2, htz⟩, fun he => ?_⟩
  have := hV.hi; have := size_le_vmeta_hi s hW; have := hW.2.2.1
  have : f.size = s.m.size := by omega
  rw [this]; exact hal

/-! ## Committing -/

/-- **A committing state's crash image is an image of `cur`'s or `prev`'s data**, of whole pages. -/
theorem commit_view {C P : CommitSt} {Xc Xp : List w8} {s : CSt} {f : OsFile} (hW : BWf s)
    (hC : CommitOk C P Xc Xp s) (hV : BView s f) :
    (bGoodU (treeData C) f ∨ bGoodU (treeData P) f) ∧ f.size % 4096 = 0 := by
  obtain ⟨hRp, hRc, htx, hsl, hpre, hslotp, ⟨N, hfl⟩, hdp, hdc, hhp, hhc, hal, hvlo, hvhi, -⟩ := hC
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
  refine ⟨?_, hal'⟩
  -- slot `p` holds `prev`'s current meta
  have hslp : bytesAt f.contents (4096 * (P.txid % 2)) 4096 = P.slot P.txid := by
    rw [refImg_slot hRp]
    exact bytesAt_congr Xp _ _ 4096 (by omega) (by omega) (fun b h1 h2 => by
      have := hagsp (b - 4096 * (P.txid % 2)) (by omega)
      rwa [show 4096 * (P.txid % 2) + (b - 4096 * (P.txid % 2)) = b by omega] at this)
  have hPm := hRp.mok
  obtain ⟨-, -, hPps, -, -, hPv, hPis, -⟩ := hPm
  have hlen0 : (bytesAt f.contents 0 4096).length = 4096 := bytesAt_length' _ _ _ (by omega)
  have hlen1 : (bytesAt f.contents 4096 4096).length = 4096 := bytesAt_length' _ _ _ (by omega)
  -- the image of `prev`, if the slot being written is not a newer valid meta
  have hgoodP : (metaValid (metaOf (bytesAt f.contents (4096 * (C.txid % 2)) 4096)) →
      (metaOf (bytesAt f.contents (4096 * (C.txid % 2)) 4096)).pageSize'.toNat = 4096 ∧
        (metaOf (bytesAt f.contents (4096 * (C.txid % 2)) 4096)).txid'.toNat < P.txid) →
      bGoodU (treeData P) f := by
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
      · exact tails_drop1024 _ htz
    have hok := fileOK_transfer Xp f.contents P hRp (by rw [hyl, hfsz]; exact hhp) hagp hm
    rw [hyl] at hok
    exact ⟨hok, hb1, hb2, htz⟩
  -- the meta of the slot being written
  have hraw := metaSlot_raw f (C.txid % 2) (by omega)
  by_cases hv : metaValid (metaOf (bytesAt f.contents (4096 * (C.txid % 2)) 4096))
  · have hv' : metaValid (decode (rawMeta f (C.txid % 2)) : Meta) := by
      unfold metaOf at hv; rwa [hraw] at hv
    have hval := metaValid_validates _ (rawMeta_length f _) hv'
    obtain ⟨n, hn⟩ := hV.slot (by rw [hvlo]) (by rw [hvhi]) _ hj2 (by omega) hval
      (fun k hk => by
        obtain ⟨c, hc, -⟩ := hfl (16 + k) (by omega)
        rw [← Nat.add_assoc] at hc; rw [hc]; rfl)
    -- the 56 bytes: all old, or all new
    have hall : (∀ k < 56, f.cache (4096 * (C.txid % 2) + 16 + k) =
          xb Xp (4096 * (C.txid % 2) + 16 + k)) ∨
        (∀ k < 56, f.cache (4096 * (C.txid % 2) + 16 + k) =
          xb Xc (4096 * (C.txid % 2) + 16 + k)) := by
      have hk' : ∀ k < 56, ∃ c, crashCands s (4096 * (C.txid % 2) + 16 + k) = some c ∧
          CandOV c (xb Xp (4096 * (C.txid % 2) + 16 + k)) (xb Xc (4096 * (C.txid % 2) + 16 + k)) N := by
        intro k hk
        have := hfl (16 + k) (by omega)
        rwa [← Nat.add_assoc] at this
      rcases N with _ | N0
      · left; intro k hk
        obtain ⟨c, hc, hov⟩ := hk' k hk
        rw [hn k hk c hc]; exact valAt_candOV hov n
      · by_cases hN : N0 ≤ n
        · right; intro k hk
          obtain ⟨c, hc, hov⟩ := hk' k hk
          rw [hn k hk c hc, valAt_candOV hov]; exact if_pos hN
        · left; intro k hk
          obtain ⟨c, hc, hov⟩ := hk' k hk
          rw [hn k hk c hc, valAt_candOV hov]; exact if_neg hN
    have htk : (encode (metaOf (bytesAt f.contents (4096 * (C.txid % 2)) 4096))).take 56 =
        (List.range 56).map fun k => f.cache (4096 * (C.txid % 2) + 16 + k) := by
      unfold metaOf; rw [hraw]; exact rawMeta_take56 f _
    rcases hall with hold | hnew
    · -- the old slot: `metaPre` makes it older than `prev`
      refine Or.inr (hgoodP fun hv2 => ?_)
      have hmold : (encode (metaOf (P.slot (P.txid + 1)))).take 56 =
          (List.range 56).map fun k => xb Xp (4096 * (C.txid % 2) + 16 + k) := by
        rw [refImg_slot hRp, hjp, metaOf_take56 _ (by
          rw [bytesAt_length' Xp (4096 * (C.txid % 2)) 4096 (by omega)]; omega)]
        apply List.map_congr_left; intro k hk; rw [List.mem_range] at hk
        rw [bytesAt_getD Xp (4096 * (C.txid % 2)) (16 + k) (by omega) (by omega)]; congr 1; omega
      have heq : (encode (metaOf (bytesAt f.contents (4096 * (C.txid % 2)) 4096))).take 56 =
          (encode (metaOf (P.slot (P.txid + 1)))).take 56 := by
        rw [htk, hmold]; apply List.map_congr_left; intro k hk; rw [List.mem_range] at hk
        exact hold k hk
      exact metaPre_of_take heq hpre hv2.1 hv2.2.1
    · -- the new meta: the image is `cur`'s
      left
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
        · exact tails_drop1024 _ htz
      have hok := fileOK_transfer Xc f.contents C hRc (by rw [hyl, hfsz]; exact hhc) hagc hm
      rw [hyl] at hok
      exact ⟨hok, hb1, hb2, htz⟩
  · exact Or.inr (hgoodP (fun h => absurd h hv))

/-! ## Init -/

/-- The bytes 80 to 4096 of a meta buffer are zero. -/
theorem metaBuf_tail (mv : Meta) (k : Nat) (h1 : 80 ≤ k) (h2 : k < 4096) :
    (metaBuf mv)[k]? = some 0 := by
  unfold metaBuf
  rw [List.getElem?_append_right (by simp only [List.length_append, ByteEncoding.encode_length]; omega)]
  simp only [List.length_append, ByteEncoding.encode_length]
  rw [List.getElem?_replicate, if_pos (by omega)]; rfl

/-- **`init`'s image has zero meta tails.** -/
theorem initImg_tails : metaTailsZero initImg := by
  intro j hj k hk1 hk2 v hv
  have e : initImg = metaBuf (initMv 0) ++
      (metaBuf (initMv 1) ++ (emptyPg 2 (W16 16) ++ emptyPg 3 (W16 2))) := by
    simp only [initImg, List.append_assoc]
  rw [e] at hv
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
  · rw [show 4096 * 0 + k = k by omega,
      List.getElem?_append_left (by rw [metaBuf_length]; omega), metaBuf_tail _ k hk1 hk2] at hv
    cases hv; rfl
  · rw [List.getElem?_append_right (by rw [metaBuf_length]; omega), metaBuf_length,
      show 4096 * 1 + k - 4096 = k by omega,
      List.getElem?_append_left (by rw [metaBuf_length]; omega), metaBuf_tail _ k hk1 hk2] at hv
    cases hv; rfl

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
  refine ⟨?_, ⟨by omega, by omega⟩, by omega, by rw [hc]; exact initImg_tails⟩
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

/-- **Every crash image of a `BDur` state is good, of whole pages**, the size of an idle state
not having moved since its last sync. -/
theorem bDur_view_al {a : BAbs} {s : CSt} {f : OsFile} (h : BDur a s)
    (hst : a.phase = .idle → s.vmeta.lo = s.vmeta.hi) (hV : BView s f) : bCrash a f := by
  obtain ⟨hW, hP⟩ := h
  unfold bCrash
  revert hP hst
  cases a.phase <;> intro hst hP <;> dsimp only at hP ⊢
  · obtain ⟨h1, h2⟩ := idle_view hW hP hV
    exact bGoodU_bGood h1 (h2 (hst rfl))
  · obtain ⟨h1, h2⟩ := commit_view hW hP hV
    rcases h1 with h1 | h1
    · exact .inl (bGoodU_bGood h1 h2)
    · exact .inr (bGoodU_bGood h1 h2)
  · exact init_view hP hV

/-- **bbolt's crash obligation**: a `BDur` state meets `FileOkS` under `BoltCrashWhole` of its
inode, with the good images of its phase, of whole pages when an idle state's size has not moved
since its last sync. -/
theorem bDur_okS (i : Ino) (a : BAbs) (s : CSt) (h : BDur a s)
    (hst : a.phase = .idle → s.vmeta.lo = s.vmeta.hi) :
    FileOkS (BoltCrashWhole (· = i)) (bOk a) i s := by
  intro hcut f hfc hseen g hg
  cases hg
  exact bDur_view_al h hst (bview_of h.1.1 hcut h.1.2.1 hfc hseen)

/-- **bbolt's crash obligation in every state** (no whole pages in `DB.grow`'s window). -/
theorem bDur_okSU (i : Ino) (a : BAbs) (s : CSt) (h : BDur a s) :
    FileOkS (BoltCrashWhole (· = i)) (bOkU a) i s := by
  intro hcut f hfc hseen g hg
  cases hg
  exact bDur_view h (bview_of h.1.1 hcut h.1.2.1 hfc hseen)

end ok

end bbolt
end EtcdGrove
end Perennial
