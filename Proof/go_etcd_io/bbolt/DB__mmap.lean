module
public import Spec.go_etcd_io.bbolt.DB__mmap
public import Spec.go_etcd_io.bbolt.DB__Logger
public import Spec.go_etcd_io.bbolt.DB__fileSize
public import Spec.go_etcd_io.bbolt.DB__munmap
public import Spec.go_etcd_io.bbolt.mmap
public import Spec.go_etcd_io.bbolt.DB__page
public import Spec.go_etcd_io.bbolt.internal.common.Page__Meta
public import Spec.go_etcd_io.bbolt.DefaultLogger__Errorf
public import Proof.go_etcd_io.bbolt.PageView

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]
variable [os_fi : OsFileInfoAssumptions (GF := GF)]
variable [linux : GOOSLinux]

/-- The whole `mmapTok` (`mmaplock` write-locked) leaves no reader's token. -/
theorem mmapTok_full_none (γ : GName) (M : GMap Nat Reader) :
    mmapTok (GF := GF) γ 1 ∗ ([∗map] _k ↦ _r ∈ M, mmapTok (GF := GF) γ sync.rfrac) ⊢
      ⌜M = ∅⌝ ∗ mmapTok (GF := GF) γ 1 := by
  iintro ⟨H1, Hm⟩
  by_cases h : M = ∅
  · iframe; ipureintro; exact h
  obtain ⟨k, r, hk⟩ : ∃ k r, M !! k = some r := by
    refine Classical.byContradiction fun hc => h ((GMap.lookup_empty_iff M).1 fun k => ?_)
    cases e : M !! k with
    | none => rfl
    | some r => exact absurd ⟨k, r, e⟩ hc
  icases (BigSepM.bigSepM_lookup_acc (M := GMap Nat)
    (Φ := fun (_ : Nat) (_ : Reader) => mmapTok (GF := GF) γ sync.rfrac)
    (show Std.get? M k = some r from hk)).1 $$ Hm with ⟨Ht, -⟩
  simp only [mmapTok]
  ihave %Hv := ghostVar_valid_2 _ _ _ _ _ $$ H1 Ht
  exfalso
  have hp := (sync.rfrac).2
  have h1 := Hv.1
  generalize sync.rfrac = q at h1 hp
  have h2 : (1 + q).val ≤ (1 : Qp).val := h1
  rw [Qp.val_add, Qp.val_one] at h2
  grind

/-- `mmapSizeOf` maps at least what it is asked to, and something. -/
theorem mmapSizeOf_ge (size ps s : Int) (h0 : 0 ≤ size) (hps : 0 < ps)
    (h : mmapSizeOf size ps = some s) : size ≤ s ∧ 0 < s := by
  unfold mmapSizeOf at h
  split at h
  · rename_i i hi
    injection h with h; subst h
    have := List.find?_some hi
    simp only [decide_eq_true_eq] at this
    exact ⟨this, Int.pow_pos (by decide)⟩
  · rename_i hnone
    have h30 : ¬ size ≤ 2 ^ (15 + 15) := by
      have := List.find?_eq_none.1 hnone 15 (List.mem_range.2 (by decide))
      simpa using this
    split at h
    · cases h
    · rename_i hmax
      injection h with h; subst h
      try dsimp only
      generalize hs1 : (if size % 1073741824 > 0 then size + 1073741824 - size % 1073741824
        else size) = s1
      have hs1ge : size ≤ s1 := by rw [← hs1]; split <;> omega
      have hlt := Int.lt_ediv_add_one_mul_self s1 hps
      generalize (s1 / ps + 1) * ps = q at hlt ⊢
      constructor
      · rw [Int.le_min]; refine ⟨?_, by omega⟩; split <;> omega
      · rw [Int.lt_min]; refine ⟨?_, by decide⟩; split <;> omega

/-- A meta inside a region's bytes, lent out as one. -/
theorem meta_acc (p : Loc) (q : DFrac) (bs : List w8) (off : Nat) (h : off + 64 ≤ bs.length)
    (hp : p.locCar ≠ 0) :
    bytesPointsto (GF := GF) p q bs ⊢
      (p +ₗ (off : Int)) ↦{q} metaOf ((bs.drop off).take 64) ∗
      ((p +ₗ (off : Int)) ↦{q} metaOf ((bs.drop off).take 64) -∗ bytesPointsto p q bs) := by
  have h1 := bytesPointsto_take_drop (GF := GF) p q bs off (by omega)
  have h2 := bytesPointsto_take_drop (GF := GF) (p +ₗ (off : Int)) q (bs.drop off) 64
    (by simp only [List.length_drop]; omega)
  have hm := Meta_bytes (hG := hG) (p +ₗ (off : Int)) (metaOf ((bs.drop off).take 64)) q
    (by simpa [Loc.add] using hp)
  rw [metaBytes_metaOf _ (by simp only [List.length_take, List.length_drop]; omega),
    List.take_take, Nat.min_self] at hm
  iintro H
  icases h1.1 $$ H with ⟨Ha, Hb⟩
  icases h2.1 $$ Hb with ⟨Hb, Hc⟩
  ihave Hm := hm.2 $$ Hb
  isplitl [Hm]
  · iexact Hm
  iintro Hm
  ihave Hb := hm.1 $$ Hm
  iapply h1.2
  iframe
  iapply h2.2
  iframe

/-- The meta bytes of slot `s` are the mapping's at `s * ps + 16`. -/
theorem slot_meta (bs : List w8) (ps n s : Nat) (hps : 80 ≤ ps) (hn : s * ps + ps ≤ n) :
    ((slotAt bs ps s).drop 16).take 64 = ((bs.take n).drop (s * ps + 16)).take 64 := by
  unfold slotAt
  rw [List.drop_take, List.take_take, List.drop_take, List.take_take, List.drop_drop]
  rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]

set_option maxRecDepth 8000 in
theorem DB.mmap.wp_proof (hLogger : DB.Logger.spec (GF := GF) (hG := hG))
    (hfileSize : DB.fileSize.spec (GF := GF) (hG := hG))
    (hmmapSize : DB.mmapSize.spec (GF := GF) (hG := hG))
    (hmunmap : DB.munmap.spec (GF := GF) (hG := hG))
    (hmmap : _root_.Perennial.EtcdGrove.bbolt.mmap.spec (GF := GF) (hG := hG))
    (hpage : DB.page.spec (GF := GF) (hG := hG))
    (hMeta : Page.Meta.spec (GF := GF) (hG := hG))
    (hValidate : Meta.Validate.spec (GF := GF) (hG := hG))
    (hErrorf : DefaultLogger.Errorf.spec (GF := GF) (hG := hG)) :
    DB.mmap.spec (GF := GF) (hG := hG) := by
  intro dbl f fd bs lg dl ps ms mf rw dq dr dp ds m0 m1 m n γ M WR WR' K minsz
    Hdbl Hbl Hps80 Hps32 Hmin0 Hmin Hlg Hdr Hrw0 Hderef
  wp_start as ⟨#Hlgf, #Hdl, #Hdlok, #Hpsf, Hf, Hms, Hml, Hrw, Hmf, Hdrf, Hds, Hm0, Hm1, #Hfile,
    Hbytes, Hmap, Hmmh, Htoks, HWR, Hold⟩
  try wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  try wp_auto
  wp_apply sync.RWMutex.wp_Lock _ _ $$ [$Hmmh] as ⟨Hlocked, Htok1⟩
  try wp_auto
  icases mmapTok_full_none γ M $$ [Htok1 Htoks] with ⟨%HM, Htok1⟩
  · iframe
  subst HM
  wp_apply hLogger dbl DFrac.discard lg dl Hdbl $$ [Hlgf Hdl] as -
  · iframe; iframe #
  have Hd : (if lg = interface.nil then discardIface dl else lg) = discardIface dl := by
    rcases Hlg with rfl | rfl <;> simp [discardIface, interface.mkOk]
  rw [Hd]
  try wp_auto
  wp_apply hfileSize dbl f fd bs ps dq DFrac.discard Hbl Hps32 $$ [Hf Hpsf Hbytes]
    as %fs %err ⟨Hf, -, Hbytes, %Hfs⟩
  · iframe; iframe #
  try wp_auto
  cases err with
  | ok ei =>
    -- `fileSize` failed: log it, return its error
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    try wp_auto
    wp_apply hErrorf dl _ _ $$ [Hdlok]
    · iframe; iexact Hdlok
    try wp_auto
    wp_apply sync.RWMutex.wp_Unlock _ _ $$ [$Hlocked $Htok1] as Hmmh
    try wp_auto
    iapply HΦ
    iframe
    isplitr
    · ipureintro; rfl
    ileft
    iframe
    ipureintro; intro h; cases h
  | nil =>
    obtain ⟨Hfs1, Hfs2⟩ := Hfs rfl
    subst Hfs1
    try wp_auto
    have Hbz : sint.Z (W64 (bs.length : Int)) = bs.length := by word
    wp_join iprop(∃ sz : w64, size_ptr ↦ sz ∗ minsz_ptr ↦ minsz ∗
        ⌜sint.Z sz = max (bs.length : Int) (sint.Z minsz)⌝) with [size minsz]
      as ⟨%sz, size, minsz, %Hszv⟩
    all_goals try wp_auto
    all_goals try wp_join_done
    · iexists _; iframe; ipureintro; rw [Int.max_def]; split <;> omega
    · iexists _; iframe; ipureintro; rw [Int.max_def]; split <;> omega
    try wp_auto
    have Hpsu : sint.Z ps = uint.Z ps := by word
    wp_apply hmmapSize dbl ps DFrac.discard sz (by omega) (by omega) $$ [Hpsf] as %r %err2 ⟨-, %Hr⟩
    · iframe #
    rw [Hszv, Hpsu] at Hr
    try wp_auto
    cases hms : mmapSizeOf (max (bs.length : Int) (sint.Z minsz)) (uint.Z ps) with
    | none =>
      rw [hms] at Hr
      cases err2 with
      | nil => exact absurd rfl Hr
      | ok ei =>
        try wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl ⟨Hsl, -⟩
        try wp_auto
        wp_apply hErrorf dl _ _ $$ [Hdlok]
        · iframe; iexact Hdlok
        try wp_auto
        wp_apply sync.RWMutex.wp_Unlock _ _ $$ [$Hlocked $Htok1] as Hmmh
        try wp_auto
        iapply HΦ
        iframe
        isplitr
        · ipureintro; rfl
        ileft
        iframe
        ipureintro; intro h; cases h
    | some s =>
      rw [hms] at Hr
      obtain ⟨rfl, Hrs⟩ := Hr
      try wp_auto
      rw [GOOSLinux.goos]
      wp_join with [size fileSize Hms db]
      · try wp_auto
        wp_if_destruct
        all_goals try wp_auto
        all_goals try wp_if_destruct
        all_goals try wp_auto
        all_goals try wp_join_done
      wp_join iprop(WR' ∗ structFieldRef DB go!"rwtx" dbl ↦{dq} rw ∗ db_ptr ↦ dbl) with [HWR Hrw db]
        as ⟨HWR, Hrw, db⟩
      · try wp_join_done
        iframe
        iapply (Hrw0 rfl); iexact HWR
      · try wp_auto
        wp_apply (Hderef Hif) $$ [HWR] as HWR
        · iframe
        try wp_auto
        try wp_join_done
      -- the old mapping goes: no reader holds it now
      ihave Hold := Hold $$ %rfl HWR
      icases Hold with ⟨Hdata, Hrange, HK⟩
      ihave Hmd : iprop((⌜dr = slice.nil⌝ ∗ fileMap fd none) ∨
          (⌜dr.ptr ≠ null ∧ dr.len = W64 (n : Int) ∧ dr.cap = W64 (n : Int)⌝ ∗
            fileMap fd (some (dr.ptr, n)) ∗ mapRange (some (dr.ptr, n)) bs 0 n)) $$ [Hmap Hrange]
      · rcases Hdr with ⟨rfl, rfl⟩ | ⟨h1, h2, h3, rfl⟩
        · ileft; iframe; ipureintro; rfl
        · iright; iframe; ipureintro; exact ⟨h1, h2, h3⟩
      wp_apply hmunmap dbl dr dp ds m0 m1 fd bs n $$ [Hm0 Hm1 Hdrf Hdata Hds Hbytes Hmd]
        as ⟨Hdrf, Hdata, Hds, Hm0, Hm1, Hbytes, Hmap⟩
      · iframe
      try wp_auto
      have Hsge := mmapSizeOf_ge _ _ _ (by omega) (by omega) hms
      have Hr0 : 0 < sint.Z r := by omega
      wp_apply hmmap dbl f mf dq slice.nil null (W64 0) fd bs r Hr0
        $$ [Hf Hmf Hdrf Hdata Hds Hfile Hbytes Hmap] as %err3 ⟨Hf, Hmf, Hbytes, Hres⟩
      · iframe; iframe #
      try wp_auto
      icases Hres with (⟨%Herr, Hdrf, Hdata, Hds, Hmapx⟩ | ⟨%b, %Hb, Hdrf, Hdata, Hds, Hmap, Hrange⟩)
      · -- `mmap` failed: the mapping is gone (or lost)
        cases err3 with
        | nil => exact absurd rfl Herr
        | ok ei =>
          try wp_auto
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %sl ⟨Hsl, -⟩
          try wp_auto
          wp_apply hErrorf dl _ _ $$ [Hdlok]
          · iframe; iexact Hdlok
          try wp_auto
          wp_apply sync.RWMutex.wp_Unlock _ _ $$ [$Hlocked $Htok1] as Hmmh
          try wp_auto
          iapply HΦ
          iframe
          isplitr
          · ipureintro; rfl
          iright; ileft
          isplitr
          · ipureintro; intro h; cases h
          iframe
          icases Hmapx with (Hmapn | ⟨%p, Hmapp, Hrp⟩)
          · iexists none, 0
            simp only [mapRange]
            iframe
          · iexists (some (p, sint.nat r)), sint.nat r
            iframe
      · obtain ⟨rfl, Hbl', Hbc, Hbp⟩ := Hb
        try wp_auto
        wp_apply hpage dbl b.ptr ps (DFrac.own 1) DFrac.discard (W64 0) Hbp (by word) $$ [Hdata Hpsf]
          as ⟨Hdata, -⟩
        · iframe; iframe #
        wp_apply hMeta
        try wp_auto
        wp_apply hpage dbl b.ptr ps (DFrac.own 1) DFrac.discard (W64 1) Hbp (by word) $$ [Hdata Hpsf]
          as ⟨Hdata, -⟩
        · iframe; iframe #
        wp_apply hMeta
        try wp_auto
        -- the metas, read out of the mapped bytes
        have Hbr : (bs.length : Int) ≤ sint.Z r := by
          have := Hsge.1; rw [Int.max_def] at this; split at this <;> omega
        have HbN : bs.length ≤ sint.nat r := by word
        have Hlen : (bs.take (sint.nat r)).length = bs.length := by
          rw [List.length_take]; omega
        have Hmr : mapRange (GF := GF) (some (b.ptr, sint.nat r)) bs 0 (sint.nat r) =
            bytesPointsto b.ptr (DFrac.own (Qp.half 1)) (bs.take (sint.nat r)) := by
          simp [mapRange, List.take_take]
        ihave Hb : bytesPointsto b.ptr (DFrac.own (Qp.half 1)) (bs.take (sint.nat r)) $$ [Hrange]
        · rw [← Hmr]
          iexact Hrange
        have Ha0 : b.ptr +ₗ uint.Z (W64 0 * ps) +ₗ 16 = b.ptr +ₗ ((16 : Nat) : Int) := by
          rw [loc_add_assoc]; congr 1; word
        have Ha1 : b.ptr +ₗ uint.Z (W64 1 * ps) +ₗ 16 = b.ptr +ₗ ((uint.nat ps + 16 : Nat) : Int) := by
          rw [loc_add_assoc]; congr 1; word
        rw [Ha0, Ha1]
        icases meta_acc b.ptr _ (bs.take (sint.nat r)) 16 (by omega) Hbp $$ Hb with ⟨HM, Hback⟩
        wp_apply hValidate _ _ _ (by simpa [Loc.add] using Hbp) $$ [HM] as %e0 ⟨HM, %He0⟩
        · iframe
        ihave Hb := Hback $$ HM
        try wp_auto
        icases meta_acc b.ptr _ (bs.take (sint.nat r)) (uint.nat ps + 16) (by rw [Hlen]; word) Hbp $$ Hb
          with ⟨HM, Hback⟩
        wp_apply hValidate _ _ _ (by simpa [Loc.add] using Hbp) $$ [HM] as %e1 ⟨HM, %He1⟩
        · iframe
        ihave Hb := Hback $$ HM
        try wp_auto
        -- the result: the new mapping and its metas
        have Hc0 : b.ptr +ₗ ((16 : Nat) : Int) = b.ptr +ₗ 16 := rfl
        have Hc1 : b.ptr +ₗ ((uint.nat ps + 16 : Nat) : Int) = b.ptr +ₗ (uint.Z ps + 16) := by
          congr 1 <;> word
        have Hmeta : ∀ (v0 v1 : internal.common.Meta),
            v0 = metaOf (((bs.take (sint.nat r)).drop 16).take 64) →
            v1 = metaOf (((bs.take (sint.nat r)).drop (uint.nat ps + 16)).take 64) →
            (metaValid v0 ∨ metaValid v1) → metasOK bs (uint.nat ps) v0 v1 := by
          intro v0 v1 h0 h1 hv
          refine ⟨?_, ?_, hv⟩
          · rw [h0, metaBytes_metaOf _ (by simp only [List.length_take, List.length_drop]; omega),
              List.take_take, Nat.min_self]
            have := slot_meta bs (uint.nat ps) (sint.nat r) 0 (by word) (by word)
            simpa using this
          · rw [h1, metaBytes_metaOf _ (by simp only [List.length_take, List.length_drop]; word),
              List.take_take, Nat.min_self]
            have := slot_meta bs (uint.nat ps) (sint.nat r) 1 (by word) (by word)
            simpa [Nat.add_comm] using this
        cases e0 with
        | nil =>
          try wp_auto
          wp_apply sync.RWMutex.wp_Unlock _ _ $$ [$Hlocked $Htok1] as Hmmh
          try wp_auto
          iapply HΦ
          rw [Hc0, Hc1]
          iframe
          isplitr
          · ipureintro; rfl
          iright; iright
          isplitr
          · ipureintro; rfl
          iframe
          iexists metaOf (((bs.take (sint.nat r)).drop 16).take 64),
            metaOf (((bs.take (sint.nat r)).drop (uint.nat ps + 16)).take 64)
          rw [Hmr]
          iframe
          ipureintro
          exact ⟨Hbl', Hbc, Hbp, by rw [Hrs], Hmeta _ _ rfl rfl (Or.inl (He0.1.1 rfl))⟩
        | ok i0 =>
          cases e1 with
          | nil =>
            try wp_auto
            wp_apply sync.RWMutex.wp_Unlock _ _ $$ [$Hlocked $Htok1] as Hmmh
            try wp_auto
            iapply HΦ
            rw [Hc0, Hc1]
            iframe
            isplitr
            · ipureintro; rfl
            iright; iright
            isplitr
            · ipureintro; rfl
            iframe
            iexists metaOf (((bs.take (sint.nat r)).drop 16).take 64),
              metaOf (((bs.take (sint.nat r)).drop (uint.nat ps + 16)).take 64)
            rw [Hmr]
            iframe
            ipureintro
            exact ⟨Hbl', Hbc, Hbp, by rw [Hrs], Hmeta _ _ rfl rfl (Or.inr (He1.1.1 rfl))⟩
          | ok i1 =>
            -- both invalid: log, return `err0`, and the deferred rollback unmaps
            try wp_auto
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %sl ⟨Hsl, -⟩
            try wp_auto
            wp_apply hErrorf dl _ _ $$ [Hdlok]
            · iframe; iexact Hdlok
            try wp_auto
            ihave Hmd : iprop((⌜b = slice.nil⌝ ∗ fileMap fd none) ∨
                (⌜b.ptr ≠ null ∧ b.len = W64 ((sint.nat r : Nat) : Int) ∧
                    b.cap = W64 ((sint.nat r : Nat) : Int)⌝ ∗
                  fileMap fd (some (b.ptr, sint.nat r)) ∗
                  mapRange (some (b.ptr, sint.nat r)) bs 0 (sint.nat r))) $$ [Hmap Hb]
            · iright
              rw [Hmr]
              iframe
              ipureintro
              exact ⟨loc_ne_null_of_car _ Hbp, by rw [Hbl']; word, by rw [Hbc]; word⟩
            wp_apply hmunmap dbl b b.ptr r _ _ fd bs (sint.nat r) $$ [Hm0 Hm1 Hdrf Hdata Hds Hbytes Hmd]
              as ⟨Hdrf, Hdata, Hds, Hm0, Hm1, Hbytes, Hmap⟩
            · iframe
            try wp_auto
            wp_apply sync.RWMutex.wp_Unlock _ _ $$ [$Hlocked $Htok1] as Hmmh
            try wp_auto
            iapply HΦ
            iframe
            isplitr
            · ipureintro; rfl
            iright; ileft
            isplitr
            · ipureintro; intro h; cases h
            iframe
            iexists 0
            simp only [mapRange]
            iempintro

end proof

end bbolt
end EtcdGrove
end Perennial
