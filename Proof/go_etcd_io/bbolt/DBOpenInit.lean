/-
A fresh database's file (`initBytes ps`, what `db.init()` writes) is well-formed
(`fileWF_initBytes`): its metas are `initMeta ps 0` and `initMeta ps 1` (both valid; the
second, of txid 1, the current one), its current tree the empty leaf on page 3, its freelist
page 2 empty.
-/
module

public import Proof.go_etcd_io.bbolt.DBOpen
public import Proof.go_etcd_io.bbolt.MetaInj
public import Spec.go_etcd_io.bbolt.DB__init

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

theorem oi_pb_len (p : Page) : (pageBytes p).length = 16 := by
  simp [pageBytes, leBytes_length']

theorem oi_mb_len (m : Meta) : (metaBytes m).length = 64 := by
  simp [metaBytes, inBucketBytes, leBytes_length']

theorem oi_mp_len (ps i : Nat) (h : 80 ≤ ps) : (initMetaPage ps i).length = ps := by
  simp only [initMetaPage, List.length_append, oi_pb_len, oi_mb_len, List.length_replicate]
  omega

theorem oi_ep_len (ps id : Nat) (fl : w16) (h : 16 ≤ ps) : (initEmptyPage ps id fl).length = ps := by
  simp only [initEmptyPage, List.length_append, oi_pb_len, List.length_replicate]
  omega

theorem oi_len (ps : Nat) (h : 80 ≤ ps) : (initBytes ps).length = 4 * ps := by
  simp only [initBytes, List.length_append, oi_mp_len _ _ h, oi_ep_len _ _ _ (by omega : 16 ≤ ps)]
  omega

theorem oi_slot_pre (A B : List w8) (ps s : Nat) (h : (s + 1) * ps ≤ A.length) :
    slotAt (A ++ B) ps s = slotAt A ps s := by
  rw [Nat.succ_mul] at h
  unfold slotAt
  rw [List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp only [List.length_drop]; omega)]

theorem oi_slot_last (A B : List w8) (ps s : Nat) (h : A.length = s * ps) (hB : B.length = ps) :
    slotAt (A ++ B) ps s = B := by
  unfold slotAt
  rw [← h, List.drop_left, List.take_of_length_le (by omega)]

theorem oi_slot_zero (B : List w8) (ps : Nat) (hB : B.length = ps) : slotAt B ps 0 = B := by
  unfold slotAt
  rw [Nat.zero_mul, List.drop_zero, List.take_of_length_le (by omega)]

theorem oi_slots (ps : Nat) (h : 80 ≤ ps) :
    slotAt (initBytes ps) ps 0 = initMetaPage ps 0 ∧ slotAt (initBytes ps) ps 1 = initMetaPage ps 1 ∧
    slotAt (initBytes ps) ps 2 = initEmptyPage ps 2 (W16 16) ∧
    slotAt (initBytes ps) ps 3 = initEmptyPage ps 3 (W16 2) := by
  have l0 := oi_mp_len ps 0 h
  have l1 := oi_mp_len ps 1 h
  have l2 := oi_ep_len ps 2 (W16 16) (by omega)
  have l3 := oi_ep_len ps 3 (W16 2) (by omega)
  unfold initBytes
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [oi_slot_pre _ _ _ _ (by simp only [List.length_append]; omega),
      oi_slot_pre _ _ _ _ (by simp only [List.length_append]; omega),
      oi_slot_pre _ _ _ _ (by omega), oi_slot_zero _ _ l0]
  · rw [oi_slot_pre _ _ _ _ (by simp only [List.length_append]; omega),
      oi_slot_pre _ _ _ _ (by simp only [List.length_append]; omega),
      oi_slot_last _ _ _ _ (by omega) l1]
  · rw [oi_slot_pre _ _ _ _ (by simp only [List.length_append]; omega),
      oi_slot_last _ _ _ _ (by simp only [List.length_append]; omega) l2]
  · rw [oi_slot_last _ _ _ _ (by simp only [List.length_append]; omega) l3]

/-- The header fields of a page whose bytes start with a page header. -/
theorem oi_hdr (p : Page) (T : List w8) (k w : Nat) (h : k + w ≤ 16) :
    leAt (pageBytes p ++ T) k w = leAt (pageBytes p) k w :=
  leAt_app_left _ _ _ _ (by rw [oi_pb_len]; exact h)

theorem oi_mp_hdr (ps i : Nat) (k w : Nat) (h : k + w ≤ 16) :
    leAt (initMetaPage ps i) k w =
      leAt (pageBytes (Page.mk (W64 (i : Int)) (W16 4) (W16 0) (W32 0))) k w := by
  unfold initMetaPage
  rw [List.append_assoc, oi_hdr _ _ _ _ h]

theorem oi_ep_hdr (ps id : Nat) (fl : w16) (k w : Nat) (h : k + w ≤ 16) :
    leAt (initEmptyPage ps id fl) k w =
      leAt (pageBytes (Page.mk (W64 (id : Int)) fl (W16 0) (W32 0))) k w := by
  unfold initEmptyPage
  rw [oi_hdr _ _ _ _ h]

theorem oi_pb_id (p : Page) : leAt (pageBytes p) 0 8 = p.id'.toNat := by
  have := leAt_leBytes_app [] (leBytes 2 p.flags'.toNat ++ leBytes 2 p.count'.toNat ++
    leBytes 4 p.overflow'.toNat) 8 p.id'.toNat (by have := p.id'.isLt; simpa using this)
  unfold pageBytes
  simp only [List.append_assoc, List.nil_append, List.length_nil] at this ⊢
  exact this

theorem oi_pb_flags (p : Page) : leAt (pageBytes p) 8 2 = p.flags'.toNat := by
  have := leAt_leBytes_app (leBytes 8 p.id'.toNat) (leBytes 2 p.count'.toNat ++
    leBytes 4 p.overflow'.toNat) 2 p.flags'.toNat (by have := p.flags'.isLt; simpa using this)
  unfold pageBytes
  simp only [List.append_assoc, leBytes_length'] at this ⊢
  exact this

theorem oi_pb_count (p : Page) : leAt (pageBytes p) 10 2 = p.count'.toNat := by
  have := leAt_leBytes_app (leBytes 8 p.id'.toNat ++ leBytes 2 p.flags'.toNat)
    (leBytes 4 p.overflow'.toNat) 2 p.count'.toNat (by have := p.count'.isLt; simpa using this)
  unfold pageBytes
  simp only [List.append_assoc, List.length_append, leBytes_length'] at this ⊢
  exact this

theorem oi_pb_ov (p : Page) : leAt (pageBytes p) 12 4 = p.overflow'.toNat := by
  have := leAt_leBytes_app (leBytes 8 p.id'.toNat ++ leBytes 2 p.flags'.toNat ++
    leBytes 2 p.count'.toNat) [] 4 p.overflow'.toNat (by have := p.overflow'.isLt; simpa using this)
  unfold pageBytes
  simp only [List.append_assoc, List.length_append, leBytes_length', List.append_nil] at this ⊢
  exact this

theorem oi_ov_mp (ps i : Nat) : pageOverflow (initMetaPage ps i) = 0 := by
  unfold pageOverflow; rw [oi_mp_hdr _ _ _ _ (by omega), oi_pb_ov]; rfl

theorem oi_ov_ep (ps id : Nat) (fl : w16) : pageOverflow (initEmptyPage ps id fl) = 0 := by
  unfold pageOverflow; rw [oi_ep_hdr _ _ _ _ _ (by omega), oi_pb_ov]; rfl

theorem oi_ep2_hdr (ps : Nat) :
    pageFlags (initEmptyPage ps 2 (W16 16)) = freelistPageFlag ∧
      pageCount (initEmptyPage ps 2 (W16 16)) = 0 := by
  unfold pageFlags pageCount
  rw [oi_ep_hdr _ _ _ _ _ (by omega), oi_ep_hdr _ _ _ _ _ (by omega), oi_pb_flags, oi_pb_count]
  exact ⟨rfl, rfl⟩

theorem oi_ep3_hdr (ps : Nat) :
    pageId (initEmptyPage ps 3 (W16 2)) = 3 ∧ pageFlags (initEmptyPage ps 3 (W16 2)) = leafPageFlag ∧
      pageCount (initEmptyPage ps 3 (W16 2)) = 0 := by
  unfold pageId pageFlags pageCount
  rw [oi_ep_hdr _ _ _ _ _ (by omega), oi_ep_hdr _ _ _ _ _ (by omega),
    oi_ep_hdr _ _ _ _ _ (by omega), oi_pb_id, oi_pb_flags, oi_pb_count]
  exact ⟨rfl, rfl, rfl⟩

/-- Page `id < 4` of a fresh database: its slot. -/
theorem oi_pageAt (ps id : Nat) (h : 80 ≤ ps) (hid : id < 4) :
    pageSpan (initBytes ps) ps id = 1 ∧ pageAt (initBytes ps) ps id = slotAt (initBytes ps) ps id := by
  obtain ⟨s0, s1, s2, s3⟩ := oi_slots ps h
  have hov : pageOverflow (slotAt (initBytes ps) ps id) = 0 := by
    rcases (by omega : id = 0 ∨ id = 1 ∨ id = 2 ∨ id = 3) with rfl | rfl | rfl | rfl
    · rw [s0]; exact oi_ov_mp ps 0
    · rw [s1]; exact oi_ov_mp ps 1
    · rw [s2]; exact oi_ov_ep ps 2 _
    · rw [s3]; exact oi_ov_ep ps 3 _
  have hsp : pageSpan (initBytes ps) ps id = 1 := by unfold pageSpan; rw [hov]
  refine ⟨hsp, ?_⟩
  unfold pageAt slotAt; rw [hsp, Nat.one_mul]

theorem oi_meta_bytes (ps i : Nat) (h : 80 ≤ ps) :
    ((initMetaPage ps i).drop 16).take 64 = metaBytes (initMeta ps i) := by
  unfold initMetaPage
  rw [List.append_assoc, List.drop_append_of_le_length (by rw [oi_pb_len]; omega),
    List.drop_of_length_le (by rw [oi_pb_len]; omega), List.nil_append,
    List.take_append_of_le_length (by rw [oi_mb_len]; omega),
    List.take_of_length_le (by rw [oi_mb_len]; omega)]

theorem oi_take56 (m : Meta) (c : w64) :
    (metaBytes { m with checksum' := c }).take 56 = (metaBytes m).take 56 := rfl

theorem oi_valid (ps i : Nat) : metaValid (initMeta ps i) := by
  refine ⟨rfl, rfl, ?_⟩
  exact congrArg fnv64a (oi_take56 (initMeta0 ps i) _).symm

theorem oi_pick (ps : Nat) : metaPick (initMeta ps 0) (initMeta ps 1) = true := by
  unfold metaPick
  have h : uint.Z (initMeta ps 0).txid' < uint.Z (initMeta ps 1).txid' := by
    show uint.Z (W64 ((0 : Nat) : Int)) < uint.Z (W64 ((1 : Nat) : Int)); decide
  rw [if_pos h, if_pos (oi_valid ps 1)]

open Classical in
/-- The tree of a fresh database: the empty leaf on page 3. -/
theorem oi_tree (ps : Nat) (h : 80 ≤ ps) (id : Nat) (pg : List w8) :
    treePages (filePages (initBytes ps) ps 4) 3 !! id = some pg ↔
      id = 3 ∧ pg = initEmptyPage ps 3 (W16 2) := by
  obtain ⟨-, -, -, s3⟩ := oi_slots ps h
  obtain ⟨-, -, hc3⟩ := oi_ep3_hdr ps
  have hp3 : filePages (initBytes ps) ps 4 !! 3 = some (initEmptyPage ps 3 (W16 2)) := by
    rw [filePages_lookup, if_pos (by omega), (oi_pageAt ps 3 h (by omega)).2, s3]
  have hth : ∀ d, treeHas (filePages (initBytes ps) ps 4) 3 d → d = 3 := by
    intro d hd
    cases hd with
    | root _ _ _ => rfl
    | sub _ pg' _ hpg hph =>
      rw [hp3] at hpg
      cases hpg
      cases hph with
      | child _ i _ _ hi _ => rw [hc3] at hi; omega
      | bucket _ i _ _ hi _ _ => rw [hc3] at hi; omega
  unfold treePages
  rw [GMap.mapLookup_filter_Some]
  constructor
  · rintro ⟨hl, hd⟩
    have := hth id (of_decide_eq_true hd)
    subst this
    rw [hp3] at hl
    exact ⟨rfl, (Option.some.inj hl).symm⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨hp3, decide_eq_true (treeHas.root 3 _ hp3)⟩

theorem oi_flno (ps : Nat) : ¬ fpOverflow (pageOf (initEmptyPage ps 2 (W16 16))) := by
  have hc := (oi_ep2_hdr ps).2
  show ¬ (W16 ((pageCount (initEmptyPage ps 2 (W16 16)) : Nat) : Int) = W16 65535)
  rw [hc]; decide

theorem oi_flN (ps : Nat) : flN (initEmptyPage ps 2 (W16 16)) = 0 := by
  have hc := (oi_ep2_hdr ps).2
  unfold flN fpCount
  rw [if_neg (oi_flno ps)]
  show uint.nat (W64 (uint.Z (W16 ((pageCount (initEmptyPage ps 2 (W16 16)) : Nat) : Int)))) = 0
  rw [hc]; decide

theorem oi_flIds (ps : Nat) : flIds (initEmptyPage ps 2 (W16 16)) = [] := by
  unfold flIds; rw [oi_flN]; rfl

theorem oi_flOff (ps : Nat) : flOff (initEmptyPage ps 2 (W16 16)) = 16 := by
  unfold flOff fpIdx
  rw [if_neg (oi_flno ps)]
  decide

/-- A fresh database's file is well-formed. -/
theorem fileWF_initBytes (ps : Nat) (h80 : 80 ≤ ps) (h32 : ps < 2 ^ 32) :
    fileWF (initBytes ps) ps := by
  have hlen := oi_len ps h80
  obtain ⟨s0, s1, s2, s3⟩ := oi_slots ps h80
  refine ⟨h80, h32, by omega, by omega, ?_⟩
  intro v0 v1 hm0 hm1 _
  rw [s0, oi_meta_bytes _ _ h80] at hm0
  rw [s1, oi_meta_bytes _ _ h80] at hm1
  obtain rfl := metaBytes_inj _ _ hm0.symm
  obtain rfl := metaBytes_inj _ _ hm1.symm
  rw [oi_pick, if_pos rfl]
  have hnps : (initBytes ps).length / ps = 4 := by
    rw [hlen, Nat.mul_div_cancel _ (by omega)]
  have hpg : uint.nat (initMeta ps 1).pgid' = 4 := by
    show uint.nat (W64 4) = 4; decide
  have hrt : uint.nat (initMeta ps 1).root'.root' = 3 := by
    show uint.nat (W64 3) = 3; decide
  have hfl : uint.nat (initMeta ps 1).freelist' = 2 := by
    show uint.nat (W64 2) = 2; decide
  obtain ⟨sp2, pa2⟩ := oi_pageAt ps 2 h80 (by omega)
  obtain ⟨sp3, -⟩ := oi_pageAt ps 3 h80 (by omega)
  have hfpg : pageAt (initBytes ps) ps 2 = initEmptyPage ps 2 (W16 16) := by rw [pa2, s2]
  obtain ⟨hid3, hfl3, hc3⟩ := oi_ep3_hdr ps
  obtain ⟨hfl2, -⟩ := oi_ep2_hdr ps
  have hl3 := oi_ep_len ps 3 (W16 2) (by omega)
  have hl2 := oi_ep_len ps 2 (W16 16) (by omega)
  have ht := oi_tree ps h80
  unfold fileCurOK
  have hids : flIds (pageAt (initBytes ps) ps 2) = [] := by rw [hfpg, oi_flIds]
  have hoff : flOff (pageAt (initBytes ps) ps 2) = 16 := by rw [hfpg, oi_flOff]
  have hn : flN (pageAt (initBytes ps) ps 2) = 0 := by rw [hfpg, oi_flN]
  rw [← hfpg] at hfl2 hl2
  simp only [hpg, hrt, hfl, hids, hoff, hn]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, by omega, ?_, ?_, ?_, ?_⟩
  · -- the tree: the empty leaf
    refine treeWF.page 3 (initEmptyPage ps 3 (W16 2)) (by omega) ((ht _ _).2 ⟨rfl, rfl⟩) hid3 ?_
    refine pageTreeWF.leaf _ _ hfl3 ⟨Nat.le_refl _, ?_, ?_, ?_⟩ ?_
    · rw [hc3, hl3]; unfold elemOff; omega
    · intro i hi; rw [hc3] at hi; omega
    · intro i j _ hj; rw [hc3] at hj; omega
    · intro i hi; rw [hc3] at hi; omega
  · refine ⟨?_, ?_⟩
    · intro id pg hid
      obtain ⟨rfl, rfl⟩ := (ht _ _).1 hid
      refine ⟨fun _ i hi => by rw [hc3] at hi; omega, fun hb => ?_⟩
      rw [hfl3] at hb; cases hb
    · refine ⟨fun id pg hid hb => ?_, fun id pg hid _ => ?_⟩
      · obtain ⟨rfl, rfl⟩ := (ht _ _).1 hid
        rw [hfl3] at hb; cases hb
      · obtain ⟨rfl, rfl⟩ := (ht _ _).1 hid
        exact ⟨fun i _ hi => by rw [hc3] at hi; omega, fun i hi => by rw [hc3] at hi; omega⟩
  · exact treeKeys.leaf 3 _ none none ((ht _ _).2 ⟨rfl, rfl⟩) hfl3
      (fun i hi => by rw [hc3] at hi; omega) (fun i hi => by rw [hc3] at hi; omega)
  · intro id1 pg1 id2 pg2 h1 h2 hne
    obtain ⟨rfl, -⟩ := (ht _ _).1 h1
    obtain ⟨rfl, -⟩ := (ht _ _).1 h2
    exact absurd rfl hne
  · intro id pg hid
    obtain ⟨rfl, rfl⟩ := (ht _ _).1 hid
    rw [sp3, hnps]; omega
  · rintro s ⟨id, pg, hid, h1, h2⟩
    obtain ⟨rfl, rfl⟩ := (ht _ _).1 hid
    exact ⟨by omega, by simp⟩
  · show W64 2 ≠ W64 18446744073709551615; decide
  · rw [sp2, hnps]; omega
  · refine ⟨hfl2, ?_, ?_, by rw [hids]; exact List.nodup_nil, fun x hx => by rw [hids] at hx; simp at hx⟩
    · rw [hoff, hn, hl2]; omega
    · rw [hl2]; omega
  · intro x hx; simp at hx
  · show uint.Z (W64 ((1 : Nat) : Int)) + 1 < 2 ^ 64; decide

end pure

end bbolt
end EtcdGrove
end Perennial
