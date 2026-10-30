module
public import Spec.go_etcd_io.bbolt.Cursor__keyValue_w
public import Spec.go_etcd_io.bbolt.elemRef__count_w
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Key
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Value
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Flags
public import Spec.go_etcd_io.bbolt.internal.common.Page__LeafPageElement
public import Spec.go_etcd_io.bbolt.internal.common.leafPageElement__Key
public import Spec.go_etcd_io.bbolt.internal.common.leafPageElement__Value
public import Spec.go_etcd_io.bbolt.internal.common.leafPageElement__Flags

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem Cursor.keyValue.wp_wproof (hcount : elemRef.count.wspec (GF := GF) (hG := hG))
    (hLPE : Page.LeafPageElement.spec (GF := GF) (hG := hG))
    (hKey : leafPageElement.Key.spec (GF := GF) (hG := hG))
    (hValue : leafPageElement.Value.spec (GF := GF) (hG := hG))
    (hFlags : leafPageElement.Flags.spec (GF := GF) (hG := hG))
    (hIKey : Inode.Key.spec (GF := GF) (hG := hG))
    (hIValue : Inode.Value.spec (GF := GF) (hG := hG))
    (hIFlags : Inode.Flags.spec (GF := GF) (hG := hG)) :
    Cursor.keyValue.wspec (GF := GF) (hG := hG) := by
  intro cl cv dqc es dqs rv q pg nv dqn ins dqi Hlast Hpage Hnodei
  by_cases Hnode : rv.node' = null
  · obtain ⟨Hc, Hlen, Hleaf, Hwf, Hidx⟩ := Hpage Hnode
    simp only [Hnode, ↓reduceIte, kvResW]
    wp_start as ⟨Hcl, Hs, Hpg⟩
    ihave %Hsl := ownSlice_len _ _ _ $$ Hs
    have Hne : es ≠ [] := by intro h; subst h; simp at Hlast
    have Hli : es[es.length - 1]? = some rv := by
      rw [List.getLast?_eq_getElem?] at Hlast; exact Hlast
    have Hpos : 0 < es.length := List.length_pos_iff.2 Hne
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (cv.stack'.len - W64 1) ∧
      sint.Z (cv.stack'.len - W64 1) < sint.Z cv.stack'.len from ⟨by word, by word⟩))]
    have Hix : (sint.Z (cv.stack'.len - W64 1)).toNat = es.length - 1 := by word
    icases ownSlice_elem_acc (sint.Z (cv.stack'.len - W64 1)) rv _ dqs es (by word)
      (by rw [Hix]; exact Hli) $$ Hs with ⟨Hr, Hsback⟩
    try wp_auto
    have Hset : es.set (sint.Z (cv.stack'.len - W64 1)).toNat rv = es := by
      have hlt : es.length - 1 < es.length := by omega
      have hget : es[es.length - 1] = rv := by
        rw [List.getElem?_eq_getElem hlt] at Hli; exact Option.some.inj Hli
      rw [Hix, ← hget]; exact List.set_getElem_self hlt
    have Hcnt : pageCount pg < 65536 := by have := leAt_lt pg 10 2; unfold pageCount; omega
    wp_apply hcount _ rv _ (zero_val node) (DFrac.own 1) q pg (fun _ => ⟨Hc, Hlen⟩) $$ [Hr Hpg] as ⟨Hr, Hpg⟩
    · simp only [Hnode, ↓reduceIte]; iframe
    try simp only [Hnode, ↓reduceIte]
    try wp_auto
    wp_if_destruct
    · -- an empty page
      have H0 : pageCount pg = 0 := by
        have := congrArg BitVec.toNat Hif; simp at this; omega
      have Hkv : kvResult rv.page' pg (sint.Z rv.index') = (slice.nil, slice.nil, W32 0) := by
        unfold kvResult; simp [H0]
      rw [Hkv]
      try wp_auto
      ispecialize Hsback $$ %rv Hr
      rw [Hset]
      try simp only
      iapply HΦ; iframe
    have H0ne : pageCount pg ≠ 0 := by
      intro h; apply Hif; rw [h]; rfl
    wp_apply hcount _ rv _ (zero_val node) (DFrac.own 1) q pg (fun _ => ⟨Hc, Hlen⟩) $$ [Hr Hpg] as ⟨Hr, Hpg⟩
    · simp only [Hnode, ↓reduceIte]; iframe
    try simp only [Hnode, ↓reduceIte]
    try wp_auto
    wp_if_destruct
    · -- past the end
      have Hge : (pageCount pg : Int) ≤ sint.Z rv.index' := by word
      have Hkv : kvResult rv.page' pg (sint.Z rv.index') = (slice.nil, slice.nil, W32 0) := by
        unfold kvResult; simp [Hge]
      rw [Hkv]
      try wp_auto
      ispecialize Hsback $$ %rv Hr
      rw [Hset]
      try simp only
      iapply HΦ; iframe
    have Hi0 : 0 ≤ sint.Z rv.index' := Hidx.resolve_right H0ne
    have Hilt : sint.Z rv.index' < (pageCount pg : Int) := by word
    try wp_auto
    try rw [Hnode]
    try wp_auto
    have Hu : uint.Z (W16 (sint.Z rv.index')) = sint.Z rv.index' := by word
    wp_apply hLPE rv.page' (W16 (sint.Z rv.index'))
    rw [Hu]
    try wp_auto
    obtain ⟨Hle, Helems, Hkvs, -⟩ := Hwf
    have Hit : (sint.Z rv.index').toNat < pageCount pg := by omega
    have Hin : elemOff (sint.Z rv.index').toNat + 16 ≤ pg.length := by
      unfold elemOff at *; omega
    have Hoff : (16 + 16 * sint.Z rv.index' : Int) = ((elemOff (sint.Z rv.index').toNat : Nat) : Int) := by
      unfold elemOff; omega
    rw [Hoff]
    icases (leafElem_in_page (hG := hG) rv.page' q pg _ Hin Hc).1 $$ Hpg with ⟨Hpre, He, Hpost⟩
    obtain ⟨Hk1, Hk2⟩ := Hkvs _ Hit
    have Hec : (rv.page' +ₗ ((elemOff (sint.Z rv.index').toNat : Nat) : Int)).locCar ≠ 0 := by
      simpa [Loc.add] using Hc
    have HpL : leafPos pg (sint.Z rv.index').toNat < 2 ^ 32 := leAt_lt _ _ 4
    have HkL : leafKsize pg (sint.Z rv.index').toNat < 2 ^ 32 := leAt_lt _ _ 4
    have HvL : leafVsize pg (sint.Z rv.index').toNat < 2 ^ 32 := leAt_lt _ _ 4
    have Hpu : uint.Z (W32 ((leafPos pg (sint.Z rv.index').toNat : Nat) : Int)) =
        (leafPos pg (sint.Z rv.index').toNat : Int) := by word
    have Hku : uint.Z (W32 ((leafKsize pg (sint.Z rv.index').toNat : Nat) : Int)) =
        (leafKsize pg (sint.Z rv.index').toNat : Int) := by word
    have Hvu : uint.Z (W32 ((leafVsize pg (sint.Z rv.index').toNat : Nat) : Int)) =
        (leafVsize pg (sint.Z rv.index').toNat : Int) := by word
    have HkOk : uint.Z (leafElemOf pg (sint.Z rv.index').toNat).pos' +
        uint.Z (leafElemOf pg (sint.Z rv.index').toNat).ksize' ≤ 2147483647 := by
      simp only [leafElemOf]; rw [Hpu, Hku]; omega
    have HvOk : uint.Z (leafElemOf pg (sint.Z rv.index').toNat).pos' +
        uint.Z (leafElemOf pg (sint.Z rv.index').toNat).ksize' +
        uint.Z (leafElemOf pg (sint.Z rv.index').toNat).vsize' ≤ 2147483647 := by
      simp only [leafElemOf]; rw [Hpu, Hku, Hvu]; omega
    wp_apply hKey _ (leafElemOf pg _) q Hec HkOk $$ [He] as He
    · iframe
    try wp_auto
    wp_apply hValue _ (leafElemOf pg _) q Hec HvOk $$ [He] as He
    · iframe
    try wp_auto
    wp_apply hFlags _ (leafElemOf pg _) q $$ [He] as He
    · iframe
    try wp_auto
    ispecialize Hsback $$ %rv Hr
    rw [Hset]
    ihave Hpg := (leafElem_in_page (hG := hG) rv.page' q pg _ Hin Hc).2 $$ [$Hpre $He $Hpost]
    simp only [Hnode, ↓reduceIte] at *
    ispecialize HΦ $$ [$Hcl $Hsback $Hpg]
    iExactEq HΦ
    have Hc' : ¬(pageCount pg = 0 ∨ (pageCount pg : Int) ≤ sint.Z rv.index') := by omega
    unfold kvResult
    rw [ite_eq_right_of_eq_false _ _ (eq_false Hc')]
    simp only [Hpu, Hku, Hvu, loc_add_assoc, Int.natCast_add, Int.add_assoc]

  · have Hi0 := Hnodei Hnode
    simp only [Hnode, ↓reduceIte, kvResW]
    wp_start as ⟨Hcl, Hs, Hn, Hins⟩
    ihave %Hsl := ownSlice_len _ _ _ $$ Hs
    have Hne : es ≠ [] := by intro h; subst h; simp at Hlast
    have Hli : es[es.length - 1]? = some rv := by
      rw [List.getLast?_eq_getElem?] at Hlast; exact Hlast
    have Hpos : 0 < es.length := List.length_pos_iff.2 Hne
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (cv.stack'.len - W64 1) ∧
      sint.Z (cv.stack'.len - W64 1) < sint.Z cv.stack'.len from ⟨by word, by word⟩))]
    have Hix : (sint.Z (cv.stack'.len - W64 1)).toNat = es.length - 1 := by word
    icases ownSlice_elem_acc (sint.Z (cv.stack'.len - W64 1)) rv _ dqs es (by word)
      (by rw [Hix]; exact Hli) $$ Hs with ⟨Hr, Hsback⟩
    try wp_auto
    have Hset : es.set (sint.Z (cv.stack'.len - W64 1)).toNat rv = es := by
      have hlt : es.length - 1 < es.length := by omega
      have hget : es[es.length - 1] = rv := by
        rw [List.getElem?_eq_getElem hlt] at Hli; exact Option.some.inj Hli
      rw [Hix, ← hget]; exact List.set_getElem_self hlt
    ihave %Hil := ownSlice_len _ _ _ $$ Hins
    wp_apply hcount _ rv _ nv dqn q pg (fun h => absurd h Hnode) $$ [Hr Hn] as ⟨Hr, Hn⟩
    · try simp only [Hnode, ↓reduceIte]; iframe
    try simp only [Hnode, ↓reduceIte]
    try wp_auto
    wp_if_destruct
    · have H0 : ins.length = 0 := by rw [Hil.1]; word
      have Hkv : nodeKV ins (sint.Z rv.index') = (slice.nil, slice.nil, W32 0) := by
        unfold nodeKV; simp [H0]
      rw [Hkv]
      try wp_auto
      ispecialize Hsback $$ %rv Hr
      rw [Hset]
      try simp only
      iapply HΦ; iframe
    wp_apply hcount _ rv _ nv dqn q pg (fun h => absurd h Hnode) $$ [Hr Hn] as ⟨Hr, Hn⟩
    · try simp only [Hnode, ↓reduceIte]; iframe
    try simp only [Hnode, ↓reduceIte]
    try wp_auto
    wp_if_destruct
    · have Hge : (ins.length : Int) ≤ sint.Z rv.index' := by rw [Hil.1]; word
      have Hkv : nodeKV ins (sint.Z rv.index') = (slice.nil, slice.nil, W32 0) := by
        unfold nodeKV; simp [Hge]
      rw [Hkv]
      try wp_auto
      ispecialize Hsback $$ %rv Hr
      rw [Hset]
      try simp only
      iapply HΦ; iframe
    have Hilt : sint.Z rv.index' < (ins.length : Int) := by rw [Hil.1]; word
    try wp_auto
    rw [decide_eq_false Hnode, Bool.not_false]
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z rv.index' ∧ sint.Z rv.index' < sint.Z nv.inodes'.len
      from ⟨Hi0, by rw [Hil.1] at Hilt; word⟩))]
    obtain ⟨it, Hit⟩ : ∃ it, ins[(sint.Z rv.index').toNat]? = some it :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    icases ownSlice_elem_acc (sint.Z rv.index') it _ dqi ins Hi0 Hit $$ Hins with ⟨Hit', Hiback⟩
    try wp_auto
    wp_apply hIKey $$ [$Hit'] as Hit'
    try wp_auto
    wp_apply hIValue $$ [$Hit'] as Hit'
    try wp_auto
    wp_apply hIFlags $$ [$Hit'] as Hit'
    try wp_auto
    ihave Hins := Hiback $$ Hit'
    rw [list_set_lookup_self _ _ _ Hit]
    ispecialize Hsback $$ %rv Hr
    rw [Hset]
    have Hkv : nodeKV ins (sint.Z rv.index') = (it.key', it.value', it.flags') := by
      unfold nodeKV
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), Hit]
    rw [Hkv]
    try simp only
    iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
