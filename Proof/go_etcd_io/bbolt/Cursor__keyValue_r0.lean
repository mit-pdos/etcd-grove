/-
The proof of `Spec/go_etcd_io/bbolt/Cursor__keyValue_r0.lean` (U6h, `notes/bbolt-proof-plan.md`):
the top element's `count()` is `0`, so `keyValue` returns nil, nil, `0` (`Cursor.keyValue_r`'s
first case, at any index).
-/
module

public import Spec.go_etcd_io.bbolt.Cursor__keyValue_r0
public import Spec.go_etcd_io.bbolt.internal.common.Page__Count

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem Cursor.keyValue_r0.wp_proof
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG)) :
    Cursor.keyValue_r0.spec (GF := GF) (hG := hG) := by
  intro K tx src q T v b dq bv ibp pp c stk els e pid pg hpa hnode h16 hc0
  wp_start as ⟨Hk, Hb, Hc, Hs⟩
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  wp_auto
  have hidx : sint.Z (stk.len - W64 1) = (els.length : Int) := by
    simp only [List.length_append, List.length_singleton] at Hsl; word
  rw [if_pos (by rw [hidx]; word)]
  icases ownSlice_elem_acc (sint.Z (stk.len - W64 1)) e _ _ (els ++ [e]) (by omega)
    (by rw [hidx]; simp) $$ Hs with ⟨He, Hsback⟩
  rw [hidx]
  wp_auto
  wp_method_call; wp_call
  wp_auto
  rw [hnode]
  wp_auto
  icases rd_hdr_acc K tx src q T v b dq bv ibp pp pid e.page' pg hpa h16 $$ [Hk Hb]
    with ⟨%dqh, Hh, Hhb⟩
  · iframe
  obtain ⟨hd, hH⟩ : ∃ hd, pageHdr pg = hd := ⟨_, rfl⟩
  have hcz : uint.Z hd.count' = (pageCount pg : Int) := by unfold pageCount; rw [hH]
  rw [hH]
  wp_apply hCnt e.page' hd dqh $$ [Hh] as Hh
  · iexact Hh
  have : W64 (uint.Z hd.count') = W64 0 := by rw [hcz, hc0]; rfl
  rw [this]
  wp_auto
  ihave Hkb := Hhb $$ Hh
  icases Hkb with ⟨Hk, Hb⟩
  ihave Hs := Hsback $$ He
  rw [show (els ++ [e]).set (↑els.length : Int).toNat e = els ++ [e] by simp]
  iapply HΦ
  iframe

end proof

end bbolt
end EtcdGrove
end Perennial
