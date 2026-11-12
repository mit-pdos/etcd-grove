/-
The proof of `Spec/go_etcd_io/bbolt/Cursor__seek_r.lean` (U6, `notes/bbolt-proof-plan.md`): the
stack emptied (`c.stack[:0]`), `search` from the bucket's root page, then `keyValue` at the route's
leaf (`rRoute_last`).
-/
module

public import Spec.go_etcd_io.bbolt.Cursor__seek_r
public import Proof.go_etcd_io.bbolt.Read.Root
public import Proof.go_etcd_io.bbolt.Read.Route

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

theorem Cursor.seek_r.wp_proof
    (hs : Cursor.search_r.spec (GF := GF) (hG := hG))
    (hkv : Cursor.keyValue_r.spec (GF := GF) (hG := hG))
    (hRP : internal.common.InBucket.RootPage.spec (GF := GF) (hG := hG)) :
    Cursor.seek_r.spec (GF := GF) (hG := hG) := by
  intro K tx src q T v b dq bv ibp pp c stk els key kr kb hbv htree
  wp_start as ⟨Hk, Hb, Hc, Hs, Hcap, Hkey⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  ihave %Hcw := ownSliceCap_wf _ _ $$ Hcap
  wp_auto
  rw [if_pos ⟨by decide, by decide, by word⟩]
  icases ownSlice_slice_with_cap (V := elemRef) (W64 0) (W64 0) stk els ⟨by decide, by decide, by word⟩
    $$ [Hs Hcap] with ⟨-, Hs, Hcap⟩
  · iframe
  have hsub : subslice (sint.nat (W64 0)) (sint.nat (W64 0)) els = ([] : List elemRef) := by
    simp [subslice]
  rw [hsub]
  wp_auto
  wp_method_call; wp_call
  unfold rBktP
  icases Hb with ⟨HIB, Htx, Hbks, Hpage, Hroot, Hnodes, Hhdr, Hil⟩
  wp_auto
  wp_apply wp_rd_rootPage hRP K tx src q T v bv ibp hbv $$ [Hk Hhdr] as ⟨Hk, Hhdr⟩
  · iframe
  rw [show (decode (List.take 8 (bytesAt bv 0 16)) : w64) = (inBucketOf bv).root' from rfl,
    show ({ bucket' := b, stack' := stk } : Cursor).bucket' = b from rfl]
  wp_apply hs K tx src q T v b dq bv ibp pp c _ [] (inBucketOf bv).root' key kr kb hbv htree
    $$ [Hk HIB Htx Hbks Hpage Hroot Hnodes Hhdr Hil Hc Hs Hcap Hkey]
    as ⟨%stk', %path, Hk, Hb, Hc, Hs, Hcap, Hkey, %Hrt⟩
  · iframe; unfold rBktP; iframe
  have hroot : (inBucketOf bv).root'.toNat = inBucketRoot bv := rfl
  rw [hroot] at Hrt
  obtain ⟨els', e, pid', pg, hpe, hpa, hnode, hfl, hwf, h16, hidx⟩ :=
    rRoute_last v bv pp kb path _ htree Hrt
  subst hpe
  wp_apply hkv K tx src q T v b dq bv ibp pp c stk' els' e pid' pg hpa hnode hfl hwf h16
    (by rw [hidx]; have := pageSeekIdx_le pg kb; word)
    $$ [Hk Hb Hc Hs] as %k %vl %fl ⟨Hk, Hb, Hc, Hs, Hkv⟩
  · iframe
  try wp_auto
  iapply HΦ
  iexists stk', els', e, pid', pg
  have hsi : (sint.Z e.index').toNat = pageSeekIdx pg kb := by
    rw [hidx]; have := pageSeekIdx_le pg kb; word
  rw [hsi]
  unfold rBktP
  iframe
  ipureintro
  exact ⟨Hrt, hpa, hfl, hidx⟩

end proof

end bbolt
end EtcdGrove
end Perennial
