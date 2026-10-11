module
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Sum64
public import Proof.go_etcd_io.bbolt.internal.common.Bytes
public import Spec.hash.fnv.New64a
public import Spec.hash.fnv.sum64a__Write
public import Spec.hash.fnv.sum64a__Sum64

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.common

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]
-- `hash.Hash64`'s type (its underlying interface): `internal/common` reaches `hash` only
-- through `hash/fnv`, so its `Assumptions` do not include `hash`'s
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

theorem Meta.Sum64.wp_proof (hNew : fnv.New64a.spec (GF := GF) (hG := hG))
    (hWrite : fnv.sum64a.Write.spec (GF := GF) (hG := hG))
    (hSum : fnv.sum64a.Sum64.spec (GF := GF) (hG := hG)) :
    Meta.Sum64.spec (GF := GF) (hG := hG) := by
  intro l v dq Hc
  wp_start as Hl
  wp_auto
  wp_apply hNew as %t %hv Hh
  try wp_auto
  rw [show sint.Z (W64 0) = 0 by rfl, arrayIndexRef_zero, show W64 56 - W64 0 = W64 56 by rfl]
  have Hlen : (metaBytes v).length = 64 := metaBytes_length v
  icases (Meta_bytes (hG := hG) l v dq Hc).1 $$ Hl with Hb
  icases (bytesPointsto_take_drop l dq (metaBytes v) 56 (by omega)).1 $$ Hb with ⟨Hb1, Hb2⟩
  ihave Hs := (ownSlice_bytes (slice.mk l (W64 56) (W64 56)) ((metaBytes v).take 56) dq
      (List.ne_nil_of_length_pos (by rw [List.length_take, Hlen]; decide))).2 $$ [Hb1]
  · iframe; ipureintro; simp only [List.length_take]; constructor <;> word
  wp_apply hWrite t hv [] (slice.mk l (W64 56) (W64 56)) ((metaBytes v).take 56) dq $$ [Hh Hs]
    as ⟨Hh, Hs⟩
  · iframe
  try wp_auto
  wp_apply hSum $$ [Hh] as Hh
  · iexact Hh
  icases (ownSlice_bytes (slice.mk l (W64 56) (W64 56)) ((metaBytes v).take 56) dq
      (List.ne_nil_of_length_pos (by rw [List.length_take, Hlen]; decide))).1 $$ Hs with ⟨Hb1, -⟩
  ihave Hb := (bytesPointsto_take_drop l dq (metaBytes v) 56 (by omega)).2 $$ [Hb1 Hb2]
  · iframe
  ihave Hl := (Meta_bytes (hG := hG) l v dq Hc).2 $$ Hb
  simp only [List.nil_append]
  iapply HΦ $$ Hl

end proof

end bbolt
end EtcdGrove
end Perennial
