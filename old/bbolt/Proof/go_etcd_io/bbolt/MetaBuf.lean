/-
A meta read from a byte buffer (`getPageSize`, `init`): the 64 bytes at an offset are the meta
`metaOf` of them (`meta_in_bytes`), lent out of the bytes and given back.
-/
module

public import Proof.go_etcd_io.bbolt.PageView

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.common

section metabuf
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- The 64 bytes at `off` of `bs`, read as a meta. -/
def metaAt (bs : List w8) (off : Nat) : Meta := metaOf ((bs.drop off).take 64)

theorem metaBytes_metaAt (bs : List w8) (off : Nat) (h : off + 64 ≤ bs.length) :
    metaBytes (metaAt bs off) = (bs.drop off).take 64 := by
  unfold metaAt
  rw [metaBytes_metaOf _ (by simp only [List.length_take, List.length_drop]; omega),
    List.take_take, Nat.min_self]

/-- The meta at `off` of a byte region, lent out of it. -/
theorem meta_in_bytes (l : Loc) (dq : DFrac) (bs : List w8) (off : Nat)
    (h : off + 64 ≤ bs.length) (hl : l.locCar ≠ 0) :
    bytesPointsto (GF := GF) l dq bs ⊢
      (l +ₗ (off : Int)) ↦{dq} metaAt bs off ∗
      ((l +ₗ (off : Int)) ↦{dq} metaAt bs off -∗ bytesPointsto l dq bs) := by
  have hl' : (l +ₗ (off : Int)).locCar ≠ 0 := by simpa [Loc.add] using hl
  have H1 := bytesPointsto_take_drop (GF := GF) l dq bs off (by omega)
  have H2 := bytesPointsto_take_drop (GF := GF) (l +ₗ (off : Int)) dq (bs.drop off) 64
    (by simp only [List.length_drop]; omega)
  have H3 := Meta_bytes (GF := GF) (hG := hG) (l +ₗ (off : Int)) (metaAt bs off) dq hl'
  rw [metaBytes_metaAt bs off h] at H3
  iintro Hb
  icases H1.1 $$ Hb with ⟨Ha, Hb⟩
  icases H2.1 $$ Hb with ⟨Hm, Hc⟩
  ihave Hm := H3.2 $$ Hm
  iframe Hm
  iintro Hm
  ihave Hm := H3.1 $$ Hm
  iapply H1.2
  iframe Ha
  iapply H2.2
  iframe

end metabuf

end bbolt
end EtcdGrove
end Perennial
