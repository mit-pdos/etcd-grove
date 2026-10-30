/-
The page `db.allocate` returns: a zeroed buffer (the page pool's, or a new one) whose header
is read as a `Page` (`zero_page`), its overflow and id set, and the bytes again
(`fresh_page`): `freshPage`.
-/
module

public import Proof.go_etcd_io.bbolt.WriteTxDeref
public import Proof.go_etcd_io.bbolt.PageView

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.common

section page
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

theorem pageBytes_zero : pageBytes (Page.mk (W64 0) (W16 0) (W16 0) (W32 0)) =
    List.replicate 16 (W8 0) := by
  first | rfl | (simp [pageBytes, leBytes]; done) | (unfold pageBytes leBytes; simp; done)

theorem leBytes_zero_4 : leBytes 4 0 = leBytes 2 0 ++ leBytes 2 0 := by decide

/-- A zeroed buffer of at least a header is a zero header and zeroes. -/
theorem zero_page (l : Loc) (n : Nat) (hl : l.locCar ≠ 0) (hn : 16 ≤ n) :
    bytesPointsto (GF := GF) l (DFrac.own 1) (List.replicate n (W8 0)) ⊣⊢
      l ↦ Page.mk (W64 0) (W16 0) (W16 0) (W32 0) ∗
        bytesPointsto (l +ₗ 16) (DFrac.own 1) (List.replicate (n - 16) (W8 0)) := by
  rw [show n = 16 + (n - 16) by omega, ← List.replicate_append_replicate]
  refine (bytesPointsto_app _ _ _ _).trans ?_
  rw [List.length_replicate, show 16 + (n - 16) - 16 = n - 16 by omega]
  refine sep_congr ?_ .rfl
  rw [← pageBytes_zero]
  exact (Page_bytes (hG := hG) l _ _ hl).symm

/-- The header with its id and overflow set, and the zeroes after it: the fresh page. -/
theorem fresh_page (l : Loc) (id : w64) (count ps : Nat) (hl : l.locCar ≠ 0)
    (hc : 0 < count) (hc32 : count ≤ 2 ^ 32) (hps : 16 ≤ count * ps) :
    l ↦ Page.mk id (W16 0) (W16 0) (W32 ((count - 1 : Nat) : Int)) ∗
      bytesPointsto (l +ₗ 16) (DFrac.own 1) (List.replicate (count * ps - 16) (W8 0)) ⊢
    bytesPointsto (GF := GF) l (DFrac.own 1) (freshPage id count ps) := by
  have hov : (W32 ((count - 1 : Nat) : Int)).toNat = count - 1 := by
    simp; omega
  have hb : pageBytes (Page.mk id (W16 0) (W16 0) (W32 ((count - 1 : Nat) : Int))) =
      leBytes 8 (uint.Z id) ++ leBytes 4 0 ++ leBytes 4 (((count - 1 : Nat) : Int)) := by
    unfold pageBytes
    simp only
    rw [hov, leBytes_zero_4]
    simp [List.append_assoc]
  have hlen : (pageBytes (Page.mk id (W16 0) (W16 0) (W32 ((count - 1 : Nat) : Int)))).length =
      16 := by
    simp [pageBytes, leBytes_length]
  iintro ⟨Hh, Hz⟩
  ihave Hh := (Page_bytes (hG := hG) l _ _ hl).1 $$ Hh
  unfold freshPage
  rw [← hb]
  iapply (bytesPointsto_app _ _ _ _).2
  rw [hlen]
  iframe

end page

end bbolt
end EtcdGrove
end Perennial
