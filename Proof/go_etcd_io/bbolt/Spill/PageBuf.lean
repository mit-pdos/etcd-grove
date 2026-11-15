/-
The spill's page buffers (U9d, `notes/bbolt-proof-plan.md`): an allocated page's buffer (`tx.pages`,
`WX.addPage`'s bytes: a zeroed header with the id and the overflow, then zeros) as `node.write`'s
pre needs it (the header's typed points-to, the zeros after it), and the buffer it leaves
(`Spill/WrittenPage`'s `wPage`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.WrittenPage
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout
public import Proof.go_etcd_io.bbolt.Model.WOps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt


namespace Spill

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- The header `node.write` leaves of an allocated page's zeroed header. -/
theorem hdrWritten_alloc (id : w64) (ovf : w32) (leaf : Bool) (n : Nat) :
    hdrWritten (⟨id, W16 0, W16 0, ovf⟩ : Page) leaf n = mkPageHdr id leaf n ovf := by
  unfold hdrWritten mkPageHdr
  cases leaf <;> rfl

/-- **The buffer after `node.write`** of the inodes `ms` into an allocated page of `count` slots
(its body within the buffer): a written page (`wPage`). -/
theorem allocBuf_written (id : w64) (leaf : Bool) (ms : List InodeM) (count : Nat) :
    encode (hdrWritten (⟨id, W16 0, W16 0, W32 ((count - 1 : Nat) : Int)⟩ : Page) leaf ms.length) ++
      (pageBody leaf ms ++ List.replicate (count * 4096 - 16 - (pageBody leaf ms).length) (W8 0)) =
    wPage id leaf ms (W32 ((count - 1 : Nat) : Int))
      (List.replicate (count * 4096 - 16 - (pageBody leaf ms).length) (W8 0)) := by
  rw [hdrWritten_alloc]; rfl

/-- A written page in an allocated buffer has the buffer's length. -/
theorem allocBuf_written_length (id : w64) (leaf : Bool) (ms : List InodeM) (count : Nat)
    (hfit : 16 + (pageBody true ms).length ≤ count * 4096) :
    (wPage id leaf ms (W32 ((count - 1 : Nat) : Int))
      (List.replicate (count * 4096 - 16 - (pageBody leaf ms).length) (W8 0))).length =
      count * 4096 := by
  rw [wPage_length]
  have : (pageBody leaf ms).length = (pageBody true ms).length := by simp [pageBody_length]
  simp only [List.length_replicate, this]
  omega

/-- A node's entries as the inodes `node.write` lays out. -/
def wsMs (ws : List WEntry) : List InodeM := ws.map fun w => ⟨w.flags, w.pgid, w.key, w.value⟩

theorem wsMs_length (ws : List WEntry) : (wsMs ws).length = ws.length := by simp [wsMs]

/-- Sorted entries lay out sorted inodes. -/
theorem wsMs_sorted {ws : List WEntry} (h : wsSorted ws) : msSorted (wsMs ws) := by
  intro i j hij hj
  have hj' : j < ws.length := by rw [wsMs_length] at hj; exact hj
  have := h i j hij hj'
  unfold wKey at this
  simp only [wsMs, List.getElem_map]
  rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem hj'] at this
  exact this

end pure

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- **A page buffer as a header and its body**: the header's typed points-to and the bytes
after it. -/
theorem pageBuf_split (p : Loc) (dq : DFrac) (h : Page) (rest : List w8) (hp : 0 < p.addr) :
    bytesPointsto (GF := GF) p dq (encode h ++ rest) ⊣⊢
      typedPointsto p h dq ∗ bytesPointsto (p +ₗ 16) dq rest := by
  have e := bytesPointsto_app (GF := GF) p dq (encode h) rest
  rw [ByteEncoding.encode_length] at e
  have t := typedPointsto_bytes (GF := GF) p h dq hp
  constructor
  · iintro H
    icases e.1 $$ H with ⟨H1, H2⟩
    iframe H2
    iapply t.2; iexact H1
  · iintro ⟨H1, H2⟩
    iapply e.2
    iframe H2
    iapply t.1; iexact H1

end heap

end Spill

end bbolt
end EtcdGrove
end Perennial
