/-
minibolt's store (`examples/bboltfs/minibolt.go`) as bytes: what a page holds, read back from the
file's bytes.

`pageHdrOf bs` and `pageMeta bs` are the header and the meta of a page whose bytes start with
`bs` (`decode` of bytes 0..16 and 16..80), and `pageView` views a page's bytes as them
(`pageMeta_view` of `Pages.lean`, for any bytes). `fileMeta xs i` is the meta in page `i` of the
file `xs`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.Pages
public import GooseLang.Ext.OsFs.Write

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.mit_pdos.etcd_grove.examples.bboltfs

section bytes
variable [GooseExts]

/-- The header of a page whose bytes start with `bs`. -/
def pageHdrOf (bs : List w8) : Page := decode (bs.take 16)

/-- The meta of a meta page whose bytes start with `bs`. -/
def pageMeta (bs : List w8) : Meta := decode ((bs.drop 16).take 64)

/-- The meta in page `i` of the file `xs`. -/
def fileMeta (xs : List w8) (i : Nat) : Meta := pageMeta (xs.drop (4096 * i))

theorem page_split (bs : List w8) (h : 80 ≤ bs.length) :
    bs = encode (pageHdrOf bs) ++ encode (pageMeta bs) ++ bs.drop 80 := by
  unfold pageHdrOf pageMeta
  rw [ByteEncoding.encode_decode _ (by simp; omega), ByteEncoding.encode_decode _ (by simp; omega)]
  rw [show bs.drop 80 = (bs.drop 16).drop 64 by simp [List.drop_drop]]
  rw [List.append_assoc, List.take_append_drop, List.take_append_drop]

theorem pageMeta_take (bs : List w8) (n : Nat) (h : 80 ≤ n) : pageMeta (bs.take n) = pageMeta bs := by
  unfold pageMeta
  rw [List.drop_take, List.take_take, show min 64 (n - 16) = 64 by omega]

/-- Page `i` of `xs` read back as its first `n` bytes. -/
theorem fileMeta_window (xs : List w8) (i n : Nat) (h : 80 ≤ n) :
    pageMeta ((xs.drop (4096 * i)).take n) = fileMeta xs i := by
  unfold fileMeta; exact pageMeta_take _ _ h

end bytes

section osbytes
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- The window `[a, a + n)` of a file's bytes, and back. -/
theorem osBytes_window (p : GoString) (dq : DFrac) (xs : List (w8 × Bool)) (a n : Nat)
    (h : a + n ≤ xs.length) :
    osBytes (L := L) p 0 dq xs ⊣⊢
      osBytes (L := L) p 0 dq (xs.take a) ∗ osBytes (L := L) p a dq ((xs.drop a).take n) ∗
        osBytes (L := L) p (a + n) dq ((xs.drop a).drop n) := by
  unfold osBytes
  have e1 := bytesG_append (gooseOsGS (L := L)) p dq 0 (xs.take a) (xs.drop a)
  have e2 := bytesG_append (gooseOsGS (L := L)) p dq a ((xs.drop a).take n) ((xs.drop a).drop n)
  rw [List.take_append_drop] at e1 e2
  simp only [List.length_take, List.length_drop, Nat.zero_add] at e1 e2
  rw [show min a xs.length = a by omega] at e1
  rw [show min n (xs.length - a) = n by omega] at e2
  exact e1.trans (sep_congr .rfl e2)

end osbytes

section views
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

/-- Any page's bytes as its header, its meta and the rest. -/
theorem pageView (l : Loc) (dq : DFrac) (bs : List w8) (h : 80 ≤ bs.length) (hl : 0 < l.addr) :
    bytesPointsto (GF := GF) l dq bs ⊣⊢
      l ↦{dq} pageHdrOf bs ∗ (l +ₗ 16) ↦{dq} pageMeta bs ∗ bytesPointsto (l +ₗ 80) dq (bs.drop 80) := by
  conv => lhs; rw [page_split bs h]
  exact pageMeta_view l dq _ _ _ hl

end views

end github_com.mit_pdos.etcd_grove.examples.bboltfs

end Perennial
