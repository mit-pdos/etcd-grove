/-
minibolt's pages (`examples/bboltfs/page.go`) as bytes: the typed views of a page's bytes (a page
header, and the meta right after it, `pageMeta_view`), and the four pages `initPages` lays out
(`initBytes`).

A page's bytes are any byte points-to at a positive address: a Go buffer's elements
(`ownSlice_bytes_acc`), or the client's halves of a file mapping's cells (heap points-tos at a
fraction, `GooseLang/Ext/OsFs/Specs.lean`). `pageMeta_view` holds at any fraction, so a read-only
view of a mapped meta page is a fractional `Page` and `Meta` points-to, what the read-only specs
(`Page.meta`, `Meta.sum64`, `Meta.validate`, `pickMeta`) take.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.Meta

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.mit_pdos.etcd_grove.examples.bboltfs

/-! ## The initial pages -/

section init
variable [GooseExts]

/-- The page size, `pageSize` (`common.DefaultPageSize`). -/
abbrev pageBytes : Nat := 4096

/-- `n` zero bytes. -/
abbrev zeroBytes (n : Nat) : List w8 := List.replicate n 0

/-- The meta `initPages` writes into page `i` (0 or 1), before its checksum: magic, version, page
size 4096, root 3, freelist 2, high water mark 4, txid `i`. -/
def initMeta0 (i : Nat) : Meta :=
  ⟨W32 0xED0CDAED, W32 2, W32 4096, W32 0, ⟨W64 3, W64 0⟩, W64 2, W64 4, W64 (i : Int), W64 0⟩

/-- The meta of page `i` (0 or 1), with its checksum. -/
def initMeta (i : Nat) : Meta := { initMeta0 i with checksum' := metaSum (initMeta0 i) }

/-- Both initial metas are valid. -/
theorem initMeta_valid (i : Nat) : metaValid (initMeta i) :=
  metaValid_withSum _ rfl rfl

/-- The header of page `id`, with flags `flags`, `count` and `overflow` 0. -/
def pageHdr (id : w64) (flags : w16) : Page := ⟨id, flags, W16 0, W32 0⟩

/-- Meta page `i` (0 or 1): its header (`metaPageFlag`), its meta, and zeros. -/
def metaPageBytes (i : Nat) : List w8 :=
  encode (pageHdr (W64 (i : Int)) (W16 4)) ++ encode (initMeta i) ++ zeroBytes (pageBytes - 80)

/-- An empty page `id` with flags `flags`: its header and zeros. -/
def emptyPageBytes (id : w64) (flags : w16) : List w8 :=
  encode (pageHdr id flags) ++ zeroBytes (pageBytes - 16)

/-- `initPages`'s four pages: the metas with txids 0 and 1, the empty freelist (page 2,
`freelistPageFlag`) and the empty root leaf (page 3, `leafPageFlag`). -/
def initBytes : List w8 :=
  metaPageBytes 0 ++ metaPageBytes 1 ++ emptyPageBytes (W64 2) (W16 16) ++
    emptyPageBytes (W64 3) (W16 2)

theorem metaPageBytes_length (i : Nat) : (metaPageBytes i).length = pageBytes := by
  simp [metaPageBytes, ByteEncoding.encode_length, pageBytes]

theorem emptyPageBytes_length (id : w64) (flags : w16) :
    (emptyPageBytes id flags).length = pageBytes := by
  simp [emptyPageBytes, ByteEncoding.encode_length, pageBytes]

theorem initBytes_length : initBytes.length = 4 * pageBytes := by
  simp only [initBytes, List.length_append, metaPageBytes_length, emptyPageBytes_length]
  omega

end init

/-! ## Typed views of a page's bytes -/

section views
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

/-- The bytes of a page holding a header and a meta are a typed header at the page, a typed meta
16 bytes after it (where `Page.meta` points), and the rest. -/
theorem pageMeta_view (l : Loc) (dq : DFrac) (hdr : Page) (v : Meta) (rest : List w8)
    (hl : 0 < l.addr) :
    bytesPointsto (GF := GF) l dq (encode hdr ++ encode v ++ rest) ⊣⊢
      l ↦{dq} hdr ∗ (l +ₗ 16) ↦{dq} v ∗ bytesPointsto (l +ₗ 80) dq rest := by
  have h16 : 0 < (l +ₗ 16).addr := by simp only [Loc.add]; omega
  have hs1 := bytesPointsto_app (GF := GF) l dq (encode hdr ++ encode v) rest
  have hs2 := bytesPointsto_app (GF := GF) l dq (encode hdr) (encode v)
  have e1 : (((encode hdr).length : Nat) : Int) = 16 := by rw [ByteEncoding.encode_length]; rfl
  have e2 : (((encode hdr ++ encode v).length : Nat) : Int) = 80 := by
    simp only [List.length_append, ByteEncoding.encode_length]; rfl
  rw [e2] at hs1
  rw [e1] at hs2
  have th := typedPointsto_bytes (GF := GF) l hdr dq hl
  have tv := typedPointsto_bytes (GF := GF) (l +ₗ 16) v dq h16
  constructor
  · iintro H
    icases hs1.1 $$ H with ⟨H1, H2⟩
    icases hs2.1 $$ H1 with ⟨Hh, Hv⟩
    iframe H2
    isplitl [Hh]
    · iapply th.2 $$ Hh
    · iapply tv.2 $$ Hv
  · iintro ⟨Hh, Hv, H2⟩
    iapply hs1.2
    iframe H2
    iapply hs2.2
    isplitl [Hh]
    · iapply th.1 $$ Hh
    · iapply tv.1 $$ Hv

/-- The bytes of a page with a header only: a typed header and the rest. -/
theorem pageHdr_view (l : Loc) (dq : DFrac) (hdr : Page) (rest : List w8) (hl : 0 < l.addr) :
    bytesPointsto (GF := GF) l dq (encode hdr ++ rest) ⊣⊢
      l ↦{dq} hdr ∗ bytesPointsto (l +ₗ 16) dq rest := by
  have hs := bytesPointsto_app (GF := GF) l dq (encode hdr) rest
  have e1 : (((encode hdr).length : Nat) : Int) = 16 := by rw [ByteEncoding.encode_length]; rfl
  rw [e1] at hs
  have th := typedPointsto_bytes (GF := GF) l hdr dq hl
  constructor
  · iintro H
    icases hs.1 $$ H with ⟨Hh, H2⟩
    iframe H2
    iapply th.2 $$ Hh
  · iintro ⟨Hh, H2⟩
    iapply hs.2
    iframe H2
    iapply th.1 $$ Hh

end views

end github_com.mit_pdos.etcd_grove.examples.bboltfs

end Perennial
