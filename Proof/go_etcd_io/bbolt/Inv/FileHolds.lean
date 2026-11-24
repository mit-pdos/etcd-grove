/-
`fileHolds` (U0a of `notes/bbolt-proof-plan.md`; design §3.11, over D-B's fix): a file with no
mapping, all of whose page-cache bytes the client holds, either fresh (no file, or empty) or the
image of a committed state `C` (`fileImage`) that is `metaOk`, `treeOK`, has a reloadable synced
freelist page (`flFileOK`), whose high-water mark is inside the file and whose txid is below
`2 ^ 62`, holding `D`.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Tx
public import Proof.go_etcd_io.bbolt.Read.TxBytes
public import GooseLang.Ext.Fs.TreeShared
public import Proof.go_etcd_io.bbolt.Inv.FileImg

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode

section holds
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A file just created holds the empty database. -/
theorem fileHoldsDef_new (i : Ino) :
    osMeta (GF := GF) i (DFrac.own 1) newMeta ⊢ fileHoldsDef i ∅ := by
  unfold fileHoldsDef
  iintro H
  iexists newMeta, []
  iframe H
  isplitl
  · unfold osBytes; iapply (bytesG_nil _ _ _ _).2; iempintro
  isplitr
  · ipureintro
    exact ⟨rfl, rfl, by decide, Or.inl ⟨rfl, rfl⟩⟩
  unfold fileRcpt
  ileft; ipureintro
  exact fun C h => fileImage_nil_not C (by simpa using h)

/-- **Decoding for `Open`**: an empty file holding `∅`, or the initial committed state `C` of a
well-formed one (with its bytes). -/
theorem fileHolds_decode (i : Ino) (D : Data) :
    fileHoldsDef (GF := GF) i D ⊢
      (∃ (m : OsMeta) (xs : List ByteG), osMeta i (DFrac.own 1) m ∗
        osBytes i 0 (DFrac.own 1) xs ∗
        ⌜m.maps = ∅ ∧ xs.length = m.size ∧ (m.size < 2 ^ 62 ∧ m.size % 4096 = 0)⌝ ∗
        fileRcpt (xs.map Prod.fst) ∗
        (⌜m.size = 0 ∧ D = ∅⌝ ∨
         ∃ C, ⌜fileImage (xs.map Prod.fst) C ∧ C.metaOk ∧ treeOK C ∧
           flFileOK (xs.map Prod.fst) C ∧ C.hwm * 4096 ≤ m.size ∧ 1 ≤ C.txid ∧ C.txid < 2 ^ 62 ∧
           treeData C = D⌝)) := by
  unfold fileHoldsDef
  iintro ⟨%m, %xs, Hm, Hb, %h, #Hr⟩
  iexists m, xs
  iframe Hm Hb Hr
  obtain ⟨h1, h2, h0, h3⟩ := h
  isplitr
  · ipureintro; exact ⟨h1, h2, h0⟩
  rcases h3 with h3 | ⟨C, hC⟩
  · ileft; ipureintro; exact h3
  · iright; iexists C; ipureintro; exact hC

end holds

end bbolt
end EtcdGrove
end Perennial
