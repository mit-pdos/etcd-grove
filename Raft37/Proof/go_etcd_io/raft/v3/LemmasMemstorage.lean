/-
Lemmas of the `MemoryStorage` proofs (raft v3.7 retarget, stage R3): reading the storage's entry
slice (`entsRO`, `InvPbLog.lean`) at a position.
-/
module

public import Raft37.Proof.go_etcd_io.raft.v3.InvMemstorage

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The pointer at position `i` of a read-only entry slice, and the log entry behind it: what
`wp_load_slice_index` and an `Entry` getter need. Persistent, so the slice fact is kept. -/
theorem entsRO_lookup (s : GoSlice) (xs : List EntryM) (i : Nat) (e : EntryM)
    (He : xs[i]? = some e) :
    entsRO (GF := GF) s xs ⊢ ∃ (ls : List Loc) (l : Loc),
      s ↦*□ ls ∗ entRO l e ∗
      ⌜ls[i]? = some l ∧ ls.length = xs.length ∧ xs.length = sint.nat s.len ∧
        0 ≤ sint.Z s.len⌝ := by
  iintro #H
  iunfold entsRO at H
  iunfold entsPts at H
  icases H with ⟨%ls, #Hs, #Hb⟩
  ihave %Hlen := ownSlice_len $$ Hs
  ihave %Hbl := entsBig_length $$ Hb
  icases entsBig_lookup ls xs i e He $$ Hb with ⟨%l, %Hl, #Hl⟩
  iexists ls, l
  iframe Hs Hl
  ipureintro
  exact ⟨Hl, Hbl, by omega, Hlen.2⟩

/-- The slice of a read-only entry slice whose first entry is `d` is not empty. -/
theorem entsRO_cons_len (s : GoSlice) (d : EntryM) (xs : List EntryM) :
    entsRO (GF := GF) s (d :: xs) ⊢ ⌜0 < sint.Z s.len ∧ (xs.length : Int) + 1 = sint.Z s.len⌝ := by
  iintro #H
  ihave %Hl := entsPts_len $$ H
  ipureintro
  obtain ⟨h1, h2⟩ := Hl
  simp only [List.length_cons] at h1
  constructor <;> word

end lemmas

end EtcdGrove
end Perennial
