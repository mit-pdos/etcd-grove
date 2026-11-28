/-
The API service's argument structs as the codec decodes them (hand-written, as `CodecDefs.lean` for the
transport's requests): the pure decoders of `AdminArgs`, `ApplyArgs` and `ReadArgs` (the generated
`rpcDec_t37`, `rpcDec_t41`, `rpcDec_t45` on any bytes), their round trips on `ApiWire.lean`'s
encodings, and so the arguments' encodings are injective below the bound of a slice's bytes
(`encApplyArgs_inj`, ...): a deposit's argument bytes name one argument.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.CodecDefs
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.ApiWire

@[expose] public section

noncomputable section

namespace Perennial

namespace github_com.hashicorp.raft.examples.hraftnet

open rpctransport

/-- The pure `AdminArgs` decoder. -/
def decAdminArgsV (bs : List w8) : Option (AdminArgsV × List w8) :=
  match decStructHdr bs with
  | none => none
  | some r =>
    match decFld getTag [] r with
    | none => none
    | some (id, r) =>
      match decFld getTag [] r with
      | none => none
      | some (ad, r) => some (⟨id, ad⟩, r)

/-- The pure `ApplyArgs` decoder. -/
def decApplyArgsV (bs : List w8) : Option (ApplyArgsV × List w8) :=
  match decStructHdr bs with
  | none => none
  | some r =>
    match decFld decBytes [] r with
    | none => none
    | some (d, r) => some (⟨d⟩, r)

/-- The pure `ReadArgs` decoder. -/
def decReadArgsV (bs : List w8) : Option (ReadArgsV × List w8) :=
  match decStructHdr bs with
  | none => none
  | some r =>
    match decFld getU64 (W64 0) r with
    | none => none
    | some (w, r) => some (⟨w⟩, r)

theorem decAdminArgsV_enc (v : AdminArgsV) (rest : List w8)
    (hl : (strct [fStr v.id, fStr v.addr] ++ rest).length < 2 ^ 64) :
    decAdminArgsV (strct [fStr v.id, fStr v.addr] ++ rest) = some (v, rest) := by
  have e : strct [fStr v.id, fStr v.addr] ++ rest = W8 1 :: (fStr v.id ++ (fStr v.addr ++ rest)) := by
    simp [strct]
  rw [e] at hl ⊢
  simp (disch := len_tac) only [decAdminArgsV, decStructHdr, ↓reduceIte, decFld_fStr]

theorem decApplyArgsV_enc (v : ApplyArgsV) (rest : List w8)
    (hl : (strct [fBytes v.data] ++ rest).length < 2 ^ 64) :
    decApplyArgsV (strct [fBytes v.data] ++ rest) = some (v, rest) := by
  have e : strct [fBytes v.data] ++ rest = W8 1 :: (fBytes v.data ++ rest) := by
    simp [strct]
  rw [e] at hl ⊢
  simp (disch := len_tac) only [decApplyArgsV, decStructHdr, ↓reduceIte, decFld_fBytes]

theorem decReadArgsV_enc (v : ReadArgsV) (rest : List w8) :
    decReadArgsV (strct [fU64 v.way] ++ rest) = some (v, rest) := by
  have e : strct [fU64 v.way] ++ rest = W8 1 :: (fU64 v.way ++ rest) := by
    simp [strct]
  rw [e]
  simp only [decReadArgsV, decStructHdr, ↓reduceIte, decFld_fU64]

/-! ## The arguments' encodings are injective (below the bound of a slice's bytes) -/

theorem encAdminArgs_inj (v v' : AdminArgsV) (hl : (encAdminArgs v).length < 2 ^ 64)
    (h : encAdminArgs v = encAdminArgs v') : v = v' := by
  have hb := tagged_body_inj h
  have h1 := decAdminArgsV_enc v [] (by unfold encAdminArgs tagged at hl; simp only [List.append_nil, List.length_append] at hl ⊢; omega)
  have h2 := decAdminArgsV_enc v' [] (by rw [← hb]; unfold encAdminArgs tagged at hl; simp only [List.append_nil, List.length_append] at hl ⊢; omega)
  rw [← hb] at h2
  rw [h1] at h2
  cases h2; rfl

theorem encApplyArgs_inj (v v' : ApplyArgsV) (hl : (encApplyArgs v).length < 2 ^ 64)
    (h : encApplyArgs v = encApplyArgs v') : v = v' := by
  have hb := tagged_body_inj h
  have h1 := decApplyArgsV_enc v [] (by unfold encApplyArgs tagged at hl; simp only [List.append_nil, List.length_append] at hl ⊢; omega)
  have h2 := decApplyArgsV_enc v' [] (by rw [← hb]; unfold encApplyArgs tagged at hl; simp only [List.append_nil, List.length_append] at hl ⊢; omega)
  rw [← hb] at h2
  rw [h1] at h2
  cases h2; rfl

theorem encReadArgs_inj (v v' : ReadArgsV) (h : encReadArgs v = encReadArgs v') : v = v' := by
  have hb := tagged_body_inj h
  have h1 := decReadArgsV_enc v []
  have h2 := decReadArgsV_enc v' []
  rw [← hb] at h2
  rw [h1] at h2
  cases h2; rfl

end github_com.hashicorp.raft.examples.hraftnet

end Perennial
