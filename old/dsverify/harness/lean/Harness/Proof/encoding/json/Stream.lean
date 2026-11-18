/-
`NewEncoder` and `Encoder.Encode` of the lab's `encoding/json` model (`stream.go`), over a writer
meeting bufio's `writerOk wr J Q` (`Harness/Proof/bufio/Defs.lean`; for a `net.Conn`,
`writerOk_conn`): `Encode(v)` writes the kit's encoding of `v` and a newline in one `Write`, and
keeps the first write error, returning it from then on.
-/
module

public import Harness.Proof.encoding.json.Codec

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace encoding.json

section spec
variable [JsonKit]
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [encoding.json.Assumptions] [JsonCodec GF]

/-- An encoder `enc` writing to `wr`, with sticky error `err` (`nil` before a write failed). -/
def ownEncoder (enc : Loc) (wr err : GoInterface) : IProp GF :=
  iprop(structFieldRef encoding.json.Encoder go!"w" enc ↦□ wr ∗
    structFieldRef encoding.json.Encoder go!"err" enc ↦ err)

set_option goose.wp.extras true

/-- `NewEncoder(w)`: an encoder writing to `w`, with no error. -/
abbrev NewEncoder.spec : Prop :=
  ∀ (w : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.json }}
    (App (Val (@! encoding.json.NewEncoder)) (Val #w))
  {{ (enc : Loc), RET #enc; ownEncoder (GF := GF) enc w interface.nil }}

theorem NewEncoder.wp_proof : NewEncoder.spec (GF := GF) (hG := hG) := by
  intro w
  wp_start
  iapply wp_fupd
  wp_auto
  iStructNamed «$r0»
  ipersist w
  imodintro
  iapply HΦ
  unfold ownEncoder
  iframe w
  iexact err

/-- `enc.Encode(v)`, `enc` writing to `wr` (`writerOk wr J Q`, `J W` holding the stream written
so far, `W`), the encoding allowed after `W` (`HQ`): with a sticky error `err0`, it returns it
and does nothing; else a `Marshal` error (non-nil, `Ψ none`, nothing written); else the encoding
`bs` and a newline are written in one `Write`, `k` bytes of them (all of them when `err` is nil),
and `err` becomes sticky. -/
abbrev Encoder.Encode.spec : Prop :=
  ∀ (F : List w8 → Bool → w64 × w64) (enc : Loc) (wr err0 v : GoInterface)
    (J Q : List w8 → IProp GF) (W : List w8) (Ψ : Option (List w8) → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.json ∗ codecSet (GF := GF) ∗
      kitCodecOk F ∗ ownEncoder enc wr err0 ∗ bufio.writerOk wr J Q ∗ J W ∗
      JsonCodec.enc v Ψ ∗
      (∀ bs, Ψ (some bs) -∗ □ Q (W ++ (bs ++ [W8 10])) ∗ Ψ (some bs)) }}
    (App (Val (enc @!! go.GoType.PointerType encoding.json.Encoder.ty @!! go!"Encode")) (Val #v))
  {{ (err : GoInterface), RET #err;
      (⌜err0 ≠ interface.nil ∧ err = err0⌝ ∗ ownEncoder enc wr err0 ∗ J W ∗
        JsonCodec.enc v Ψ) ∨
      (⌜err0 = interface.nil ∧ err ≠ interface.nil⌝ ∗ ownEncoder enc wr interface.nil ∗ J W ∗
        Ψ none) ∨
      (⌜err0 = interface.nil⌝ ∗ ∃ (bs : List w8) (k : Nat),
        ⌜k ≤ bs.length + 1 ∧ (err = interface.nil → k = bs.length + 1)⌝ ∗
        ownEncoder enc wr err ∗ J (W ++ (bs ++ [W8 10]).take k) ∗ Ψ (some bs) ∗
        bufio.errOrNil err) }}

theorem Encoder.Encode.wp_proof : Encoder.Encode.spec (GF := GF) (hG := hG) := by
  intro F enc wr err0 v J Q W Ψ
  wp_start as ⟨#Hset, #Hok, Henc, #Hwr, HJ, Hv, HQ⟩
  unfold ownEncoder
  icases Henc with ⟨#Hw, Herr⟩
  cases err0 with
  | ok e0 =>
    wp_auto
    iapply HΦ
    ileft
    isplitr
    · ipureintro; simp
    isplitl [Herr]
    · iframe Herr; iexact Hw
    iframe
  | nil =>
  wp_auto
  wp_apply Marshal.wp_proof F v Ψ $$ [$Hset $Hok $Hv] as %s %err Hm
  icases Hm with (⟨%Herr0, %bs, Hs, Hcap, HΨ⟩ | ⟨%Herr0, HΨ⟩)
  · subst Herr0
    wp_auto
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := w8) (t := go.byte) [W8 10]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %lit ⟨Hlit, -⟩
    wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hs $Hcap $Hlit] as %b2 ⟨Hb2, Hcap2, -⟩
    iunfold bufio.writerOk at Hwr
    icases Hwr with ⟨%e, %He, -, #HWrite⟩
    obtain ⟨rfl, hty⟩ := He
    ihave ⟨HQb, HΨ⟩ := HQ $$ HΨ
    wp_auto
    wp_apply HWrite $$ HJ HQb Hb2 as %k %err2 %Hk Hb2 HJ #Herr2
    simp only [List.length_append, List.length_singleton] at Hk
    rcases err2 with ei | _
    all_goals
      wp_auto
      iapply HΦ
      iright; iright
      isplitr
      · ipureintro; rfl
      iexists bs, k
      isplitr
      · ipureintro; exact Hk
      isplitl [Herr]
      · iframe Herr; iexact Hw
      iframe
      iexact Herr2
  · cases err with
    | nil => exact absurd rfl Herr0
    | ok e =>
    wp_auto
    iapply HΦ
    iright; ileft
    isplitr
    · ipureintro; simp
    isplitl [Herr]
    · iframe Herr; iexact Hw
    iframe

end spec

end encoding.json

end Perennial
