/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/jsonstream/Frame.lean (lab master
915f964; notes/dsv-vr.md): over any `GF`, the connection number a `Nat`.
-/
/-
The decoder's framing of `γ`'s stream (pure, from the codec's scanner facts and the wire's reader
views): where a healthy decoder stands (`events.rstreamAt ms pend U R`: `R` read, `U` its unread
buffered bytes), the scanner on `U` either asks for more (`scanF`'s `More`, and `U` is short) or
finds the next line's value: whitespace `ws`, then `encEvent m` of a valid message `m` with
plain strings, after which the decoder stands again (`rstreamAt` of the rest `z`). With
`leadSpace_line` (the model's `skipSpace` at the value: the whitespace's length) and
`rstreamAt_append` (what a read appends). Lean-first beyond the lab's.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.json
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.jsoncodec.Stream

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

open examples

theorem jsonstream.ws_space (ws : List w8) (h : ws = [] ∨ ws = [W8 10]) :
    ∀ c ∈ ws, encoding.json.isSpaceB c = true := by
  rcases h with rfl | rfl
  · simp
  · intro c hc; simp at hc; subst hc; decide

theorem jsonstream.line_eq (m : Msg) : VsrWire.line m = VsrWire.encEvent m ++ [W8 10] := rfl

theorem jsonstream.lines_snoc (ms : List Msg) (m : Msg) :
    VsrWire.lines (ms ++ [m]) = VsrWire.lines ms ++ VsrWire.encEvent m ++ [W8 10] := by
  simp [VsrWire.lines, VsrWire.line]


theorem jsonstream.scanF_partial (ws pre : List w8) (m : Msg) (eof : Bool)
    (hws : ∀ c ∈ ws, encoding.json.isSpaceB c = true) (hm : PlainMsg m)
    (hpre : pre <+: VsrWire.encEvent m) (hne : pre ≠ VsrWire.encEvent m) :
    (vsrnet.scanF (ws ++ pre) eof).1 = W64 1 :=
  vsrnet.scanF_partial_eof ws pre m eof hws hm hpre hne

theorem jsonstream.scanF_space (ws : List w8) (eof : Bool)
    (hws : ∀ c ∈ ws, encoding.json.isSpaceB c = true) :
    (vsrnet.scanF ws eof).1 = W64 1 := by
  rw [vsrnet.scanF_space ws eof hws]

theorem jsonstream.rstreamAt_append (ms : List Msg) (pend : Option Msg) (U R x : List w8)
    (h : events.rstreamAt ms pend U R) : events.rstreamAt ms pend (U ++ x) (R ++ x) := by
  cases pend with
  | none =>
    obtain ⟨ws, U', hws, hU, hR⟩ := h
    exact ⟨ws, U' ++ x, hws, by rw [hU, List.append_assoc], by rw [hR, List.append_assoc]⟩
  | some m =>
    obtain ⟨hm, hR⟩ := h
    exact ⟨hm, by rw [hR]; simp⟩

/-- The model's `skipSpace` at a line's value: the whitespace before it (an event's encoding
starts with `{`). -/
theorem jsonstream.leadSpace_line (ws z : List w8) (m : Msg) (hws : ws = [] ∨ ws = [W8 10])
    (hm : PlainMsg m) : encoding.json.leadSpace (ws ++ VsrWire.encEvent m ++ z) = ws.length := by
  obtain ⟨rest, he⟩ : ∃ rest, VsrWire.encEvent m = VsrJson.cLB :: rest := by
    simp only [VsrWire.encEvent, VsrJson.encEvent, hm, ↓reduceIte, VsrJson.evJV, VsrJson.ser,
      List.cons_append]
    exact ⟨_, rfl⟩
  rw [he]
  rcases hws with rfl | rfl <;> rfl


section facts
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [π : NetProtoGS]

/-- `protoOf_next`, its facts as the decoder uses them. -/
theorem jsonstream.protoOf_next_short (γ : VsrGhost.Names) (cid : Nat) (ext R : List w8)
    (ms : List Msg) (rest : List w8)
    (hR : R <+: ext) (hms : R = VsrWire.lines ms ++ rest) (hne : rest ≠ []) :
    □ VsrWire.protoOf (G := hG.goose_globalGS) γ cid ext ⊢ ∃ m : Msg, ⌜rest <+: VsrWire.line m ∨ VsrWire.line m <+: rest⌝ ∗
      ⌜PlainMsg m ∧ MsgBound m⌝ ∗ ⌜(VsrWire.line m).length < 2 ^ 60⌝ ∗
      VsrGhost.fact γ (.msg m) := by
  iintro #H
  ihave ⟨%m, %h1, %h2, %h3, %h4, #Hf⟩ := VsrWire.protoOf_next γ cid ext R ms rest hR hms hne $$ H
  iexists m
  iframe Hf
  ipureintro
  exact ⟨h1, ⟨h2, h3⟩, h4⟩

/-- An encoding is never a strict prefix of another (the scanner ends a value where it ends). -/
theorem jsonstream.enc_prefix_free (m m' : Msg) (hm : PlainMsg m) (hm' : PlainMsg m')
    (h : VsrWire.encEvent m <+: VsrWire.encEvent m') :
    VsrWire.encEvent m = VsrWire.encEvent m' := by
  refine Classical.byContradiction fun hne => ?_
  have h1 := vsrnet.scanF_partial [] (VsrWire.encEvent m) m' (by simp) hm' h hne
  have h2 := vsrnet.scanF_line [] m [] false (by simp) hm
  simp only [List.nil_append, List.append_nil] at h1 h2
  rw [h2] at h1
  simp at h1

/-- Two encodings that are prefixes of one list are equal. -/
theorem jsonstream.enc_common (m m' : Msg) (A : List w8) (hm : PlainMsg m) (hm' : PlainMsg m')
    (h1 : VsrWire.encEvent m <+: A) (h2 : VsrWire.encEvent m' <+: A) :
    VsrWire.encEvent m = VsrWire.encEvent m' := by
  rcases List.prefix_or_prefix_of_prefix h1 h2 with h | h
  · exact jsonstream.enc_prefix_free m m' hm hm' h
  · exact (jsonstream.enc_prefix_free m' m hm' hm h).symm

/-- The outcome of the scanner on a healthy decoder's unread bytes, knowing the next message
`m` of the stream after `ws` (from `protoOf_next`). -/
theorem jsonstream.scan_none_pure (ws U' : List w8) (ms : List Msg) (R : List w8) (m : Msg)
    (eof : Bool) (hws : ws = [] ∨ ws = [W8 10]) (hm : PlainMsg m)
    (hlen : (VsrWire.line m).length < 2 ^ 60)
    (hnext : U' <+: VsrWire.line m ∨ VsrWire.line m <+: U') (hR : R = VsrWire.lines ms ++ U') :
    ((vsrnet.scanF (ws ++ U') eof).1 = W64 1 ∧ (ws ++ U').length < 2 ^ 60) ∨
    (∃ (z : List w8) (ms' : List Msg) (pend' : Option Msg),
      ws ++ U' = ws ++ VsrWire.encEvent m ++ z ∧
      vsrnet.scanF (ws ++ U') eof =
        (W64 0, W64 (ws.length + (VsrWire.encEvent m).length)) ∧
      events.rstreamAt ms' pend' z R) := by
  have hsp := jsonstream.ws_space ws hws
  have hwsl : ws.length ≤ 1 := by rcases hws with rfl | rfl <;> simp
  -- the line is in `U'`: its value is found, the newline stays
  have hfull : ∀ z, U' = VsrWire.encEvent m ++ [W8 10] ++ z →
      ∃ (z : List w8) (ms' : List Msg) (pend' : Option Msg),
        ws ++ U' = ws ++ VsrWire.encEvent m ++ z ∧
        vsrnet.scanF (ws ++ U') eof =
          (W64 0, W64 (ws.length + (VsrWire.encEvent m).length)) ∧
        events.rstreamAt ms' pend' z R := by
    intro z hz
    refine ⟨[W8 10] ++ z, ms ++ [m], none, ?_, ?_, ?_⟩
    · rw [hz]; simp
    · rw [hz, show ws ++ (VsrWire.encEvent m ++ [W8 10] ++ z) =
        ws ++ VsrWire.encEvent m ++ ([W8 10] ++ z) by simp]
      exact vsrnet.scanF_line ws m _ eof hsp hm
    · refine ⟨[W8 10], z, Or.inr rfl, rfl, ?_⟩
      rw [hR, hz, jsonstream.lines_snoc]; simp
  rcases hnext with h | h
  · -- `U'` is a prefix of the line
    rw [jsonstream.line_eq] at h
    by_cases hp : U' <+: VsrWire.encEvent m
    · by_cases he : U' = VsrWire.encEvent m
      · right
        refine ⟨[], ms, some m, by simp [he], ?_, ⟨hm, by simp [hR, he]⟩⟩
        rw [he, show ws ++ VsrWire.encEvent m = ws ++ VsrWire.encEvent m ++ [] by simp]
        exact vsrnet.scanF_line ws m [] eof hsp hm
      · left
        refine ⟨jsonstream.scanF_partial ws U' m eof hsp hm hp he, ?_⟩
        have := hp.length_le
        have h2 : (VsrWire.line m).length = (VsrWire.encEvent m).length + 1 := by
          simp [VsrWire.line]
        simp only [List.length_append]; omega
    · -- `U'` is the whole line
      have hl := h.length_le
      have hlt : ¬ U'.length ≤ (VsrWire.encEvent m).length := by
        intro hle
        exact hp (List.prefix_of_prefix_length_le h (List.prefix_append _ _) hle)
      have heq : U' = VsrWire.encEvent m ++ [W8 10] :=
        h.eq_of_length (by simp only [List.length_append, List.length_singleton] at hl ⊢; omega)
      right
      exact hfull [] (by simp [heq])
  · right
    obtain ⟨z, hz⟩ := h
    exact hfull z (by rw [← hz, jsonstream.line_eq])

/-- The scan outcome of a healthy decoder (see the file header): from the reader's knowledge of
the stream (`protoPrefix`, from its token). -/
theorem jsonstream.scan_next (γ : VsrGhost.Names) (cid : Nat) (R U : List w8) (ms : List Msg)
    (pend : Option Msg) (eof : Bool) (hst : events.rstreamAt ms pend U R) :
    protoPrefix (VsrWire.protoOf (G := hG.goose_globalGS) γ) cid R ⊢
      ⌜(vsrnet.scanF U eof).1 = W64 1 ∧ U.length < 2 ^ 60⌝ ∨
      (∃ (m : Msg) (ws z : List w8) (ms' : List Msg) (pend' : Option Msg),
        ⌜U = ws ++ VsrWire.encEvent m ++ z ∧ (ws = [] ∨ ws = [W8 10]) ∧ PlainMsg m ∧
          vsrnet.scanF U eof = (W64 0, W64 (ws.length + (VsrWire.encEvent m).length)) ∧
          events.rstreamAt ms' pend' z R ∧ MsgBound m⌝ ∗ VsrGhost.fact γ (.msg m)) := by
  -- the stream is at a line's start (`ms`, after `ws`), or the decoder has nothing unread
  have hnorm : (∃ ms0 ws U', (ws = [] ∨ ws = [W8 10]) ∧ U = ws ++ U' ∧
      R = VsrWire.lines ms0 ++ U') ∨ U = [] ∨
      (∃ m0, PlainMsg m0 ∧ U ≠ [] ∧ R = VsrWire.lines ms ++ VsrWire.encEvent m0 ++ U) := by
    cases pend with
    | none => obtain ⟨ws, U', h1, h2, h3⟩ := hst; exact Or.inl ⟨ms, ws, U', h1, h2, h3⟩
    | some m0 =>
      obtain ⟨hm0, hR⟩ := hst
      by_cases hU : U = []
      · exact Or.inr (Or.inl hU)
      · exact Or.inr (Or.inr ⟨m0, hm0, hU, hR⟩)
  have hspace : U = [] → (vsrnet.scanF U eof).1 = W64 1 ∧ U.length < 2 ^ 60 := by
    intro hU; subst hU; exact ⟨jsonstream.scanF_space [] eof (by simp), by simp⟩
  iintro Hp
  unfold protoPrefix
  icases Hp with (%hR0 | ⟨%ext, %hRe, #Hext⟩)
  · -- nothing read: nothing unread
    ileft; ipureintro
    rcases hnorm with ⟨ms0, ws, U', hws, hU, hR⟩ | hU | ⟨m0, -, hne, hR⟩
    · subst hR0
      have hU' : U' = [] := (List.append_eq_nil_iff.1 hR.symm).2
      subst hU' hU
      simp only [List.append_nil]
      refine ⟨jsonstream.scanF_space ws eof (jsonstream.ws_space ws hws), ?_⟩
      rcases hws with rfl | rfl <;> simp
    · exact hspace hU
    · subst hR0; simp at hR; exact absurd hR.2.2 hne
  -- the stream so far is a prefix of the protocol's `ext`
  have hcase : ∀ ms0 ws U', (ws = [] ∨ ws = [W8 10]) → U = ws ++ U' →
      R = VsrWire.lines ms0 ++ U' →
      (⊢ (□ VsrWire.protoOf (G := hG.goose_globalGS) γ cid ext -∗ (⌜(vsrnet.scanF U eof).1 = W64 1 ∧ U.length < 2 ^ 60⌝ ∨
      (∃ (m : Msg) (ws z : List w8) (ms' : List Msg) (pend' : Option Msg),
        ⌜U = ws ++ VsrWire.encEvent m ++ z ∧ (ws = [] ∨ ws = [W8 10]) ∧ PlainMsg m ∧
          vsrnet.scanF U eof = (W64 0, W64 (ws.length + (VsrWire.encEvent m).length)) ∧
          events.rstreamAt ms' pend' z R ∧ MsgBound m⌝ ∗ VsrGhost.fact γ (.msg m))) : IProp GF)) := by
    intro ms0 ws U' hws hU hR
    iintro #H
    by_cases hU' : U' = []
    · subst hU'
      ileft; ipureintro
      rw [hU, List.append_nil]
      refine ⟨jsonstream.scanF_space ws eof (jsonstream.ws_space ws hws), ?_⟩
      rcases hws with rfl | rfl <;> simp
    ihave ⟨%m, %hnext, ⟨%hm, %hmb⟩, %hlen, #Hf⟩ :=
      jsonstream.protoOf_next_short γ cid ext R ms0 U' hRe hR hU' $$ H
    rcases jsonstream.scan_none_pure ws U' ms0 R m eof hws hm hlen hnext hR with
      ⟨h1, h2⟩ | ⟨z, ms', pend', h1, h2, h3⟩
    · ileft; ipureintro; rw [hU]; exact ⟨h1, h2⟩
    · iright
      iexists m, ws, z, ms', pend'
      iframe Hf
      ipureintro
      rw [hU]
      exact ⟨h1, hws, hm, h2, h3, hmb⟩
  rcases hnorm with ⟨ms0, ws, U', hws, hU, hR⟩ | hU | ⟨m0, hm0, hne, hR⟩
  · iapply hcase ms0 ws U' hws hU hR
    iexact Hext
  · ileft; ipureintro; exact hspace hU
  · -- the last message's newline: `U` starts with it
    have hne' : VsrWire.encEvent m0 ++ U ≠ [] := by simp [hne]
    ihave ⟨%m, %hnext, ⟨%hm, -⟩, -, -⟩ :=
      jsonstream.protoOf_next_short γ cid ext R ms (VsrWire.encEvent m0 ++ U) hRe
        (by rw [hR, List.append_assoc]) hne' $$ Hext
    have hA : ∃ A, VsrWire.encEvent m0 <+: A ∧ VsrWire.encEvent m <+: A ∧
        (VsrWire.encEvent m0 ++ U <+: VsrWire.line m ∨ VsrWire.line m <+: VsrWire.encEvent m0 ++ U) := by
      rcases hnext with h | h
      · exact ⟨VsrWire.line m, (List.prefix_append _ _).trans h, List.prefix_append _ _, Or.inl h⟩
      · exact ⟨VsrWire.encEvent m0 ++ U, List.prefix_append _ _,
          (List.prefix_append _ _).trans h, Or.inr h⟩
    obtain ⟨A, hA1, hA2, hnext'⟩ := hA
    have heq := jsonstream.enc_common m0 m A hm0 hm hA1 hA2
    rw [jsonstream.line_eq, ← heq] at hnext'
    have hU10 : ∃ U'', U = [W8 10] ++ U'' := by
      rcases hnext' with h | h
      · rw [List.prefix_append_right_inj] at h
        obtain ⟨t, ht⟩ := h
        cases U with
        | nil => exact absurd rfl hne
        | cons x xs =>
          cases t with
          | nil => simp at ht; exact ⟨[], by simp [ht.1, ht.2]⟩
          | cons y ys => simp at ht
      · rw [List.prefix_append_right_inj] at h
        obtain ⟨t, ht⟩ := h
        exact ⟨t, ht.symm⟩
    obtain ⟨U'', hU''⟩ := hU10
    iapply hcase (ms ++ [m0]) [W8 10] U'' (Or.inr rfl) hU''
      (by rw [hR, hU'', jsonstream.lines_snoc]; simp)
    iexact Hext

end facts

end Perennial.github_com.tangledbytes.go_vsr.pkg
