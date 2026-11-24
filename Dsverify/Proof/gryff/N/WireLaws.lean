/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/N/WireLaws.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit N: the laws of `msgWireB` (the body of `Proto2/Wire.lean`'s `msgWire`)

* `msgWireB_ne_nil`: a message's bytes are not empty.
* `msgWireB_app_inj`: a message's bytes at the start of another's are its bytes, and the
  messages agree (the code fixes the kind, the encoding is injective, `WireInj.lean`).
* `flat_prefix`: whole messages at the start of whole messages are their first ones.
-/
module

public import Dsverify.Proof.gryff.N.WireInj

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.gryff.netN

open model wire

variable [GooseExts]

open wire.gryffproto wire.epaxosproto

/-- The kind of a message, as a number. -/
def msgKindIdx : Msg → Nat
  | .read1 _ => 0 | .read2 _ => 1 | .read1Reply _ => 2 | .read2Reply _ => 3 | .write1 _ => 4
  | .write2 _ => 5 | .write1Reply _ => 6 | .write2Reply _ => 7 | .preAccept _ => 8
  | .preAcceptReply _ => 9 | .preAcceptOK _ => 10 | .accept _ => 11 | .acceptReply _ => 12
  | .commit _ => 13 | .prepare _ => 14 | .prepareReply _ => 15 | .executed _ => 16
  | .executeOverwrite _ => 17

theorem msgWireB_ne_nil {m : Msg} {b : List w8} (h : msgWireB m b) : b ≠ [] := by
  cases m <;> simp only [msgWireB] at h <;>
    first
    | (obtain ⟨g, rfl, -⟩ := h; simp)
    | exact h.elim

/-- The code of a message's bytes. -/
theorem msgWireB_code {m : Msg} {b : List w8} (h : msgWireB m b) :
    ∃ c rest, b = c :: rest ∧ msgCode m = some c := by
  cases m <;> simp only [msgWireB] at h <;>
    first
    | (obtain ⟨g, rfl, -⟩ := h; exact ⟨_, _, rfl, rfl⟩)
    | exact h.elim

/-- The kinds with the same code are the same. -/
theorem msgCode_kind {m m' : Msg} {c : w8} (h : msgCode m = some c) (h' : msgCode m' = some c) :
    msgKindIdx m = msgKindIdx m' := by
  cases m <;> cases m' <;> simp only [msgCode, Option.some.injEq, reduceCtorEq] at h h' <;>
    subst h <;> first | rfl | exact absurd h' (by decide)

/-- Two messages' bytes, one at the start of the other's continuation: the same message. -/
theorem msgWireB_app_inj {m m' : Msg} {b b' x y : List w8} (h1 : msgWireB m b)
    (h2 : msgWireB m' b') (h : b ++ x = b' ++ y) : m = m' ∧ b = b' ∧ x = y := by
  obtain ⟨c, r, rfl, hc⟩ := msgWireB_code h1
  obtain ⟨c', r', rfl, hc'⟩ := msgWireB_code h2
  simp only [List.cons_append, List.cons.injEq] at h
  obtain ⟨rfl, h⟩ := h
  have hk := msgCode_kind hc hc'
  cases m with
  | read1 mm =>
    cases m' <;> simp only [msgKindIdx] at hk <;> (try exact absurd hk (by decide))
    simp only [msgWireB, List.cons.injEq] at h1 h2
    obtain ⟨g, ⟨-, rfl⟩, h1⟩ := h1; obtain ⟨g', ⟨-, rfl⟩, h2⟩ := h2
    obtain ⟨rfl, rfl⟩ := read1_app_inj h; subst h1 h2; exact ⟨rfl, rfl, rfl⟩
  | read2 mm =>
    cases m' <;> simp only [msgKindIdx] at hk <;> (try exact absurd hk (by decide))
    simp only [msgWireB, List.cons.injEq] at h1 h2
    obtain ⟨g, ⟨-, rfl⟩, h1⟩ := h1; obtain ⟨g', ⟨-, rfl⟩, h2⟩ := h2
    obtain ⟨rfl, rfl⟩ := read2_app_inj h; subst h1 h2; exact ⟨rfl, rfl, rfl⟩
  | read1Reply mm =>
    cases m' <;> simp only [msgKindIdx] at hk <;> (try exact absurd hk (by decide))
    simp only [msgWireB, List.cons.injEq] at h1 h2
    obtain ⟨g, ⟨-, rfl⟩, h1⟩ := h1; obtain ⟨g', ⟨-, rfl⟩, h2⟩ := h2
    obtain ⟨rfl, rfl⟩ := read1Reply_app_inj h; subst h1 h2; exact ⟨rfl, rfl, rfl⟩
  | read2Reply mm =>
    cases m' <;> simp only [msgKindIdx] at hk <;> (try exact absurd hk (by decide))
    simp only [msgWireB, List.cons.injEq] at h1 h2
    obtain ⟨g, ⟨-, rfl⟩, h1⟩ := h1; obtain ⟨g', ⟨-, rfl⟩, h2⟩ := h2
    obtain ⟨rfl, rfl⟩ := read2Reply_app_inj h; subst h1 h2; exact ⟨rfl, rfl, rfl⟩
  | write1 mm =>
    cases m' <;> simp only [msgKindIdx] at hk <;> (try exact absurd hk (by decide))
    simp only [msgWireB, List.cons.injEq] at h1 h2
    obtain ⟨g, ⟨-, rfl⟩, h1⟩ := h1; obtain ⟨g', ⟨-, rfl⟩, h2⟩ := h2
    obtain ⟨rfl, rfl⟩ := write1_app_inj h; subst h1 h2; exact ⟨rfl, rfl, rfl⟩
  | write2 mm =>
    cases m' <;> simp only [msgKindIdx] at hk <;> (try exact absurd hk (by decide))
    simp only [msgWireB, List.cons.injEq] at h1 h2
    obtain ⟨g, ⟨-, rfl⟩, h1⟩ := h1; obtain ⟨g', ⟨-, rfl⟩, h2⟩ := h2
    obtain ⟨rfl, rfl⟩ := write2_app_inj h; subst h1 h2; exact ⟨rfl, rfl, rfl⟩
  | write1Reply mm =>
    cases m' <;> simp only [msgKindIdx] at hk <;> (try exact absurd hk (by decide))
    simp only [msgWireB, List.cons.injEq] at h1 h2
    obtain ⟨g, ⟨-, rfl⟩, h1⟩ := h1; obtain ⟨g', ⟨-, rfl⟩, h2⟩ := h2
    obtain ⟨rfl, rfl⟩ := write1Reply_app_inj h; subst h1 h2; exact ⟨rfl, rfl, rfl⟩
  | write2Reply mm =>
    cases m' <;> simp only [msgKindIdx] at hk <;> (try exact absurd hk (by decide))
    simp only [msgWireB, List.cons.injEq] at h1 h2
    obtain ⟨g, ⟨-, rfl⟩, h1⟩ := h1; obtain ⟨g', ⟨-, rfl⟩, h2⟩ := h2
    obtain ⟨rfl, rfl⟩ := write2Reply_app_inj h; subst h1 h2; exact ⟨rfl, rfl, rfl⟩
  | preAccept mm =>
    cases m' <;> simp only [msgKindIdx] at hk <;> (try exact absurd hk (by decide))
    simp only [msgWireB, List.cons.injEq] at h1 h2
    obtain ⟨g, ⟨-, rfl⟩, h1⟩ := h1; obtain ⟨g', ⟨-, rfl⟩, h2⟩ := h2
    obtain ⟨ha1, ha2, rfl⟩ := h1; obtain ⟨hb1, hb2, rfl⟩ := h2
    obtain ⟨rfl, rfl⟩ := preAccept_app_inj ha1 ha2 hb1 hb2 h; exact ⟨rfl, rfl, rfl⟩
  | preAcceptReply mm =>
    cases m' <;> simp only [msgKindIdx] at hk <;> (try exact absurd hk (by decide))
    simp only [msgWireB, List.cons.injEq] at h1 h2
    obtain ⟨g, ⟨-, rfl⟩, h1⟩ := h1; obtain ⟨g', ⟨-, rfl⟩, h2⟩ := h2
    obtain ⟨ha1, ha2, rfl⟩ := h1; obtain ⟨hb1, hb2, rfl⟩ := h2
    obtain ⟨rfl, rfl⟩ := preAcceptReply_app_inj ha1 ha2 hb1 hb2 h; exact ⟨rfl, rfl, rfl⟩
  | preAcceptOK mm =>
    cases m' <;> simp only [msgKindIdx] at hk <;> (try exact absurd hk (by decide))
    simp only [msgWireB, List.cons.injEq] at h1 h2
    obtain ⟨g, ⟨-, rfl⟩, h1⟩ := h1; obtain ⟨g', ⟨-, rfl⟩, h2⟩ := h2
    obtain ⟨rfl, rfl⟩ := preAcceptOK_app_inj h; subst h1 h2; exact ⟨rfl, rfl, rfl⟩
  | accept mm =>
    cases m' <;> simp only [msgKindIdx] at hk <;> (try exact absurd hk (by decide))
    simp only [msgWireB, List.cons.injEq] at h1 h2
    obtain ⟨g, ⟨-, rfl⟩, h1⟩ := h1; obtain ⟨g', ⟨-, rfl⟩, h2⟩ := h2
    obtain ⟨ha1, ha2, rfl⟩ := h1; obtain ⟨hb1, hb2, rfl⟩ := h2
    obtain ⟨rfl, rfl⟩ := accept_app_inj ha1 ha2 hb1 hb2 h; exact ⟨rfl, rfl, rfl⟩
  | acceptReply mm =>
    cases m' <;> simp only [msgKindIdx] at hk <;> (try exact absurd hk (by decide))
    simp only [msgWireB, List.cons.injEq] at h1 h2
    obtain ⟨g, ⟨-, rfl⟩, h1⟩ := h1; obtain ⟨g', ⟨-, rfl⟩, h2⟩ := h2
    obtain ⟨rfl, rfl⟩ := acceptReply_app_inj h; subst h1 h2; exact ⟨rfl, rfl, rfl⟩
  | commit mm =>
    cases m' <;> simp only [msgKindIdx] at hk <;> (try exact absurd hk (by decide))
    simp only [msgWireB, List.cons.injEq] at h1 h2
    obtain ⟨g, ⟨-, rfl⟩, h1⟩ := h1; obtain ⟨g', ⟨-, rfl⟩, h2⟩ := h2
    obtain ⟨ha1, ha2, rfl⟩ := h1; obtain ⟨hb1, hb2, rfl⟩ := h2
    obtain ⟨rfl, rfl⟩ := commit_app_inj ha1 ha2 hb1 hb2 h; exact ⟨rfl, rfl, rfl⟩
  | prepare mm =>
    cases m' <;> simp only [msgKindIdx] at hk <;> (try exact absurd hk (by decide))
    simp only [msgWireB, List.cons.injEq] at h1 h2
    obtain ⟨g, ⟨-, rfl⟩, h1⟩ := h1; obtain ⟨g', ⟨-, rfl⟩, h2⟩ := h2
    obtain ⟨rfl, rfl⟩ := prepare_app_inj h; subst h1 h2; exact ⟨rfl, rfl, rfl⟩
  | prepareReply mm =>
    cases m' <;> simp only [msgKindIdx] at hk <;> (try exact absurd hk (by decide))
    simp only [msgWireB, List.cons.injEq] at h1 h2
    obtain ⟨g, ⟨-, rfl⟩, h1⟩ := h1; obtain ⟨g', ⟨-, rfl⟩, h2⟩ := h2
    obtain ⟨ha1, ha2, rfl⟩ := h1; obtain ⟨hb1, hb2, rfl⟩ := h2
    obtain ⟨rfl, rfl⟩ := prepareReply_app_inj ha1 ha2 hb1 hb2 h; exact ⟨rfl, rfl, rfl⟩
  | executed mm =>
    cases m' <;> simp only [msgKindIdx] at hk <;> (try exact absurd hk (by decide))
    simp only [msgWireB, List.cons.injEq] at h1 h2
    obtain ⟨g, ⟨-, rfl⟩, h1⟩ := h1; obtain ⟨g', ⟨-, rfl⟩, h2⟩ := h2
    obtain ⟨rfl, rfl⟩ := executed_app_inj h; subst h1 h2; exact ⟨rfl, rfl, rfl⟩
  | executeOverwrite mm => simp [msgWireB] at h1

/-- Whole messages at the start of whole messages are their first ones. -/
theorem flat_prefix {ms ms' : List Msg} {bs bs' : List (List w8)}
    (h : List.Forall₂ msgWireB ms bs) (h' : List.Forall₂ msgWireB ms' bs')
    (hp : bs.flatten <+: bs'.flatten) : ms <+: ms' := by
  induction h generalizing ms' bs' with
  | nil => exact List.nil_prefix
  | @cons m b ms bs hm _ ih =>
    cases h' with
    | nil =>
      exfalso
      obtain ⟨z, hz⟩ := hp
      simp only [List.flatten_cons, List.flatten_nil, List.append_assoc,
        List.append_eq_nil_iff] at hz
      exact msgWireB_ne_nil hm hz.1
    | @cons m' b' ms' bs' hm' h'' =>
      obtain ⟨z, hz⟩ := hp
      simp only [List.flatten_cons, List.append_assoc] at hz
      obtain ⟨rfl, rfl, hz⟩ := msgWireB_app_inj hm hm' hz
      simp only [List.append_cancel_left_eq] at hz
      exact List.cons_prefix_cons.2 ⟨rfl, ih h'' ⟨z, hz⟩⟩

end Perennial.gryff.netN

namespace Perennial.gryff.netN

open model wire

variable [GooseExts]

/-- The next message after whole messages: its code and the bytes after it, comparable with
its encoding. -/
theorem flat_next {msV ms : List Msg} {bsV bs : List (List w8)} {c : w8} {D : List w8}
    (hV : List.Forall₂ msgWireB msV bsV) (hW : List.Forall₂ msgWireB ms bs)
    (hp : bsV.flatten ++ c :: D <+: bs.flatten) :
    ∃ (m1 : Msg) (e1 : List w8) (msR : List Msg), ms = msV ++ m1 :: msR ∧
      msgWireB m1 (c :: e1) ∧ (D <+: e1 ∨ e1 <+: D) := by
  induction hV generalizing ms bs with
  | nil =>
    cases hW with
    | nil => obtain ⟨z, hz⟩ := hp; simp at hz
    | @cons m1 b1 msR bsR hm1 _ =>
      obtain ⟨c1, e1, rfl, -⟩ := msgWireB_code hm1
      obtain ⟨z, hz⟩ := hp
      simp only [List.flatten_nil, List.nil_append, List.flatten_cons, List.cons_append,
        List.cons.injEq] at hz
      obtain ⟨rfl, hz⟩ := hz
      refine ⟨m1, e1, msR, rfl, hm1, ?_⟩
      have hp' : D <+: e1 ++ bsR.flatten := ⟨z, hz⟩
      rcases Nat.le_total D.length e1.length with hl | hl
      · left; exact List.prefix_of_prefix_length_le hp' (List.prefix_append _ _) hl
      · right; exact List.prefix_of_prefix_length_le (List.prefix_append _ _) hp' hl
  | @cons m b msV' bsV' hm _ ih =>
    cases hW with
    | nil =>
      exfalso; obtain ⟨z, hz⟩ := hp
      simp only [List.flatten_cons, List.flatten_nil, List.append_assoc,
        List.append_eq_nil_iff] at hz
      exact msgWireB_ne_nil hm hz.1
    | @cons m' b' ms'' bs'' hm' hW' =>
      obtain ⟨z, hz⟩ := hp
      simp only [List.flatten_cons, List.append_assoc] at hz
      obtain ⟨rfl, rfl, hz⟩ := msgWireB_app_inj hm hm' hz
      simp only [List.append_cancel_left_eq] at hz
      obtain ⟨m1, e1, msR, h1, h2, h3⟩ := ih hW' ⟨z, by rw [List.append_assoc]; exact hz⟩
      exact ⟨m1, e1, msR, by rw [h1]; rfl, h2, h3⟩

theorem msgCode_ne_beacon {m : Msg} {c : w8} (h : msgCode m = some c) :
    c ≠ W8 6 ∧ c ≠ W8 7 := by
  cases m <;> simp only [msgCode, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> decide

end Perennial.gryff.netN
