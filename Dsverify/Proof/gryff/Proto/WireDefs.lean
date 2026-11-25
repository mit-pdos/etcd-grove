/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Proto/WireDefs.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

The bodies of the client-side wire predicates (`Proto/Wire.lean`'s sealed slots, U4) and their
byte-level facts: a reply's bytes determine its request id and output.
-/
module

public import Dsverify.Proof.gryff.Proto.ClientLaws
public import Dsverify.Proof.gryff.Wire.Enc
public import GooseLang.Ext.Net.Proto

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net dsverify_lab.harness
open wire.gryffproto

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- `WireLaws.replyBytesOk`, stated before it (the same text, with the opcodes inlined). -/
def replyBytesD [GooseExts] (hs req : w32) (o : RegOutput w64) (m : List w8) : Prop :=
  (∃ (r : ReadReply.Msg) (v : w64), m = W8 25 :: ReadReply.enc r ∧ r.RequestId' = req ∧
    r.ClientId' = hs ∧ r.OK' = W8 1 ∧ r.V' = v ∧ o = .value v) ∨
  (∃ r : WriteReply.Msg, m = W8 27 :: WriteReply.enc r ∧ r.RequestId' = req ∧
    r.ClientId' = hs ∧ r.OK' = W8 1 ∧ o = .done) ∨
  (∃ r : RMWReply.Msg, m = W8 23 :: RMWReply.enc r ∧ r.RequestId' = req ∧
    r.OK' = W8 1 ∧ o = .done)

theorem u32Le_append_inj {a b : w32} {l1 l2 : List w8} (h : u32Le a ++ l1 = u32Le b ++ l2) :
    a = b ∧ l1 = l2 := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp [u32Le_length])
  exact ⟨u32Le_inj h1, h2⟩

theorem u64Le_append_inj {a b : w64} {l1 l2 : List w8} (h : u64Le a ++ l1 = u64Le b ++ l2) :
    a = b ∧ l1 = l2 := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp [u64Le_length])
  exact ⟨u64Le_inj h1, h2⟩

/-- A reply's bytes determine its request id and its output. -/
theorem replyBytesD_unique [GooseExts] {hs req1 req2 : w32} {o1 o2 : RegOutput w64}
    {m : List w8} (h1 : replyBytesD hs req1 o1 m) (h2 : replyBytesD hs req2 o2 m) :
    req1 = req2 ∧ o1 = o2 := by
  unfold replyBytesD at h1 h2
  rcases h1 with ⟨r1, v1, rfl, hq1, _, _, hv1, ho1⟩ | ⟨r1, rfl, hq1, _, _, ho1⟩ |
      ⟨r1, rfl, hq1, _, ho1⟩ <;>
    rcases h2 with ⟨r2, v2, e, hq2, _, _, hv2, ho2⟩ | ⟨r2, e, hq2, _, _, ho2⟩ |
      ⟨r2, e, hq2, _, ho2⟩ <;>
    simp only [List.cons.injEq] at e <;>
    first
    | (exact absurd e.1 (by decide))
    | skip
  · obtain ⟨-, e⟩ := e
    simp only [ReadReply.enc, wire.state.Value.enc, List.append_assoc] at e
    obtain ⟨eq, e⟩ := u32Le_append_inj e
    obtain ⟨-, e⟩ := u32Le_append_inj e
    obtain ⟨ev, -⟩ := u64Le_append_inj e
    subst hq1 hq2 ho1 ho2 hv1 hv2
    exact ⟨eq, by rw [ev]⟩
  · obtain ⟨-, e⟩ := e
    simp only [WriteReply.enc, List.append_assoc] at e
    obtain ⟨eq, -⟩ := u32Le_append_inj e
    subst hq1 hq2 ho1 ho2
    exact ⟨eq, rfl⟩
  · obtain ⟨-, e⟩ := e
    simp only [RMWReply.enc, List.append_assoc] at e
    obtain ⟨eq, -⟩ := u32Le_append_inj e
    subst hq1 hq2 ho1 ho2
    exact ⟨eq, rfl⟩

/-! ## Requests -/

/-- `WireLaws.reqBytesOk`, stated before it (the opcodes inlined). -/
def reqBytesD [GooseExts] (hs req : w32) (i : RegInput w64) (m : List w8) : Prop :=
  match i with
  | .read => ∃ r : Read.Msg, m = W8 24 :: Read.enc r ∧ r.RequestId' = req ∧
      r.ClientId' = hs ∧ r.K' = W64 0 ∧ r.D'.Key' = W64 (-1)
  | .write v => ∃ r : Write.Msg, m = W8 26 :: Write.enc r ∧ r.RequestId' = req ∧
      r.ClientId' = hs ∧ r.K' = W64 0 ∧ r.V' = v ∧ r.D'.Key' = W64 (-1)
  | .cas o n => ∃ r : RMW.Msg, m = W8 22 :: RMW.enc r ∧ r.RequestId' = req ∧
      r.ClientId' = hs ∧ r.K' = W64 0 ∧ r.OldValue' = o ∧ r.NewValue' = n ∧
      r.D'.Key' = W64 (-1)

/-- `WireLaws.reqShape`, stated before it. -/
def reqShapeD [GooseExts] (code : w8) (m : List w8) : Prop :=
  (code = W8 24 ∧ ∃ r : Read.Msg, m = code :: Read.enc r) ∨
  (code = W8 26 ∧ ∃ r : Write.Msg, m = code :: Write.enc r) ∨
  (code = W8 22 ∧ ∃ r : RMW.Msg, m = code :: RMW.enc r)

/-- A request's length, from its opcode. -/
def reqLen (code : w8) : Nat :=
  if code = W8 24 then 45 else if code = W8 26 then 53 else 61

theorem reqShapeD_len [GooseExts] {code : w8} {m : List w8} (h : reqShapeD code m) :
    m.length = reqLen code ∧ m.head? = some code := by
  rcases h with ⟨rfl, r, rfl⟩ | ⟨rfl, r, rfl⟩ | ⟨rfl, r, rfl⟩ <;>
    simp [reqLen, Read.enc, Write.enc, RMW.enc, Dep.enc, ValTag.enc, Tag.enc,
      wire.state.Key.enc, wire.state.Value.enc, u32Le_length, u64Le_length]

theorem reqBytesD_shape [GooseExts] {hs req : w32} {i : RegInput w64} {m : List w8}
    (h : reqBytesD hs req i m) : ∃ c, reqShapeD c m := by
  cases i with
  | read => obtain ⟨r, rfl, _⟩ := h; exact ⟨_, Or.inl ⟨rfl, r, rfl⟩⟩
  | write v => obtain ⟨r, rfl, _⟩ := h; exact ⟨_, Or.inr (Or.inl ⟨rfl, r, rfl⟩)⟩
  | cas o n => obtain ⟨r, rfl, _⟩ := h; exact ⟨_, Or.inr (Or.inr ⟨rfl, r, rfl⟩)⟩

/-- Requests are self-delimiting: of two requests at the start of the same bytes, each is the
other. -/
theorem reqShapeD_split [GooseExts] {c1 c2 : w8} {x1 x2 r1 r2 : List w8}
    (h1 : reqShapeD c1 x1) (h2 : reqShapeD c2 x2) (h : x1 ++ r1 = x2 ++ r2) :
    x1 = x2 ∧ r1 = r2 := by
  obtain ⟨l1, hd1⟩ := reqShapeD_len h1
  obtain ⟨l2, hd2⟩ := reqShapeD_len h2
  have hc : c1 = c2 := by
    cases x1 with
    | nil => simp at hd1
    | cons a x1 =>
      cases x2 with
      | nil => simp at hd2
      | cons b x2 =>
        simp only [List.head?_cons, Option.some.injEq] at hd1 hd2
        simp only [List.cons_append, List.cons.injEq] at h
        rw [← hd1, ← hd2, h.1]
  subst hc
  exact List.append_inj h (l1.trans l2.symm)

/-- Whole requests at the start of the bytes of whole requests are their first messages. -/
theorem reqs_flatten_prefix [GooseExts] :
    ∀ (A B : List (List w8)) (rest : List w8), (∀ x ∈ A, ∃ c, reqShapeD c x) →
      (∀ y ∈ B, ∃ c, reqShapeD c y) → A.flatten ++ rest = B.flatten → A <+: B
  | [], _, _, _, _, _ => List.nil_prefix
  | x :: A, [], rest, hA, _, h => by
    obtain ⟨c, hc⟩ := hA x (List.mem_cons_self ..)
    obtain ⟨hl, _⟩ := reqShapeD_len hc
    have : x.length = 0 := by
      have := congrArg List.length h
      simp only [List.flatten_cons, List.append_assoc, List.length_append, List.flatten_nil,
        List.length_nil] at this
      omega
    exfalso
    unfold reqLen at hl
    split at hl
    · omega
    · split at hl <;> omega
  | x :: A, y :: B, rest, hA, hB, h => by
    obtain ⟨c, hc⟩ := hA x (List.mem_cons_self ..)
    obtain ⟨d, hd⟩ := hB y (List.mem_cons_self ..)
    simp only [List.flatten_cons, List.append_assoc] at h
    obtain ⟨rfl, h'⟩ := reqShapeD_split hc hd h
    exact (List.prefix_cons_inj x).2 (reqs_flatten_prefix A B rest
      (fun z hz => hA z (List.mem_cons_of_mem _ hz)) (fun z hz => hB z (List.mem_cons_of_mem _ hz)) h')

/-- A request's bytes determine its id. -/
theorem reqBytesD_id [GooseExts] {hs r1 r2 : w32} {i1 i2 : RegInput w64} {m : List w8}
    (h1 : reqBytesD hs r1 i1 m) (h2 : reqBytesD hs r2 i2 m) : r1 = r2 := by
  have key : ∀ {c : w8} {a b : w32} {l1 l2 : List w8}, c :: (u32Le a ++ l1) = c :: (u32Le b ++ l2) →
      a = b := fun h => (u32Le_append_inj (List.cons.inj h).2).1
  cases i1 <;> cases i2 <;> simp only [reqBytesD] at h1 h2 <;>
    obtain ⟨q1, e1, hq1, _⟩ := h1 <;> obtain ⟨q2, e2, hq2, _⟩ := h2 <;>
    rw [e1] at e2 <;> simp only [List.cons.injEq] at e2 <;>
    first
    | exact absurd e2.1 (by decide)
    | (subst hq1 hq2
       simp only [Read.enc, Write.enc, RMW.enc, List.append_assoc] at e2
       exact (u32Le_append_inj e2.2).1)

/-- The pure core of `clientReqsOk_elim`: a request read after whole requests is the next
registered one, with a greater id than those before it. -/
theorem reqs_elim_pure [GooseExts] (hs : w32) (ms : List (w32 × RegInput w64 × List w8))
    (ms' : List (List w8)) (code : w8) (m post : List w8)
    (hbody : ms'.flatten ++ m ++ post = (ms.map (fun x => x.2.2)).flatten)
    (hok : ∀ x ∈ ms, reqBytesD hs x.1 x.2.1 x.2.2)
    (hsort : (ms.map (fun x => sint.Z x.1)).Pairwise (· < ·))
    (hpre : ∀ x ∈ ms', ∃ c, reqShapeD c x) (hm : reqShapeD code m) :
    ∃ x, ms[ms'.length]? = some x ∧ x.2.2 = m ∧
      ∀ y ∈ ms', ∀ r j, reqBytesD hs r j y → sint.Z r < sint.Z x.1 := by
  let B := ms.map (fun x => x.2.2)
  have hA : ms' ++ [m] <+: B := by
    refine reqs_flatten_prefix (ms' ++ [m]) B post ?_ ?_ ?_
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hpre x hx
      · simp only [List.mem_singleton] at hx; subst hx; exact ⟨code, hm⟩
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      exact reqBytesD_shape (hok x hx)
    · simpa [List.flatten_append, List.append_assoc] using hbody
  obtain ⟨C, hC⟩ := hA
  have hBn : B[ms'.length]? = some m := by
    rw [← hC]; simp
  have hBk : ∀ k (hk : k < ms'.length), B[k]? = some ms'[k] := by
    intro k hk; rw [← hC]; simp [List.getElem?_append_left hk, hk]
  simp only [B, List.getElem?_map] at hBn
  cases hx : ms[ms'.length]? with
  | none => rw [hx] at hBn; simp at hBn
  | some x =>
    rw [hx] at hBn
    simp only [Option.map_some, Option.some.injEq] at hBn
    refine ⟨x, rfl, hBn, ?_⟩
    intro y hy r j hr
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
    have hBk' := hBk k hk
    simp only [B, List.getElem?_map] at hBk'
    cases hz : ms[k]? with
    | none => rw [hz] at hBk'; simp at hBk'
    | some z =>
      rw [hz] at hBk'
      simp only [Option.map_some, Option.some.injEq] at hBk'
      have hzmem : z ∈ ms := List.mem_of_getElem? hz
      have := reqBytesD_id hr (hBk' ▸ hok z hzmem)
      subst this
      have hkn : k < ms'.length := hk
      have hlt := List.pairwise_iff_getElem.1 hsort k ms'.length
        (by simp; exact (List.getElem?_eq_some_iff.1 hz).1)
        (by simp; exact (List.getElem?_eq_some_iff.1 hx).1) hkn
      simp only [List.getElem_map] at hlt
      have e1 : ms[k]'(by exact (List.getElem?_eq_some_iff.1 hz).1) = z :=
        (List.getElem?_eq_some_iff.1 hz).2
      have e2 : ms[ms'.length]'(by exact (List.getElem?_eq_some_iff.1 hx).1) = x :=
        (List.getElem?_eq_some_iff.1 hx).2
      rw [e1, e2] at hlt
      exact hlt

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- `clientReqsOk`'s body: whole requests of client `hs`, each registered, with increasing
non-negative ids (N-8) up to `last`. -/
def clientReqsBody (γ : GryffNames GF) (hs : w32) (last : Int) (body : List w8) :
    IProp GF :=
  iprop(∃ ms : List (w32 × RegInput w64 × List w8),
    ⌜body = (ms.map (fun x => x.2.2)).flatten ∧ (∀ x ∈ ms, reqBytesD hs x.1 x.2.1 x.2.2) ∧
      (ms.map (fun x => sint.Z x.1)).Pairwise (· < ·) ∧ (∀ x ∈ ms, sint.Z x.1 ≤ last) ∧
      (∀ x ∈ ms, 0 ≤ sint.Z x.1)⌝ ∗
    [∗list] x ∈ ms, opReg γ.proto (sint.Z hs, sint.Z x.1) x.2.1)

/-- `clientReplyOk`'s body: a reply with `OK = 1` to one of client `hs`'s requests, whose
operation is linearized with the reply's output. -/
def clientReplyBody (γ : GryffNames GF) (hs : w32) (m : List w8) : IProp GF :=
  iprop(∃ (req : w32) (o : RegOutput w64), ⌜replyBytesD hs req o m⌝ ∗
    opDone γ.proto (sint.Z hs, sint.Z req) o)

instance clientReplyBody_persistent (γ : GryffNames GF) (hs : w32) (m : List w8) :
    Persistent (clientReplyBody γ hs m) := by
  unfold clientReplyBody
  have := fun (req : w32) (o : RegOutput w64) =>
    opDone_persistent (GF := GF) γ.proto (sint.Z hs, sint.Z req) o
  infer_instance

end

end Perennial.gryff
