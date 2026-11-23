/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Client/{Base,Requested,Stream}.lean (run
gryff-bump-1, lab master 915f964; notes/dsv-gryff.md), restated for `Net/`'s connections.

The client's side of Gryff's wire protocol on its replica's port:
* `replyShape_len`, `replyShape_prefix_eq`, `replies_mem`, `repliesOk_snoc`: whole replies in a
  stream (`Client/Defs.lean`'s `replyShape`, `repliesOk`).
* `reqMsg hs req i`, `reqMsg_ok`: the request `op` writes (opcode and message, key `0`, no
  dependency `noDepV`).
* `clientReplyOk_shape`: a replica's message to a client is one whole reply.
* `reply_opDone`: a whole reply with `OK = 1` to the client's request `req`, read after whole
  replies on the connection whose dialer sent the handshake `u32Le hs`, witnesses the request's
  commit with the reply's output (`gryffWireQ`'s `acceptStream`, its client branch).
-/
module

public import Dsverify.Proof.gryff.Client.Defs
public import Dsverify.Proof.gryff.N.PeerMark

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net dsverify_lab.harness Perennial.gryff.netN
open wire.gryffproto

/-! ## Whole replies -/

section pure
variable [GooseExts]

/-- The length of a reply by its opcode. -/
def replyLen (code : w8) : Nat :=
  if code = gryffReadReply then 30 else if code = gryffWriteReply then 22 else 18

theorem ReadReply_enc_length (r : ReadReply.Msg) : (ReadReply.enc r).length = 29 := by
  simp [ReadReply.enc, Tag.enc, wire.state.Value.enc, u32Le_length, u64Le_length]

theorem WriteReply_enc_length (r : WriteReply.Msg) : (WriteReply.enc r).length = 21 := by
  simp [WriteReply.enc, Tag.enc, u32Le_length]

theorem RMWReply_enc_length (r : RMWReply.Msg) : (RMWReply.enc r).length = 17 := by
  simp [RMWReply.enc, wire.state.Value.enc, u32Le_length, u64Le_length]

theorem replyShape_len (m : List w8) (h : replyShape m) :
    ∃ code rest, m = code :: rest ∧ m.length = replyLen code := by
  rcases h with ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨r, rfl⟩
  · refine ⟨_, _, rfl, ?_⟩
    simp [replyLen, ReadReply_enc_length]
  · refine ⟨_, _, rfl, ?_⟩
    simp [replyLen, WriteReply_enc_length, gryffWriteReply, gryffReadReply]
  · refine ⟨_, _, rfl, ?_⟩
    simp [replyLen, RMWReply_enc_length, gryffWriteReply, gryffReadReply, gryffRMWReply]

/-- Two replies at the same place of a stream are the same. -/
theorem replyShape_prefix_eq {m1 m2 x y : List w8} (h1 : replyShape m1) (h2 : replyShape m2)
    (h : m1 ++ x <+: m2 ++ y) : m1 = m2 := by
  obtain ⟨c1, r1, rfl, hl1⟩ := replyShape_len m1 h1
  obtain ⟨c2, r2, rfl, hl2⟩ := replyShape_len m2 h2
  have hc : c1 = c2 := by
    obtain ⟨t, ht⟩ := h
    simp only [List.cons_append, List.cons.injEq] at ht
    exact ht.1
  subst hc
  have hlen : (c1 :: r1).length = (c1 :: r2).length := by rw [hl1, hl2]
  obtain ⟨t, ht⟩ := h
  have := congrArg (List.take (c1 :: r1).length) ht
  rw [List.append_assoc, List.take_left] at this
  rw [this, hlen, List.take_left]

/-- A whole reply read after whole replies, within a stream of whole replies, is one of the
stream's. -/
theorem replies_mem {ms1 ms2 : List (List w8)} {m : List w8}
    (h1 : ∀ x ∈ ms1, replyShape x) (h2 : ∀ x ∈ ms2, replyShape x) (hm : replyShape m)
    (h : ms1.flatten ++ m <+: ms2.flatten) : m ∈ ms2 := by
  induction ms1 generalizing ms2 with
  | nil =>
    cases ms2 with
    | nil =>
      obtain ⟨c, rest, rfl, -⟩ := replyShape_len m hm
      obtain ⟨t, ht⟩ := h
      simp at ht
    | cons m2 ms2 =>
      have := replyShape_prefix_eq (x := []) (y := ms2.flatten) hm (h2 m2 (by simp))
        (by simpa using h)
      subst this; simp
  | cons x ms1 ih =>
    cases ms2 with
    | nil =>
      obtain ⟨c, rest, rfl, -⟩ := replyShape_len x (h1 x (by simp))
      obtain ⟨t, ht⟩ := h
      simp at ht
    | cons m2 ms2 =>
      have hx := replyShape_prefix_eq (x := ms1.flatten ++ m) (y := ms2.flatten)
        (h1 x (by simp)) (h2 m2 (by simp)) (by simpa [List.append_assoc] using h)
      subst hx
      have h' : ms1.flatten ++ m <+: ms2.flatten := by
        simpa [List.append_assoc, List.prefix_append_right_inj] using h
      exact List.mem_cons_of_mem _ (ih (fun y hy => h1 y (by simp [hy]))
        (fun y hy => h2 y (by simp [hy])) h')

theorem repliesOk_snoc {R m : List w8} (hR : repliesOk R) (hm : replyShape m) :
    repliesOk (R ++ m) := by
  obtain ⟨ms, rfl, h⟩ := hR
  refine ⟨ms ++ [m], by simp, ?_⟩
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact h x hx
  · simp at hx; subst hx; exact hm

end pure

/-! ## The requests -/

section req
variable [GooseExts] [GoGlobalContext]

/-- The value of `noDep()`: key `-1`, no value. -/
def noDepV : gryff.src.gryffproto.Dep :=
  ⟨W64 (-1), ⟨W64 0, ⟨W32 0, W32 0, W32 0⟩⟩⟩

/-- Client `hs`'s request `req` for input `i`, as `op` writes it: the opcode and the message
(key `0`, no dependency). -/
def reqMsg (hs req : w32) : RegInput w64 → List w8
  | .read => gryffRead :: Read.enc ⟨req, hs, W64 0, noDepV⟩
  | .write v => gryffWrite :: Write.enc ⟨req, hs, W64 0, v, noDepV⟩
  | .cas a b => gryffRMW :: RMW.enc ⟨req, hs, W64 0, noDepV, a, b⟩

theorem reqMsg_ok (hs req : w32) (i : RegInput w64) :
    reqBytesOk hs req i (reqMsg hs req i) := by
  cases i with
  | read => exact ⟨⟨req, hs, W64 0, noDepV⟩, rfl, rfl, rfl, rfl, rfl⟩
  | write v => exact ⟨⟨req, hs, W64 0, v, noDepV⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cas a b => exact ⟨⟨req, hs, W64 0, noDepV, a, b⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end req

/-! ## Replies -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [net.Assumptions] [net.FieldAssumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- A replica's message to a client is one whole reply. -/
theorem clientReplyOk_shape (γ : GryffNames GF) (hs : w32) (m : List w8) :
    clientReplyOk γ hs m ⊢ ⌜replyShape m⌝ := by
  unfold clientReplyOk clientReplyBody
  iintro ⟨%req, %o, %hm, -⟩
  ipureintro
  unfold replyBytesD at hm
  unfold replyShape
  rcases hm with ⟨r, -, rfl, -⟩ | ⟨r, rfl, -⟩ | ⟨r, rfl, -⟩
  · exact Or.inl ⟨r, rfl⟩
  · exact Or.inr (Or.inl ⟨r, rfl⟩)
  · exact Or.inr (Or.inr ⟨r, rfl⟩)

theorem replies_shape (γ : GryffNames GF) (hs : w32) (ms : List (List w8)) :
    ([∗list] m ∈ ms, clientReplyOk γ hs m) ⊢ ⌜∀ m ∈ ms, replyShape m⌝ := by
  induction ms with
  | nil => iintro -; ipureintro; simp
  | cons x ms ih =>
    iintro H
    ihave ⟨Hx, Hms⟩ := (BigSepL.bigSepL_cons (Φ := fun _ m => clientReplyOk γ hs m)).1 $$ H
    ihave %Hx := clientReplyOk_shape γ hs x $$ Hx
    ihave %Hms := ih $$ Hms
    ipureintro
    intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact Hx
    · exact Hms m hm

/-- A whole reply with `OK = 1` read on the client's connection witnesses its request's
commit. -/
theorem reply_opDone (γ : GryffNames GF) (a : GoString) (cn : Nat) (hs req : w32)
    (o : RegOutput w64) (X R m : List w8) (hhs : hs < peerMark) (hR : repliesOk R)
    (hm : replyShape m) (hok : replyBytesOk hs req o m) :
    sentLb (Gg := hG.goose_globalGS) cn false (u32Le hs ++ X) ∗ protoPrefix (gryffWireQ γ a) cn (R ++ m) ⊢
      opDone γ.proto (sint.Z hs, sint.Z req) o := by
  iintro ⟨#Hlb, #Hp⟩
  unfold protoPrefix
  icases Hp with (%Hnil | ⟨%ext, %Hext, #HQ⟩)
  · exfalso
    obtain ⟨c0, rest, rfl, -⟩ := replyShape_len m hm
    simp at Hnil
  unfold gryffWireQ
  icases HQ with (%Hext0 | ⟨%full, %Hfull, #Hacc⟩)
  · exfalso
    obtain ⟨c0, rest, rfl, -⟩ := replyShape_len m hm
    subst Hext0
    obtain ⟨t, ht⟩ := Hext
    simp at ht
  unfold acceptStream
  icases Hacc with ⟨%hs', #Hlb', Hcase⟩
  ihave %Hcmp := sentLb_comparable cn false (u32Le hs ++ X) (u32Le hs') $$ [$Hlb $Hlb']
  have hhs' : hs = hs' := by
    apply u32Le_inj
    exact prefix_same_len_n (by simp [u32Le_length]) Hcmp
  subst hhs'
  icases Hcase with (⟨%id, %dst, %Hid, -⟩ | ⟨-, Hmsgs⟩)
  · exfalso
    rw [Hid.1] at hhs
    exact peerMark_or_ge_n id hhs
  unfold msgsOk
  icases Hmsgs with ⟨%ms, %Hms, #Hall⟩
  ihave %Hsh := replies_shape γ hs ms $$ Hall
  obtain ⟨rs, hRrs, hrs⟩ := hR
  have hmem : m ∈ ms := by
    refine replies_mem hrs Hsh hm ?_
    rw [← hRrs, ← Hms.1]
    exact Hext.trans Hfull
  ihave Hm := BigSepL.bigSepL_mem (Φ := fun x => clientReplyOk γ hs x) hmem $$ Hall
  iapply clientReplyOk_elim γ hs req o m hok $$ Hm

end laws

end Perennial.gryff
