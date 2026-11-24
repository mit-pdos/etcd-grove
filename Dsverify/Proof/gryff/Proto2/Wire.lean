/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Proto2/Wire.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Stage 2's peer streams (replacing stage 1's per-message `peerMsgOk`): what replica id `k` writes
to replica id `q` on their connection is a prefix of the wire encodings of `k`'s stream of model
messages to `q` (`streamOf k q t` for a trace `t` that `k`'s real trace extends), and carries `k`'s
prediction (`predIdIs`; the dialer's handshake is enough to learn it). `Proto/Wire.lean`'s
`dialStream` and `acceptStream` use `peerStreamOk` in their peer branches.

* `msgWire m b` (sealed: unit N's): the bytes `b` are a message of the kind of `m` as
  `SendMsg` writes it, its opcode (the rpc code the replica registered for the kind) then its Go
  struct's encoding (`Wire/Enc.lean`), whose fields the model keeps (`Model/Msg.lean`) are `m`'s.
* Self-messages (`k = q`) go through the replica's Go channels, not bytes: only the receive
  tokens (`Proto2/Laws.lean`, `recv_msg` with `k = q`) are used.
-/
module

public import Dsverify.Proof.gryff.Proto2.InvDefs
public import Dsverify.Proof.gryff.N.WireLaws

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode proto
open model kahn pure

variable [GooseExts]

/-- The bytes `b` are model message `m` on the wire (sealed: unit N defines it from
`Wire/Enc.lean`'s encodings and the rpc codes; see the module header). -/
@[irreducible] def msgWire (_m : Msg) (_b : List w8) : Prop := netN.msgWireB _m _b

theorem msgWire_eq : msgWire = netN.msgWireB := by
  funext m b; unfold msgWire; rfl

/-- The bytes `W` are the messages `ms`, in order. -/
def msgsWire (ms : List Msg) (W : List w8) : Prop :=
  ∃ bs : List (List w8), List.Forall₂ msgWire ms bs ∧ W = bs.flatten

/-- A replica id from a wire id (`peerRole_ids`: the peers' ids are below 3). -/
def rid3 (x : w32) : Fin 3 := ⟨x.toNat % 3, Nat.mod_lt _ (by decide)⟩

/-- (Sealed slot's law, unit N.) Messages are self-delimiting on the wire: whole messages at
the start of whole messages are their first ones. -/
theorem msgsWire_prefix {ms ms' : List Msg} {W W' : List w8} (h : msgsWire ms W)
    (h' : msgsWire ms' W') (hp : W <+: W') : ms <+: ms' := by
  obtain ⟨bs, hbs, rfl⟩ := h
  obtain ⟨bs', hbs', rfl⟩ := h'
  rw [msgWire_eq] at hbs hbs'
  exact netN.flat_prefix hbs hbs' hp

/-- (Sealed slot's law, unit N.) A message's bytes are not empty. -/
theorem msgWire_ne_nil {m : Msg} {b : List w8} (h : msgWire m b) : b ≠ [] := by
  rw [msgWire_eq] at h
  exact netN.msgWireB_ne_nil h

theorem forall₂_snoc {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β} {a : α} {b : β}, List.Forall₂ R l1 l2 → R a b →
      List.Forall₂ R (l1 ++ [a]) (l2 ++ [b])
  | [], [], _, _, .nil, h => .cons h .nil
  | _ :: _, _ :: _, _, _, .cons h1 h2, h => .cons h1 (forall₂_snoc h2 h)

theorem msgsWire_snoc {ms : List Msg} {m : Msg} {W b : List w8} (hW : msgsWire ms W)
    (hb : msgWire m b) : msgsWire (ms ++ [m]) (W ++ b) := by
  obtain ⟨bs, h1, rfl⟩ := hW
  exact ⟨bs ++ [b], forall₂_snoc h1 hb, by simp⟩

section
variable [GooseExts] {GF : BundledGFunctors} [AllG GF] [InvGS_gen .hasLC GF]

/-- What replica id `k` writes to `q`: a prefix of the encodings of `k`'s stream to `q`, with
`k`'s prediction (persistent). -/
def peerStreamOk (γ : ProtoNames) (k q : Fin 3) (W : List w8) : IProp GF :=
  iprop((∃ ws, predIdIs γ k ws) ∗
    ∃ (t : List Ev) (ms : List Msg) (W' : List w8), traceLb γ k t ∗
      ⌜ms <+: streamOf k q t ∧ msgsWire ms W' ∧ W <+: W'⌝)

instance peerStreamOk_persistent (γ : ProtoNames) (k q : Fin 3) (W : List w8) :
    Persistent (peerStreamOk (GF := GF) γ k q W) := by
  unfold peerStreamOk; infer_instance

/-- **Send** (`SendMsg`'s proof, under replica `k`'s lock after `replica_step`): with the first
`ms` of `k`'s stream to `q` on the wire, the next one `m` (its trace's lower bound from the step)
may follow. -/
theorem peerStream_send (γ : ProtoNames) (k q : Fin 3) (ws : List w64) (t : List Ev)
    (ms : List Msg) (m : Msg) (W b : List w8) (hpre : ms ++ [m] <+: streamOf k q t)
    (hW : msgsWire ms W) (hb : msgWire m b) :
    predIdIs (GF := GF) γ k ws ∗ traceLb γ k t ⊢ peerStreamOk γ k q (W ++ b) := by
  unfold peerStreamOk
  iintro ⟨#Hp, #Ht⟩
  isplitl
  · iexists ws; iexact Hp
  iexists t, ms ++ [m], W ++ b
  iframe Ht
  ipureintro
  exact ⟨hpre, msgsWire_snoc hW hb, List.prefix_refl _⟩

/-- **Receive** (the listener's proof): whole messages `ms` read from what `k` wrote to `q` are
the first ones of `k`'s stream to `q`. -/
theorem peerStream_recv (γ : ProtoNames) (k q : Fin 3) (ms : List Msg) (V W : List w8)
    (hV : msgsWire ms V) (hVW : V <+: W) :
    peerStreamOk (GF := GF) γ k q W ⊢ streamLb γ k q ms := by
  unfold peerStreamOk streamLb
  iintro ⟨-, %t, %ms', %W', #Ht, %h⟩
  obtain ⟨h1, h2, h3⟩ := h
  iexists t
  iframe Ht
  ipureintro
  exact (msgsWire_prefix hV h2 (hVW.trans h3)).trans h1

/-- The sender's prediction, from any of its bytes (the handshake suffices). -/
theorem peerStream_pred (γ : ProtoNames) (k q : Fin 3) (W : List w8) :
    peerStreamOk (GF := GF) γ k q W ⊢ ∃ ws, predIdIs γ k ws := by
  unfold peerStreamOk
  iintro ⟨H, -⟩
  iexact H

/-- Prefix-closed. -/
theorem peerStream_prefix (γ : ProtoNames) (k q : Fin 3) (W W' : List w8) (h : W' <+: W) :
    peerStreamOk (GF := GF) γ k q W ⊢ peerStreamOk γ k q W' := by
  unfold peerStreamOk
  iintro ⟨H, %t, %ms, %W'', #Ht, %h1⟩
  iframe H
  iexists t, ms, W''
  iframe Ht
  ipureintro
  exact ⟨h1.1, h1.2.1, h.trans h1.2.2⟩

/-- The handshake (no message yet): the sender's prediction, with an update (hub request R-I-3;
stage 1's update-free `peerStream_nil` removed). -/
theorem peerStream_nil_upd (γ : ProtoNames) (k q : Fin 3) (ws : List w64) :
    predIdIs (GF := GF) γ k ws ⊢ |==> peerStreamOk γ k q [] := by
  unfold peerStreamOk
  iintro #Hp
  imod monoListLbOwn_nil (GF := GF) (A := Ev) (γ.s2.trace k) with #Hlb
  imodintro
  isplitl
  · iexists ws; iexact Hp
  iexists [], [], []
  unfold traceLb
  iframe Hlb
  ipureintro
  exact ⟨List.nil_prefix, ⟨[], .nil, rfl⟩, List.prefix_refl _⟩

end

end Perennial.gryff
