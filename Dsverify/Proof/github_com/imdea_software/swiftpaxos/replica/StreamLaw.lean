/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/StreamLaw.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The stream law a replica's peer reader gives the `Unmarshal` of a table message
(`sp.unmarshalOk`): after the frames of `done` and a type byte `c`, whatever the reader returns
next is a prefix of a well-formed message's body of type `c` (`sp.nextOk c`), by the protocol
(`framesProto`: a stream is a prefix of the frames of well-formed messages).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.Defs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace sp

/-- After the frames of `done`, a type byte `c` and bytes `d`, in a prefix of the frames of the
well-formed `ms`: `d` is a prefix of a well-formed message's body of type `c`. -/
theorem frames_nextOk_pure {ok : Msg → Prop} {done ms : List Msg} {c : w8} {d : List w8}
    (hd : ∀ x ∈ done, x.wf) (hms : ∀ x ∈ ms, x.wf ∧ ok x)
    (h : framesOf done ++ c :: d <+: framesOf ms) :
    ∃ (m : Msg) (w : List w8), m.wf ∧ ok m ∧ m.code = c ∧ d <+: m.body ++ w := by
  obtain ⟨u, hu⟩ := h
  induction done generalizing ms with
  | nil =>
    cases ms with
    | nil => simp [framesOf] at hu
    | cons b ms =>
      simp only [framesOf, List.map_nil, List.flatten_nil, List.nil_append, List.map_cons,
        List.flatten_cons, Msg.frame, List.cons_append, List.cons.injEq] at hu
      exact ⟨b, framesOf ms, (hms b (by simp)).1, (hms b (by simp)).2, hu.1.symm, u,
        by simpa [framesOf, List.append_assoc] using hu.2⟩
  | cons x done ih =>
    cases ms with
    | nil => simp [framesOf, Msg.frame] at hu
    | cons b ms =>
      simp only [framesOf, List.map_cons, List.flatten_cons, List.append_assoc] at hu
      obtain ⟨hdb, h2⟩ := frame_peel (hd x (by simp)) (hms b (by simp)).1 hu
      subst hdb
      exact ih (fun z hz => hd z (List.mem_cons_of_mem _ hz))
        (fun z hz => hms z (List.mem_cons_of_mem _ hz))
        (by simp only [framesOf, List.append_assoc]; exact h2)

section laws
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF] [π : NetProtoGS]
variable {γ : Names} {γc γm : GName}

/-- The next message's bytes of a stream whose kind the reader knows. -/
theorem stream_nextOk (k : RdKind) (hk : ∀ m, k.ok m → m.isPeer) (cid : Nat) (ext : List w8)
    (done : List Msg) (c : w8)
    (d : List w8) (hpre : k.head ++ framesOf done ++ c :: d <+: ext) (hd : ∀ x ∈ done, x.wf) :
    connKind γ cid k.conn ∗ k.proto γ γc γm cid ext ⊢ ⌜nextOk c d⌝ := by
  iintro ⟨#Hk, HP⟩
  have key : ∀ (head : List w8) (ok : Msg → Prop) (bs : List w8),
      (∀ m, ok m → m.isPeer) → head ++ framesOf done ++ c :: d <+: bs →
      framesProto γ γc γm head ok bs ⊢ ⌜nextOk c d⌝ := by
    intro head ok bs hok hb
    iintro HP
    icases framesProto_wf _ _ _ $$ HP with ⟨%ms, %H, -⟩
    ipureintro
    have h2 := hb.trans H.1
    simp only [List.append_assoc] at h2
    have h3 := (List.prefix_append_right_inj head).1 h2
    obtain ⟨m, w, hw, hm, hc, hp⟩ := frames_nextOk_pure (ok := ok) hd
      (fun x hx => ⟨(H.2 x hx).2, (H.2 x hx).1⟩) h3
    exact ⟨m, w, hw, hok m hm, hc, hp⟩
  cases k with
  | peerIn id =>
    simp only [RdKind.proto, RdKind.conn, RdKind.head, RdKind.ok] at hpre hk ⊢
    icases inP_elim cid ext $$ HP with (%Hnil | ⟨%k', Hk', HP⟩)
    · subst Hnil; obtain ⟨u, hu⟩ := hpre; simp [helloBytes] at hu
    ihave %Heq := connKind_agree (γ := γ) cid ConnKind.peer k' $$ [$Hk $Hk']
    subst Heq
    icases HP with ⟨%id', HP⟩
    ihave %Hid : ⌜id' = id⌝ $$ [HP]
    · unfold framesProto
      icases HP with ⟨%ms, %H, -⟩
      ipureintro
      have h2 := hpre.trans H.1
      simp only [List.append_assoc] at h2
      exact (hello_prefix h2).symm
    subst Hid
    iapply key _ _ ext hk hpre $$ HP
  | peerOut =>
    simp only [RdKind.proto, RdKind.conn, RdKind.head, RdKind.ok] at hpre hk ⊢
    icases outQ_elim cid ext $$ HP with (%Hnil | ⟨%k', Hk', HP⟩)
    · subst Hnil; obtain ⟨u, hu⟩ := hpre; simp at hu
    ihave %Heq := connKind_agree (γ := γ) cid ConnKind.peer k' $$ [$Hk $Hk']
    subst Heq
    iapply key [] _ ext hk hpre $$ HP
  | client cl =>
    simp only [RdKind.proto, RdKind.conn, RdKind.head, RdKind.ok] at hpre hk ⊢
    icases inP_elim cid ext $$ HP with (%Hnil | ⟨%k', Hk', HP⟩)
    · subst Hnil; obtain ⟨u, hu⟩ := hpre; simp at hu
    ihave %Heq := connKind_agree (γ := γ) cid (ConnKind.client cl) k' $$ [$Hk $Hk']
    subst Heq
    iapply key [] _ ext hk hpre $$ HP

end laws

section reader
variable [go_gctx : GoGlobalContext] [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS]
variable {γ : Names} {γc γm : GName}

/-- **The peer reader's stream law** after the frames of `done` and the type byte `c`. -/
theorem reader_streamLaw (br : Loc) (rd : GoInterface) (k : RdKind)
    (hk : ∀ m, k.ok m → m.isPeer) (cid : Nat)
    (done : List Msg) (R : List w8) (c : w8) (hR : R = k.head ++ framesOf done)
    (hd : ∀ x ∈ done, x.wf) :
    connKind γ cid k.conn ⊢
      streamLaw br rd (recvTokL cid k.side (k.proto γ γc γm)) (R ++ [c]) (nextOk c) := by
  subst hR
  iintro #Hk
  unfold streamLaw
  imodintro
  iintro %d Hrd
  icases ownReader_proto br rd cid k.side _ _ $$ Hrd with ⟨Hrd, Hp⟩
  iframe Hrd
  inext
  icases Hp with (%Hnil | ⟨%ext, %Hext, #HP⟩)
  · simp at Hnil
  iapply stream_nextOk k hk cid ext done c d (by simpa [List.append_assoc] using Hext) hd $$
    [$Hk $HP]

end reader

end sp

end Perennial.github_com.imdea_software.swiftpaxos
