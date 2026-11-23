/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/ConnLemmas.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The peers' handshake (P1) over the frozen protocol `sp.inP` (through its intro/elim laws):
* `peer_of_hello`: a connection whose stream starts with the peers' hello byte (0xFF) is a
  peer's (a client's stream starts with a proposal's type byte, 0);
* `hello_read`: on a peer's connection, the first 5 bytes are a hello (`helloBytes id`);
* `hello_inP`: a dialer that registered its connection as a peer's may write its hello.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.Stream

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace sp

section laws
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF] [π : NetProtoGS] [Perennial.github_com.imdea_software.swiftpaxos.sp.GobFmt]
variable {γ : Names} {γc γm : GName}

/-- A client's stream's first byte is a proposal's type byte. -/
theorem client_first_byte (cl : w32) (ext : List w8) (c : w8) (hpre : [c] <+: ext) :
    framesProto γ γc γm [] (Msg.isProposeOf cl) ext ⊢ ⌜c = W8 0⌝ := by
  unfold framesProto
  iintro ⟨%ms, %H, -⟩
  ipureintro
  obtain ⟨u, hu⟩ := hpre.trans H.1
  cases ms with
  | nil => simp [framesOf] at hu
  | cons m ms =>
    have hp := H.2 m (by simp)
    cases m <;> simp [Msg.isProposeOf] at hp
    simp [framesOf, Msg.frame, Msg.code] at hu
    exact hu.1

/-- A stream that starts with the hello byte is a peer's. -/
theorem peer_of_hello (cid : Nat) (ext : List w8) (hpre : [W8 0xFF] <+: ext) :
    inP γ γc γm cid ext ⊢ connKind γ cid .peer := by
  iintro HP
  icases inP_elim cid ext $$ HP with (%Hnil | ⟨%k', Hk', HP⟩)
  · subst Hnil; obtain ⟨u, hu⟩ := hpre; simp at hu
  cases k' with
  | peer => iexact Hk'
  | client cl =>
    ihave %Hc := client_first_byte cl ext _ hpre $$ HP
    exfalso; revert Hc; decide

/-- On a peer's connection, the first 5 bytes read are a hello. -/
theorem hello_read (cid : Nat) (ext bs : List w8) (hpre : bs <+: ext) (hl : bs.length = 5) :
    connKind γ cid .peer ∗ inP γ γc γm cid ext ⊢ ⌜∃ id, bs = helloBytes id⌝ := by
  iintro ⟨#Hk, HP⟩
  icases inP_elim cid ext $$ HP with (%Hnil | ⟨%k', Hk', HP⟩)
  · subst Hnil; obtain ⟨u, hu⟩ := hpre; simp at hu; simp [hu.1] at hl
  ihave %Heq := connKind_agree (γ := γ) cid ConnKind.peer k' $$ [$Hk $Hk']
  subst Heq
  icases HP with ⟨%id, HP⟩
  unfold framesProto
  icases HP with ⟨%ms, %H, -⟩
  ipureintro
  refine ⟨id, ?_⟩
  obtain ⟨u, hu⟩ := hpre.trans H.1
  have h5 : (helloBytes id).length = 5 := by simp [helloBytes, le32, u32Le_length]
  exact (List.append_inj hu (by rw [hl, h5])).1

/-- The dialer's hello is in `inP` on a connection it registered as a peer's. -/
theorem hello_inP (cid : Nat) (me : w32) :
    connKind γ cid .peer ⊢ inP γ γc γm cid (helloBytes me) := by
  iintro #Hk
  iapply inP_peer cid me
  iframe Hk
  unfold framesProto
  iexists []
  isplitr
  · ipureintro; simp [framesOf]
  iapply (BigSepL.bigSepL_nil_intro (P := iprop(True))); itrivial

end laws

end sp

end Perennial.github_com.imdea_software.swiftpaxos
