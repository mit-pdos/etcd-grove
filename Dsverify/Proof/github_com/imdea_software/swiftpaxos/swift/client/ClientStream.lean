/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/client/ClientStream.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
A client's reader over a replica's stream (`sp.outQ`, through its elimination law): the pure
part of the protocol (`sp.cw.stOk`) and the witness of the message just decoded.

* `msgOk_cKind`: a client message's witness says its hashes have 32 bytes (`is_hash_len`; an
  unfold of `sp.msgOk`, `sp.checksum`, `sp.pathHashes`, `sp.depHash`, `sp.chainHash`,
  `sp.hashOf`: a missing law of the slot);
* `rd_stOk`: what the reader has read is `stOk`;
* `rd_witness`: after the frames of `done`, the frame of `m`: `m` is the stream's next message,
  with its witness.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.ClientWire
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

-- PORT: lab imports dropped: Harness.Proof.bufio.Net

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace sp.cw

section laws
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF]
variable {γ : Names} {γc γm : GName}

instance connKind_persistent' (cid : w64) (k : ConnKind) : Persistent (connKind γ cid k) := by
  unfold connKind; infer_instance

theorem chainHash_len (xs : List CmdId) (init h : Hash) :
    chainHash init xs h ⊢ ⌜init.length = 32 → h.length = 32⌝ := by
  induction xs generalizing init with
  | nil =>
    simp only [chainHash]
    iintro %H; ipureintro; intro hl; rw [H]; exact hl
  | cons x xs ih =>
    simp only [chainHash, hashOf]
    iintro ⟨%h1, ⟨%a, %Ha, Hh⟩, Hc⟩
    ihave %Hl := sha256IsHash_len _ _ _ _ $$ Hh
    ihave %H2 := ih h1 $$ Hc
    ipureintro; intro _; exact H2 (by rw [← Ha]; exact Hl)

theorem pathHashes_ok (Ps : List (List CmdId)) (hs : List Hash) :
    pathHashes Ps hs ⊢ ⌜hashOk hs⌝ := by
  unfold pathHashes
  iintro ⟨%H, Hb⟩
  ihave %Hall : ⌜∀ (i : Nat) (P : List CmdId), Ps[i]? = some P → ∀ (h : Hash), hs[i]? = some h → h.length = 32⌝ $$ [Hb]
  · iintro %i %P %hP %h %hh
    ihave Hi := BigSepL.bigSepL_lookup hP $$ Hb
    icases Hi with ⟨%h', %Hh', Hc⟩
    rw [hh] at Hh'; cases Hh'
    ihave %Hl := startHash_len _ _ $$ Hc
    ipureintro; exact Hl
  ipureintro
  intro h hm
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
  have hlt : i < Ps.length := by
    rw [← H.1]
    rcases Nat.lt_or_ge i hs.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none_iff.mpr h'] at hi; cases hi
  exact Hall i Ps[i] (List.getElem?_eq_getElem hlt) h hi

theorem checksum_ok (Ps : List (List CmdId)) (D : List CmdId) (cs : List Hash) :
    checksum Ps D cs ⊢ ⌜hashOk cs ∧ cs ≠ []⌝ := by
  unfold checksum depHash
  iintro ⟨%hs, %d, %Hcs, Hp, Hd⟩
  ihave %H1 := pathHashes_ok _ _ $$ Hp
  ihave %H2 := chainHash_len _ _ _ $$ Hd
  ipureintro
  subst Hcs
  refine ⟨?_, by simp⟩
  intro h hm
  rcases List.mem_append.1 hm with h' | h'
  · exact H1 h h'
  · simp at h'; subst h'; exact H2 (by simp)

/-- A client message's witness: its hashes have 32 bytes. -/
theorem msgOk_cKind (cl : w32) (m : Msg) (hm : Msg.isToClient cl m) :
    msgOk γ γc γm m ⊢ ⌜cKind m⌝ := by
  cases m <;> simp only [Msg.isToClient] at hm
  · simp only [msgOk, cKind]
    iintro ⟨%D, %P, %c, -, -, -, Hc, -⟩
    ihave %H := checksum_ok $$ Hc
    ipureintro; exact H.1
  · simp only [cKind]; iintro -; ipureintro; trivial
  · simp only [msgOk, cKind]
    iintro ⟨%N, %fr, %l, %s, %Ps, %c, -, -, Hc, -⟩
    iapply checksum_ok $$ Hc

/-- The protocol of a stream to client `cl`: every prefix is `stOk`, and a message decoded
after the frames of `done` has its witness. -/
theorem outQ_frames (cid : w64) (cl : w32) (ext : List w8) :
    connKind γ cid (.client cl) ∗ outQ γ γc γm cid ext ⊢
      ∃ ms : List Msg, ⌜ext <+: framesOf ms ∧ ∀ m ∈ ms, cMsg cl m⌝ ∗
        [∗list] m ∈ ms, msgOk γ γc γm m := by
  iintro ⟨#Hk, HP⟩
  icases outQ_elim cid ext $$ HP with (%Hnil | ⟨%k', Hk', HP⟩)
  · iexists []
    isplitr
    · ipureintro; subst Hnil; simp [framesOf]
    iapply BigSepL.bigSepL_nil.2; iempintro
  ihave %Heq := connKind_agree (γ := γ) cid (ConnKind.client cl) k' $$ [$Hk $Hk']
  subst Heq
  simp only
  unfold framesProto
  icases HP with ⟨%ms, %H, Hms⟩
  haveI := msgOk_persistent (γ := γ) (γc := γc) (γm := γm)
  ihave #Hms' := Hms
  ihave %Hw : ⌜∀ m ∈ ms, cKind m⌝ $$ [Hms']
  · iintro %m %hm
    ihave Hm := (BigSepL.bigSepL_mem hm) $$ Hms'
    iapply msgOk_cKind cl m (H.2 m hm).1 $$ Hm
  iexists ms
  iframe Hms'
  ipureintro
  refine ⟨by simpa using H.1, fun m hm => ⟨(H.2 m hm).1, Hw m hm⟩⟩

end laws

section reader
variable [go_gctx : GoGlobalContext] [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable {γ : Names} {γc γm : GName}

/-- The protocol fact of what a reader over a connection has read (`recvTok_proto`). (Unfolds
the harness's `ownReader`: a missing law of `bufio`.) -/
theorem ownReader_proto (br : Loc) (rd : GoInterface) (cid : w64)
    (side : Bool) (P : Proto netDistGF) (R : List w8) :
    bufio.ownReader br rd (recvTok cid side P) R ⊢
      bufio.ownReader br rd (recvTok cid side P) R ∗
      (⌜R = []⌝ ∨ ∃ ext, ⌜R <+: ext⌝ ∗ □ P cid ext) := by
  unfold bufio.ownReader
  iintro ⟨%pend, %perr, HI, Hrep⟩
  icases recvTok_proto cid side P (R ++ pend) $$ HI with ⟨HI, #Hp⟩
  isplitl [HI Hrep]
  · iexists pend, perr; iframe
  unfold protoPrefix
  icases Hp with (%Hn | ⟨%ext, %He, #HP⟩)
  · ileft; ipureintro; exact (List.append_eq_nil_iff.1 Hn).1
  · iright; iexists ext; iframe HP; ipureintro
    exact (List.prefix_append R pend).trans He

/-- What a client's reader has read is `stOk`. -/
theorem rd_stOk (br : Loc) (rd : GoInterface) (cid : w64) (cl : w32) (R : List w8) :
    connKind γ cid (.client cl) ∗
      bufio.ownReader br rd (recvTok cid false (outQ γ γc γm)) R ⊢
      bufio.ownReader br rd (recvTok cid false (outQ γ γc γm)) R ∗ ⌜stOk cl R⌝ := by
  iintro ⟨#Hk, Hr⟩
  icases ownReader_proto br rd cid false _ R $$ Hr with ⟨Hr, Hp⟩
  iframe Hr
  icases Hp with (%Hn | ⟨%ext, %He, #HP⟩)
  · ipureintro; subst Hn; exact ⟨[], by simp [framesOf], by simp⟩
  icases outQ_frames cid cl ext $$ [$Hk $HP] with ⟨%ms, %H, -⟩
  ipureintro
  exact ⟨ms, He.trans H.1, H.2⟩

/-- **The message decoded, with its witness**: after the frames of `done` (client messages),
the frame of a client message `m`, `m` is the stream's next message: of client `cl`, with its
witness. -/
theorem rd_witness (br : Loc) (rd : GoInterface) (cid : w64) (cl : w32) (done : List Msg)
    (m : Msg) (hd : ∀ d ∈ done, cMsg cl d) (hm : cKind m) :
    connKind γ cid (.client cl) ∗
      bufio.ownReader br rd (recvTok cid false (outQ γ γc γm)) (framesOf done ++ m.frame) ⊢
      bufio.ownReader br rd (recvTok cid false (outQ γ γc γm)) (framesOf done ++ m.frame) ∗
      msgOk γ γc γm m ∗ ⌜cMsg cl m⌝ := by
  haveI := msgOk_persistent (γ := γ) (γc := γc) (γm := γm)
  iintro ⟨#Hk, Hr⟩
  icases ownReader_proto br rd cid false _ _ $$ Hr with ⟨Hr, Hp⟩
  iframe Hr
  icases Hp with (%Hn | ⟨%ext, %He, #HP⟩)
  · exfalso; simp [Msg.frame] at Hn
  icases outQ_frames cid cl ext $$ [$Hk $HP] with ⟨%ms, %H, Hms⟩
  obtain ⟨rest, rfl⟩ := frames_align hd (frames_next hd hm ⟨ms, He.trans H.1, H.2⟩) H.2
    (He.trans H.1)
  icases (BigSepL.bigSepL_append).1 $$ Hms with ⟨-, Hm⟩
  icases (BigSepL.bigSepL_cons).1 $$ Hm with ⟨Hm, -⟩
  iframe Hm
  ipureintro
  exact H.2 m (by simp)

end reader

end sp.cw

end Perennial.github_com.imdea_software.swiftpaxos
