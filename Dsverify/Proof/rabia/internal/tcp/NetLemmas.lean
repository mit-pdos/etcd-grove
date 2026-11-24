/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/tcp/NetLemmas.lean`, run
`rabia-r1wake-1`, onto `GooseLang/Ext/Net/Proto.lean`: the stream facts are the protocol's,
`protoPrefix (netP γ k) cn R` (what `rdOwn_proto` gives of a reader, one step later), not the
lab's `recvTok`.)

Lemmas of the network endpoint's routines: broadcast logs' prefixes and elements, message types,
the frames of a `netP` stream (`netP_frameIs`, `netP_read`, `netP_frameIs_hs`, `netP_read_hs`).
-/
module

public import Dsverify.Proof.rabia.internal.tcp.Hub
public import Dsverify.Proof.rabia.internal.tcp.Frames

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.rabia.internal.tcp

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode model Net rabia
  rabia.internal.message

theorem bcastPart_append (a b : List MsgV) : bcastPart (a ++ b) = bcastPart a ++ bcastPart b := by
  simp [bcastPart]

theorem bcastPart_prefix {a b : List MsgV} (h : a <+: b) : bcastPart a <+: bcastPart b := by
  obtain ⟨t, rfl⟩ := h; rw [bcastPart_append]; exact List.prefix_append _ _

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]

/-- Two handshakes' streams, one a prefix of the other, are the same server's. -/
theorem hs_prefix' {c c' : Nat} (hc : c < 128) (hc' : c' < 128) {Y F : List w8}
    (h : hsBytes c ++ Y <+: hsBytes c' ++ F) : c = c' := by
  have h1 := hsCmd_enc_len c hc
  have h2 := hsCmd_enc_len c' hc'
  have hp : model.frame (encCmd (hsCmd c)) <+: model.frame (encCmd (hsCmd c')) ++ F :=
    (List.prefix_append _ _).trans h
  have he := frame_prefix_inj h1 h2 hp
  exact hsBytes_inj c c' hc hc' (Or.inl (by simp [hsBytes, he]))

instance objOk_timeless (γ : Names) (cf : RCfg) (o : ObjV) : Timeless (objOk (GF := GF) γ cf o) := by
  unfold objOk; infer_instance
instance decObjOk_timeless (γ : Names) (cf : RCfg) (s : Nat) (d : DVal) (o : ObjV) :
    Timeless (decObjOk (GF := GF) γ cf s d o) := by unfold decObjOk; cases d <;> infer_instance
instance bmsgOk_timeless (γ : Names) (cf : RCfg) (X : Nat) (m : MsgV) :
    Timeless (bmsgOk (GF := GF) γ cf X m) := by
  unfold bmsgOk; repeat' (first | split | infer_instance)

theorem bmsgOk_notReply (γ : Names) (cf : RCfg) (X : Nat) (m : MsgV) :
    bmsgOk (GF := GF) γ cf X m ⊢ ⌜m.ty ≠ tyProposalReply⌝ := by
  unfold bmsgOk
  by_cases h : m.ty = tyProposalReply
  · have h1 : m.ty ≠ tyClientRequest := by rw [h]; decide
    have h2 : m.ty ≠ tyProposal := by rw [h]; decide
    have h3 : m.ty ≠ tyState := by rw [h]; decide
    have h4 : m.ty ≠ tyVote := by rw [h]; decide
    have h5 : m.ty ≠ tyProposalRequest := by rw [h]; decide
    have h6 : m.ty ≠ tyDecision := by rw [h]; decide
    simp only [h1, h2, h3, h4, h5, h6, ite_false]
    iintro H; iexfalso; iexact H
  · iintro -; ipureintro; exact h

theorem replyOk_ty (γ : Names) (cf : RCfg) (k : Nat) (m : MsgV) :
    replyOk (GF := GF) γ cf k m ⊢ ⌜m.ty = tyProposalReply⌝ := by
  unfold replyOk
  iintro ⟨%o, %W, %b, %h, -⟩
  ipureintro; exact h.1

theorem bcastLb_agree (γ : Names) (X : Nat) (A B : List MsgV) :
    bcastLb (GF := GF) γ X A ∗ bcastLb γ X B ⊢ ⌜A <+: B ∨ B <+: A⌝ := by
  unfold bcastLb
  iintro ⟨H1, H2⟩
  iapply mono_list_lb_valid $$ H1 H2

theorem bcastLb_prefix (γ : Names) (X : Nat) (A B : List MsgV) (h : B <+: A) :
    bcastLb (GF := GF) γ X A ⊢ bcastLb γ X B := by
  unfold bcastLb; exact monoListLbOwn_le B h

/-- An element of a prefix of server `X`'s broadcast log has its facts. -/
theorem bcast_elem (γ : Names) (cf : RCfg) (X : Nat) (hX : X < maxS) (l : List MsgV) (n : Nat)
    (m : MsgV) (h : l[n]? = some m) :
    shared (GF := GF) γ ∗ cfgIs γ.rab cf ∗ bcastLb γ X l ⊢ |={⊤}=> bmsgOk γ cf X m := by
  iintro ⟨#Hsh, #Hcf, #Hlb⟩
  unfold shared
  icases Hsh with ⟨-, #Hinvs, -, -⟩
  ihave #Hinv := (BigSepL.bigSepL_lookup (i := X) (by rw [List.getElem?_range hX])) $$ Hinvs
  unfold bcastInv
  iinv Hinv with ⟨%L, >Ha, >#Hall, >%Hro⟩ Hclose
  unfold bcastLb
  ihave %Hpre := mono_list_auth_lb_valid $$ Ha Hlb
  have hL : L[n]? = some m := Perennial.prefix_getElem? Hpre.2 h
  icases Hall with (%Hnil | ⟨%cf', #Hcf', #Hall⟩)
  · subst Hnil; simp at hL
  ihave %Heq := cfgIs_agree γ.rab cf cf' $$ [$Hcf $Hcf']
  subst Heq
  ihave #Hm := (BigSepL.bigSepL_lookup hL) $$ Hall
  imod Hclose $$ [Ha] with -
  · inext; iexists L; iframe Ha
    isplitr
    · iright; iexists cf; iframe #
    ipureintro; exact Hro
  imodintro
  iexact Hm

/-- The next frame after server `X`'s handshake and its messages `l` is a message's encoding. -/
theorem netP_frameIs (γ : Names) (k : Nat) (cid : Nat) (X : Nat) (hX : X < maxS) (l : List MsgV)
    (hl : ∀ m ∈ l, (encMsg m).length < 2 ^ 32) :
    ⊢ frameIs (netP (GF := GF) γ k) cid (hsBytes X ++ frames (l.map encMsg))
      (fun bs => ∃ m, bs = encMsg m) := by
  unfold frameIs
  iintro !> %bs %hbs Hp
  unfold protoPrefix
  icases Hp with (%Hnil | ⟨%ext, %Hext, #HQ⟩)
  · ipureintro; exfalso
    have := congrArg List.length Hnil
    simp [frame_length] at this
  have hne : ext ≠ [] := by
    intro h; subst h; have := Hext.length_le; simp [frame_length] at this
  ihave ⟨%cf', %X', %fs, %Hp, -, -⟩ := netP_hub0 γ k cid ext hne $$ HQ
  ipureintro
  obtain ⟨hX', hn', hext, hb⟩ := Hp
  have h2 := Hext.trans hext
  have hxx : X = X' := hs_prefix' (by unfold maxS at hX; omega) (by unfold maxS at hn'; omega)
    (Y := frames (l.map encMsg) ++ model.frame bs) (by simpa [List.append_assoc] using h2)
  subst hxx
  have hpre := frames_decomp_pre (pre := hsBytes X) (A := l.map encMsg) (L := fs.map encMsg)
    (b := bs) (X := []) (by simpa using hl) (by simpa using hb) hbs
    (by simpa [List.append_assoc] using h2)
  have hget := prefix_snoc_getElem hpre
  have hmem : bs ∈ fs.map encMsg := List.mem_of_getElem? hget
  obtain ⟨r, -, hr⟩ := List.mem_map.1 hmem
  exact ⟨r, hr.symm⟩

/-- The message read after server `X`'s handshake and its messages `l`: the broadcasts read are a
prefix of `B_X`; a `ProposalReply` is one to `k`. -/
theorem netP_read (γ : Names) (cf : RCfg) (k : Nat) (cid : Nat) (X : Nat) (hX : X < maxS)
    (l : List MsgV) (hl : ∀ m ∈ l, (encMsg m).length < 2 ^ 32) (m : MsgV)
    (hm : (encMsg m).length < 2 ^ 32) :
    cfgIs γ.rab cf ∗ protoPrefix (netP (GF := GF) γ k) cid
        (hsBytes X ++ frames (l.map encMsg) ++ model.frame (encMsg m)) ⊢
      bcastLb γ X (bcastPart (l ++ [m])) ∗
      (if m.ty = tyProposalReply then replyOk γ cf k m else iprop(True)) := by
  iintro ⟨#Hcf, Hp⟩
  unfold protoPrefix
  icases Hp with (%Hnil | ⟨%ext, %Hext, #HQ⟩)
  · iexfalso; ipureintro
    have := congrArg List.length Hnil
    simp [frame_length] at this
  have hne : ext ≠ [] := by
    intro h; subst h; have := Hext.length_le; simp [frame_length] at this
  ihave %Hok := cfgIs_ok γ.rab cf $$ Hcf
  ihave ⟨%X', %fs, %Hp, #Hlb, #Hreps⟩ := netP_hub γ cf k cid ext hne $$ [$Hcf $HQ]
  obtain ⟨hX', hext, hb⟩ := Hp
  have h2 := Hext.trans hext
  have hn := RCfg.n_le_maxS cf Hok
  have hxx : X = X' := hs_prefix' (by unfold maxS at hX; omega) (by unfold maxS at hn; omega)
    (Y := frames (l.map encMsg) ++ model.frame (encMsg m))
    (by simpa [List.append_assoc] using h2)
  subst hxx
  have hpre := frames_decomp_pre (pre := hsBytes X) (A := l.map encMsg) (L := fs.map encMsg)
    (b := encMsg m) (X := []) (by simpa using hl) (by simpa using hb) hm
    (by simpa [List.append_assoc] using h2)
  have hpre' : l ++ [m] <+: fs := map_prefix_of_inj (fun a b h => encMsg_inj h) (by simpa using hpre)
  isplitr
  · iapply bcastLb_prefix γ X _ _ (bcastPart_prefix hpre') $$ Hlb
  split
  · rename_i hty
    have hmem : m ∈ fs.filter (·.ty = tyProposalReply) := by
      rw [List.mem_filter]; exact ⟨hpre'.subset (by simp), by simp [hty]⟩
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hmem
    iapply (BigSepL.bigSepL_lookup hi) $$ Hreps
  · itrivial

/-- The handshake frame of a `netP` stream is a command's encoding. -/
theorem netP_frameIs_hs (γ : Names) (k : Nat) (cid : Nat) :
    ⊢ frameIs (netP (GF := GF) γ k) cid [] (fun bs => ∃ c, bs = encCmd c) := by
  unfold frameIs
  iintro !> %bs %hbs Hp
  unfold protoPrefix
  icases Hp with (%Hnil | ⟨%ext, %Hext, #HQ⟩)
  · ipureintro; exfalso
    have := congrArg List.length Hnil
    simp [frame_length] at this
  have hne : ext ≠ [] := by
    intro h; subst h; have := Hext.length_le; simp [frame_length] at this
  ihave ⟨%cf', %X', %fs, %Hp, -, -⟩ := netP_hub0 γ k cid ext hne $$ HQ
  ipureintro
  obtain ⟨hX, hn', hext, -⟩ := Hp
  have hpre : model.frame bs <+: model.frame (encCmd (hsCmd X')) ++ frames (fs.map encMsg) := by
    have := (show model.frame bs <+: ext by simpa using Hext)
    exact this.trans hext
  have := frame_prefix_inj hbs (hsCmd_enc_len X' (by unfold maxS at hn'; omega)) hpre
  exact ⟨_, this⟩

/-- After the handshake on a `netP` stream: it is server `X`'s (`X < nS`). -/
theorem netP_read_hs (γ : Names) (cf : RCfg) (k : Nat) (cid : Nat) (q : CmdV)
    (hq : (encCmd q).length < 2 ^ 32) :
    cfgIs γ.rab cf ∗ protoPrefix (netP (GF := GF) γ k) cid ([] ++ model.frame (encCmd q)) ⊢
      ⌜∃ X, X < cf.n ∧ q = hsCmd X⌝ := by
  iintro ⟨#Hcf, Hp⟩
  ihave %Hok := cfgIs_ok γ.rab cf $$ Hcf
  have hn := RCfg.n_le_maxS cf Hok
  unfold protoPrefix
  icases Hp with (%Hnil | ⟨%ext, %Hext, #HQ⟩)
  · iexfalso; ipureintro
    have := congrArg List.length Hnil
    simp [frame_length] at this
  have hne : ext ≠ [] := by
    intro h; subst h; have := Hext.length_le; simp [frame_length] at this
  ihave ⟨%X, %fs, %Hp, -, -⟩ := netP_hub γ cf k cid ext hne $$ [$Hcf $HQ]
  ipureintro
  obtain ⟨hX, hext, -⟩ := Hp
  have hpre : model.frame (encCmd q) <+: model.frame (encCmd (hsCmd X)) ++ frames (fs.map encMsg) := by
    have := (show model.frame (encCmd q) <+: ext by simpa using Hext)
    exact this.trans hext
  have he := frame_prefix_inj hq (hsCmd_enc_len X (by unfold maxS at hn; omega)) hpre
  exact ⟨X, hX, encCmd_inj he⟩

end lemmas

end Perennial.rabia.internal.tcp
