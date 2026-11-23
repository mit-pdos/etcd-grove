/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/tcp/ProtoLemmas.lean`, run
`rabia-r1wake-1`, onto `GooseLang/Ext/Net/Proto.lean`.)

Lemmas on the protocols of `Core/Proto.lean` and `Net`'s connection tokens, for tcp's proofs:
the protocols' persistence and prefix closure (`ProtoPrefixClosed`, what `net.conn_streamWriterOk`
asks), the sent bytes' laws `sentLb_prefix`, `sentLb_agree` (from `Proto.lean`'s definitions:
missing laws there, as the lab's were of its harness), `recvTokL_sentLb` and its reader form
`rdOwn_sentLb` (what a connection's reader has returned was sent), the handshakes' injectivity.
-/
module

public import Dsverify.Proof.rabia.internal.tcp.Basics

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.rabia.internal.tcp

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode model Net rabia

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]

instance estab_persistent (γ : Names) (c k : Nat) (cid : Nat) :
    Persistent (estab (GF := GF) γ c k cid) := by unfold estab; infer_instance
instance reqOk_persistent (γ : Names) (c : Nat) (q : CmdV) :
    Persistent (reqOk (GF := GF) γ c q) := by unfold reqOk; infer_instance
instance repOk_persistent (γ : Names) (c : Nat) (q : CmdV) :
    Persistent (repOk (GF := GF) γ c q) := by unfold repOk; infer_instance
instance objOk_persistent (γ : Names) (cf : RCfg) (o : ObjV) :
    Persistent (objOk (GF := GF) γ cf o) := by unfold objOk; infer_instance
instance replyOk_persistent (γ : Names) (cf : RCfg) (k : Nat) (m : MsgV) :
    Persistent (replyOk (GF := GF) γ cf k m) := by unfold replyOk; infer_instance
instance decObjOk_persistent (γ : Names) (cf : RCfg) (s : Nat) (d : DVal) (o : ObjV) :
    Persistent (decObjOk (GF := GF) γ cf s d o) := by unfold decObjOk; cases d <;> infer_instance
instance bmsgOk_persistent (γ : Names) (cf : RCfg) (X : Nat) (m : MsgV) :
    Persistent (bmsgOk (GF := GF) γ cf X m) := by
  unfold bmsgOk; repeat' (first | split | infer_instance)
instance bcastLb_persistent (γ : Names) (X : Nat) (l : List MsgV) :
    Persistent (bcastLb (GF := GF) γ X l) := by unfold bcastLb; infer_instance
instance proxyP_persistent (γ : Names) (k : Nat) (cid : Nat) (W : List w8) :
    Persistent (proxyP (GF := GF) γ k cid W) := by unfold proxyP; infer_instance
instance proxyQ_persistent (γ : Names) (k : Nat) (cid : Nat) (W : List w8) :
    Persistent (proxyQ (GF := GF) γ k cid W) := by unfold proxyQ; infer_instance
instance netP_persistent (γ : Names) (k : Nat) (cid : Nat) (W : List w8) :
    Persistent (netP (GF := GF) γ k cid W) := by unfold netP; infer_instance

/-- A prefix of sent bytes was sent (`Proto.lean`'s `sentLb`, `wLb_le`). -/
theorem sentLb_prefix (cn : Nat) (s : Bool) (W W' : List w8) (h : W' <+: W) :
    sentLb (Gg := hG.goose_globalGS) cn s W ⊢ sentLb (Gg := hG.goose_globalGS) cn s W' := by
  unfold sentLb
  iintro ⟨%γ, #He, #Hlb⟩
  iexists γ
  iframe He
  iapply wLb_le _ W' h $$ Hlb

/-- Two prefixes of what a writer wrote are comparable. -/
theorem sentLb_agree (cn : Nat) (s : Bool) (A B : List w8) :
    sentLb (Gg := hG.goose_globalGS) cn s A ∗ sentLb (Gg := hG.goose_globalGS) cn s B ⊢
      ⌜A <+: B ∨ B <+: A⌝ := by
  unfold sentLb
  iintro ⟨⟨%γ1, #He1, #H1⟩, ⟨%γ2, #He2, #H2⟩⟩
  icases connElem_agree cn γ1 γ2 $$ He1 He2 with %h
  subst h
  unfold wLb
  iapply mono_list_lb_valid $$ H1 H2

/-- What a reader has read was written by the other end (`recvTok_sentLb`, for `recvTokL`). -/
theorem recvTokL_sentLb (cn : Nat) (s : Bool) (P : Proto GF) (R : List w8) :
    recvTokL (Gg := hG.goose_globalGS) cn s P R ⊢
      recvTokL (Gg := hG.goose_globalGS) cn s P R ∗ sentLb (Gg := hG.goose_globalGS) cn (!s) R := by
  refine persistent_entails_left ?_
  unfold recvTokL recvCore sentLb connH
  iintro ⟨⟨%γ, %Pd, %Pa, ⟨#He, -⟩, -, -, #Hlb⟩, -⟩
  iexists γ
  iframe He Hlb

/-- What a connection's reader has returned was written by the other end. -/
theorem rdOwn_sentLb [_root_.Perennial.bufio.Assumptions] (br : Loc) (cn : Nat) (s : Bool)
    (P : Proto GF) (R : List w8) :
    rdOwn br cn s P R ⊢ rdOwn br cn s P R ∗ sentLb (Gg := hG.goose_globalGS) cn (!s) R := by
  unfold rdOwn
  iintro ⟨%ri, %E, H⟩
  ihave ⟨H, #Hlb⟩ := EtcdGrove.bufio.ownBufReader_fact br ri rabia.internal.message.connPre _ E R
    (fun r => sentLb (Gg := hG.goose_globalGS) cn (!s) r) (fun r => recvTokL_sentLb cn s P r)
    (fun x y => sentLb_prefix cn (!s) (x ++ y) x (List.prefix_append x y)) $$ H
  iframe Hlb
  iexists ri, E
  iexact H

theorem proxyP_closed (γ : Names) (k : Nat) : ProtoPrefixClosed (GF := GF) (proxyP γ k) where
  nil cn := by
    unfold proxyP
    iintro !>
    ileft; ipureintro; rfl
  pre cn x y h := by
    unfold proxyP
    iintro #H
    imodintro
    icases H with (%Hn | ⟨%cf, %c, %qs, #Hcf, %Hp, #Hest, #Hreq⟩)
    · ileft; ipureintro; subst Hn; exact List.prefix_nil.mp h
    iright
    iexists cf, c, qs
    iframe Hcf Hest Hreq
    ipureintro
    obtain ⟨h1, h2, h3, h4⟩ := Hp
    exact ⟨h1, h2, h.trans h3, h4⟩

theorem proxyQ_closed (γ : Names) (k : Nat) : ProtoPrefixClosed (GF := GF) (proxyQ γ k) where
  nil cn := by
    unfold proxyQ
    iintro !>
    ileft; ipureintro; rfl
  pre cn x y h := by
    unfold proxyQ
    iintro #H
    imodintro
    icases H with (%Hn | ⟨%c, %rs, #Hs, %Hp, #Hrep⟩)
    · ileft; ipureintro; subst Hn; exact List.prefix_nil.mp h
    iright
    iexists c, rs
    iframe Hs Hrep
    ipureintro
    exact ⟨Hp.1, h.trans Hp.2.1, Hp.2.2⟩

theorem netP_closed (γ : Names) (k : Nat) : ProtoPrefixClosed (GF := GF) (netP γ k) where
  nil cn := by
    unfold netP
    iintro !>
    ileft; ipureintro; rfl
  pre cn x y h := by
    unfold netP
    iintro #H
    imodintro
    icases H with (%Hn | ⟨%cf, %X, %fs, #Hcf, %Hp, #Hb, #Hr⟩)
    · ileft; ipureintro; subst Hn; exact List.prefix_nil.mp h
    iright
    iexists cf, X, fs
    iframe Hcf Hb Hr
    ipureintro
    exact ⟨Hp.1, h.trans Hp.2.1, Hp.2.2⟩

theorem noneP_closed : ProtoPrefixClosed (GF := GF) noneP :=
  ProtoPrefixClosed.of_pure (fun _ W => W = []) (fun _ => rfl)
    (fun _ a b h hb => by subst hb; exact List.prefix_nil.mp h)

theorem maxS_cases (k : Nat) (hk : k < maxS) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
  unfold maxS at hk; omega

theorem RCfg.n_le_maxS (cf : RCfg) (h : cf.Ok) : cf.n ≤ maxS := by
  unfold RCfg.Ok at h; unfold maxS; omega

theorem RCfg.n_pos (cf : RCfg) (h : cf.Ok) : 0 < cf.n := by
  unfold RCfg.Ok at h; omega

theorem cfgIs_ok (γ : RabiaNames) (cf : RCfg) : cfgIs (GF := GF) γ cf ⊢ ⌜cf.Ok⌝ := by
  unfold cfgIs; iintro ⟨-, %h⟩; ipureintro; exact h

theorem range_maxS : List.range maxS = [0, 1, 2, 3, 4] := by simp [maxS, List.range_succ]

theorem hsCmd_enc_len (c : Nat) (hc : c < 128) : (encCmd (hsCmd c)).length < 2 ^ 32 := by
  unfold encCmd hsCmd encScalar
  rw [varint]
  have : (BitVec.ofNat 32 c).toNat = c := by simp; omega
  simp only [this]
  split <;> simp [*]

theorem hsBytes_inj (c c' : Nat) (hc : c < 128) (hc' : c' < 128)
    (h : hsBytes c <+: hsBytes c' ∨ hsBytes c' <+: hsBytes c) : c = c' := by
  have h1 := hsCmd_enc_len c hc
  have h2 := hsCmd_enc_len c' hc'
  have he : encCmd (hsCmd c) = encCmd (hsCmd c') := by
    rcases h with h | h
    · exact frame_prefix_inj (y := []) h1 h2 (by simpa [hsBytes] using h)
    · exact (frame_prefix_inj (y := []) h2 h1 (by simpa [hsBytes] using h)).symm
  have := congrArg CmdV.cliId (encCmd_inj he)
  simp only [hsCmd] at this
  have := congrArg BitVec.toNat this
  simp at this
  omega

end lemmas

end Perennial.rabia.internal.tcp
