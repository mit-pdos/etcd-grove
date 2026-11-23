/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/tcp/ProxyLemmas.lean`, run
`rabia-r1wake-1`, onto `GooseLang/Ext/Net/Proto.lean`: the facts of a `proxyP` stream come from
the protocol up to extension (`protoPrefix`, what `rdOwn_proto` gives one step later), not from
the lab's reader token; the client's sending of its handshake from `rdOwn_sentLb`.)

The proxy's reading of `proxyP` streams: the handshake (its client), then the client's requests
in order (each the protocol's next, with its facts and the established connection).
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

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]

theorem hs_prefix {c c' : Nat} (hc : c < 128) (hc' : c' < 128) {Y F : List w8}
    (h : hsBytes c ++ Y <+: hsBytes c' ++ F) : c = c' := by
  have h1 := hsCmd_enc_len c hc
  have h2 := hsCmd_enc_len c' hc'
  have hp : model.frame (encCmd (hsCmd c)) <+: model.frame (encCmd (hsCmd c')) ++ F :=
    (List.prefix_append _ _).trans h
  have he := frame_prefix_inj h1 h2 hp
  exact hsBytes_inj c c' hc hc' (Or.inl (by simp [hsBytes, he]))

theorem ne_nil_of_prefix {R ext : List w8} (h : R <+: ext) (hR : R ≠ []) : ext ≠ [] := by
  rintro rfl; exact hR (List.prefix_nil.mp h)


/-- The handshake frame of a `proxyP` stream is a command's encoding. -/
theorem proxyP_frameIs_hs (γ : Names) (k : Nat) (cid : Nat) :
    ⊢ frameIs (GF := GF) (proxyP γ k) cid [] (fun bs => ∃ c, bs = encCmd c) := by
  unfold frameIs
  imodintro
  iintro %bs %hbs Hp
  unfold protoPrefix
  icases Hp with (%Hnil | ⟨%ext, %Hext, #HQ⟩)
  · ipureintro; exfalso; exact rabia.model.frame_ne_nil bs (by simpa using Hnil)
  have hne : ext ≠ [] := ne_nil_of_prefix Hext (by simpa using rabia.model.frame_ne_nil bs)
  ihave ⟨%cf, %c, %qs, %Hp, -⟩ := proxyP_hub0 γ k cid ext hne $$ HQ
  ipureintro
  obtain ⟨hc, -, hext, -⟩ := Hp
  have hpre : model.frame bs <+: model.frame (encCmd (hsCmd c)) ++ frames (qs.map encCmd) := by
    have := (by simpa using Hext : model.frame bs <+: ext)
    exact this.trans hext
  have := frame_prefix_inj hbs (hsCmd_enc_len c (by unfold nC at hc; omega)) hpre
  exact ⟨_, this⟩

/-- After the handshake: it is the client `c`'s (`c < nC`, `c mod nS = k`). -/
theorem proxyP_read_hs (γ : Names) (cf : RCfg) (k : Nat) (cid : Nat) (q : CmdV)
    (hq : (encCmd q).length < 2 ^ 32) :
    cfgIs γ.rab cf ∗ protoPrefix (proxyP (GF := GF) γ k) cid ([] ++ model.frame (encCmd q)) ⊢
      ∃ c, ⌜c < nC ∧ c % cf.n = k ∧ q = hsCmd c⌝ := by
  iintro ⟨#Hcf, Hp⟩
  unfold protoPrefix
  icases Hp with (%Hnil | ⟨%ext, %Hext, #HQ⟩)
  · ipureintro; exfalso; exact rabia.model.frame_ne_nil _ (by simpa using Hnil)
  have hne : ext ≠ [] := ne_nil_of_prefix Hext (by simpa using rabia.model.frame_ne_nil _)
  ihave ⟨-, %c, %qs, %Hp, -⟩ := proxyP_hub γ cf k cid ext hne $$ [$Hcf $HQ]
  obtain ⟨hc, hck, hext, -⟩ := Hp
  have hpre : model.frame (encCmd q) <+: model.frame (encCmd (hsCmd c)) ++ frames (qs.map encCmd) :=
    (by simpa using Hext : model.frame (encCmd q) <+: ext).trans hext
  have he := frame_prefix_inj hq (hsCmd_enc_len c (by unfold nC at hc; omega)) hpre
  have hqc := encCmd_inj he
  iexists c
  ipureintro; exact ⟨hc, hck, hqc⟩

/-- The next frame after the handshake and the requests `qs` is a command's encoding. -/
theorem proxyP_frameIs (γ : Names) (k : Nat) (cid : Nat) (c : Nat) (hc : c < nC) (qs : List CmdV)
    (hqs : ∀ q ∈ qs, (encCmd q).length < 2 ^ 32) :
    ⊢ frameIs (GF := GF) (proxyP γ k) cid
      (hsBytes c ++ frames (qs.map encCmd)) (fun bs => ∃ c, bs = encCmd c) := by
  unfold frameIs
  imodintro
  iintro %bs %hbs Hp
  unfold protoPrefix
  icases Hp with (%Hnil | ⟨%ext, %Hext, #HQ⟩)
  · ipureintro; exfalso
    have := congrArg List.length Hnil
    simp [frame_length] at this
  have hne : ext ≠ [] := ne_nil_of_prefix Hext (by simp [rabia.model.frame_ne_nil])
  ihave ⟨%cf, %c', %qs', %Hp, -⟩ := proxyP_hub0 γ k cid ext hne $$ HQ
  ipureintro
  obtain ⟨hc', -, hext, -, -, hb⟩ := Hp
  have h2 := Hext.trans hext
  have hcc : c = c' := hs_prefix (by unfold nC at hc; omega) (by unfold nC at hc'; omega)
    (Y := frames (qs.map encCmd) ++ model.frame bs) (by simpa [List.append_assoc] using h2)
  subst hcc
  have hpre := frames_decomp_pre (pre := hsBytes c) (A := qs.map encCmd) (L := qs'.map encCmd)
    (b := bs) (X := [])
    (by simpa using hqs) (by simpa using fun q hq => (hb q hq).2) hbs (by simpa [List.append_assoc] using h2)
  have hget := prefix_snoc_getElem hpre
  have hmem : bs ∈ qs'.map encCmd := List.mem_of_getElem? hget
  obtain ⟨r, -, hr⟩ := List.mem_map.1 hmem
  exact ⟨r, hr.symm⟩

/-- The request read after the handshake and the requests `qs`: a request of client `c` with a
sequence number above those of `qs`, within the budget, registered, on the established connection. -/
theorem proxyP_read (γ : Names) (k : Nat) (cid : Nat) (c : Nat) (hc : c < nC) (qs : List CmdV)
    (hqs : ∀ q ∈ qs, (encCmd q).length < 2 ^ 32) (q : CmdV) (hq : (encCmd q).length < 2 ^ 32) :
    protoPrefix (proxyP (GF := GF) γ k) cid
        (hsBytes c ++ frames (qs.map encCmd) ++ model.frame (encCmd q)) ⊢
      ⌜q.cliSeq.toNat < opBudget ∧ ∀ q' ∈ qs, q'.cliSeq.toNat < q.cliSeq.toNat⌝ ∗ reqOk γ c q ∗
      estab γ c k cid := by
  iintro Hp
  unfold protoPrefix
  icases Hp with (%Hnil | ⟨%ext, %Hext, #HQ⟩)
  · iexfalso; ipureintro
    have := congrArg List.length Hnil
    simp [frame_length] at this
  have hne : ext ≠ [] := ne_nil_of_prefix Hext (by simp [rabia.model.frame_ne_nil])
  ihave ⟨%cf, %c', %qs', %Hp, #Hest, #Hreqs⟩ := proxyP_hub0 γ k cid ext hne $$ HQ
  obtain ⟨hc', -, hext, hlen, hidx, hb⟩ := Hp
  have h2 := Hext.trans hext
  have hcc : c = c' := hs_prefix (by unfold nC at hc; omega) (by unfold nC at hc'; omega)
    (Y := frames (qs.map encCmd) ++ model.frame (encCmd q)) (by simpa [List.append_assoc] using h2)
  subst hcc
  have hpre := frames_decomp_pre (pre := hsBytes c) (A := qs.map encCmd) (L := qs'.map encCmd)
    (b := encCmd q) (X := [])
    (by simpa using hqs) (by simpa using fun q hq => (hb q hq).2) hq (by simpa [List.append_assoc] using h2)
  have hpre' : qs ++ [q] <+: qs' := map_prefix_of_inj (fun a b h => encCmd_inj h) (by simpa using hpre)
  have hget := prefix_snoc_getElem hpre
  simp only [List.getElem?_map, List.length_map] at hget
  rcases h : qs'[qs.length]? with _ | r
  · simp [h] at hget
  simp only [h, Option.map_some, Option.some.injEq] at hget
  have hqr : q = r := encCmd_inj hget.symm
  subst hqr
  have hlt : qs.length < qs'.length := by
    rcases List.getElem?_eq_some_iff.1 h with ⟨hl, -⟩; exact hl
  isplitr
  · ipureintro
    have hpw := (hidx.sublist hpre'.sublist)
    rw [List.pairwise_append] at hpw
    exact ⟨(hb q (List.mem_of_getElem? h)).1, fun a ha => hpw.2.2 a ha q (by simp)⟩
  isplitr
  · iapply (BigSepL.bigSepL_lookup (i := qs.length) h) $$ Hreqs
  icases Hest with (%Hn | #Hest)
  · subst Hn; simp at hlt
  · iexact Hest

end lemmas

end Perennial.rabia.internal.tcp
