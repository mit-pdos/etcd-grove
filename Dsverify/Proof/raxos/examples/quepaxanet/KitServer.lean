/-
Server machine `k` (`kit.go`'s `Server`, `serve`, `config`): it waits for the configuration
(`awaitConf` at its configuration address, the first configuration on a bag channel: `confIs γ c`),
and if it is one of `c`'s replicas (`k ≤ c.n`) it runs replica `k` (`raxos.New` of `config`'s
`InstanceConfig`, `NetworkInit`, `StartProposers`, `Run`, from `replicaRes γ c k`, which its
share `serverRes γ k` and `confIs γ c` give); it then sleeps forever. The callees' specs are
parameters (`strings.Split`: Perennial's; the replica's: `Replica/Results`; the library's:
`net`, `io`); the kit's `Results` supplies the proofs.
-/
module

public import Dsverify.Proof.raxos.examples.quepaxanet.KitAwait
public import Dsverify.Proof.raxos.Replica
public import Perennial.Spec.strings.Split

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace raxos.examples.quepaxanet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote
open raxos raxos.pure

/-- Replica `k`'s (1 ≤ k ≤ n) configured entry. -/
theorem peer_fields [GooseExts] (n k : Nat) (hk : 1 ≤ k ∧ k ≤ n) :
    (peersCfg n)[k - 1]? = some ⟨decStr k, go!"127.0.0.1", decStr (7600 + (6 + k)),
      decStr (7600 + (26 + k))⟩ := by
  unfold peersCfg
  rw [List.getElem?_map, List.getElem?_range' (by omega)]
  simp only [Option.map_some]
  rw [show 1 + 1 * (k - 1) = k by omega, show 7600 + (6 + k) = 7606 + k by omega,
    show 7600 + (26 + k) = 7626 + k by omega]
  rfl

theorem peersCfg_length [GooseExts] (n : Nat) : (peersCfg n).length = n := by
  simp [peersCfg]

/-- Client `c`'s (c < 6) configured entry. -/
theorem client_fields [GooseExts] (c : Nat) (hc : c < 6) :
    clientsCfg[c]? = some ⟨decStr (21 + c), go!"127.0.0.1", decStr (7600 + (1 + c))⟩ := by
  unfold clientsCfg
  rw [List.getElem?_map, List.getElem?_range hc]
  rw [show 7600 + (1 + c) = 7601 + c by omega]
  rfl

theorem clientsCfg_length [GooseExts] : clientsCfg.length = 6 := by
  simp [clientsCfg]

theorem ite_t {α : Sort _} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]

theorem cv_lt6 (cv : w64) (h : uint.Z cv < uint.Z (W64 6)) : uint.nat cv < 6 := by word

theorem cv_eq6 (cv : w64) (h1 : uint.nat cv ≤ 6) (h : ¬ uint.Z cv < uint.Z (W64 6)) :
    uint.nat cv = 6 := by word

theorem cv_succ (cv : w64) (h : uint.nat cv < 6) :
    uint.nat (cv + W64 1) = uint.nat cv + 1 ∧ uint.nat (cv + W64 1) ≤ 6 := by
  constructor <;> word

section config
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : raxos.examples.quepaxanet.Assumptions]
variable [strings.Assumptions]

local notation "kpkg" => pkg_id.raxos.examples.quepaxanet

set_option goose.wp.extras true

/-- `RecAddrs()` returns a new slice of the recorders' addresses. -/
theorem wp_RecAddrs :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! raxos.examples.quepaxanet.RecAddrs)) (Val #()))
    {{ (sl : GoSlice), RET #sl; sl ↦* recAddrsL }} := by
  wp_start as -
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.string))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoString) (t := go.string) recAddrsL
  wp_auto
  isplitl []
  · ipureintro; rw [recAddrsL_lit]; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  iapply HΦ
  iexact Hsl

/-- **`config(n, addrs, recs)`**: QuePaxa's configuration of `n` replicas, `n ∈ {3, 5}`. -/
theorem wp_config (wp_Split : strings.Split.spec (GF := GF) (hG := hG))
    (n : Nat) (hn : n = 3 ∨ n = 5) (asl rsl : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ asl ↦*□ addrsL ∗ rsl ↦*□ recAddrsL }}
      (App (App (App (Val (@! raxos.examples.quepaxanet.config)) (Val #(W64 n))) (Val #asl))
        (Val #rsl))
    {{ (cfg : Loc), RET #cfg; ∃ cv, cfg ↦□ cv ∗ cfgVal n cv }} := by
  wp_start as ⟨#Hasl, #Hrsl⟩
  wp_auto
  have hn5 : n ≤ 5 := by omega
  ihave %Hlen := ownSlice_len _ _ _ $$ Hasl
  have Halen : sint.Z asl.len = 12 := by
    have : addrsL.length = 12 := rfl
    word
  ihave %Hrlen := ownSlice_len _ _ _ $$ Hrsl
  have Hrlen' : sint.Z rsl.len = 12 := by
    have : recAddrsL.length = 12 := rfl
    word
  ihave HI : (∃ (i : w64) (sl : GoSlice),
      "i" ∷ i_ptr ↦ i ∗
      "Hc" ∷ «$r0_ptr» ↦ ({ (zero_val raxos.configuration.InstanceConfig) with Peers' := sl }) ∗
      "Hsl" ∷ sl ↦* (peersCfg n).take (uint.nat i - 1) ∗
      "Hcap" ∷ ownSliceCap raxos.configuration.ReplicaInstance sl (DFrac.own 1) ∗
      "%Hi" ∷ ⌜1 ≤ uint.nat i ∧ uint.nat i ≤ n + 1⌝ : IProp GF) $$ [i «$r0»]
  · iexists W64 1, slice.nil
    iframe i
    isplitl [«$r0»]
    · iexact «$r0»
    rw [show List.take (uint.nat (W64 1) - 1) (peersCfg n) = [] from rfl]
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSliceCap_nil
    ipureintro; constructor <;> simp
  wp_for HI
  wp_if_destruct
  · have Hle : uint.nat i ≤ n := by
      have : uint.nat i ≤ uint.nat (W64 (n : Int)) := by word
      have : uint.nat (W64 (n : Int)) = n := by rcases hn with rfl | rfl <;> rfl
      omega
    have hix : (sint.Z (W64 6 + i)).toNat = 6 + uint.nat i := by word
    have ha := addrsL_get (6 + uint.nat i) (by omega)
    have hsp := split_portAddr (6 + uint.nat i) (by omega)
    have hrec := recAddrsL_get (6 + uint.nat i) (by omega)
    have hsq := split_portAddr (26 + uint.nat i) (by omega)
    rw [show 7620 + (6 + uint.nat i) = 7600 + (26 + uint.nat i) by omega] at hrec
    have hpeer := peer_fields n (uint.nat i) ⟨Hi.1, Hle⟩
    rw [ite_t (by word)]
    wp_apply wp_load_slice_index asl (sint.Z (W64 6 + i)) addrsL _ _ (by word) $$ [Hasl] as -
    · iframe Hasl; ipureintro; rw [hix]; exact ha
    wp_apply wp_Split _ go!":" (by decide) as %psl ⟨Hp, -⟩
    rw [hsp]
    rw [ite_t (by word)]
    wp_apply wp_load_slice_index rsl (sint.Z (W64 6 + i)) recAddrsL _ _ (by word)
      $$ [Hrsl] as -
    · iframe Hrsl; ipureintro; rw [hix]; exact hrec
    wp_apply wp_Split _ go!":" (by decide) as %qsl ⟨Hq, -⟩
    rw [hsq]
    wp_apply wp_digits i
    ihave %Hplen := ownSlice_len _ _ _ $$ Hp
    ihave %Hqlen := ownSlice_len _ _ _ $$ Hq
    simp only [List.length_cons, List.length_nil] at Hplen Hqlen
    rw [ite_t (by word)]
    wp_apply wp_load_slice_index psl (sint.Z (W64 0)) _ _ go!"127.0.0.1" (by word)
      $$ [Hp] as Hp
    · iframe Hp; ipureintro; rfl
    repeat (first | wp_load | wp_pure)
    rw [ite_t (by word)]
    wp_apply wp_load_slice_index psl (sint.Z (W64 1)) _ _ (decStr (7600 + (6 + uint.nat i)))
      (by word) $$ [Hp] as Hp
    · iframe Hp; ipureintro; rfl
    repeat (first | wp_load | wp_pure)
    rw [ite_t (by word)]
    wp_apply wp_load_slice_index qsl (sint.Z (W64 1)) _ _ (decStr (7600 + (26 + uint.nat i)))
      (by word) $$ [Hq] as Hq
    · iframe Hq; ipureintro; rfl
    wp_pure
    wp_pure
    wp_pure
    wp_bind (App (Val (GoInstruction (CompositeLiteral raxos.configuration.ReplicaInstance.ty))) _)
    wp_pures
    wp_apply wp_slice_literal (V := raxos.configuration.ReplicaInstance)
      [⟨opid.bstr (toString (uint.nat i)), go!"127.0.0.1", decStr (7600 + (6 + uint.nat i)),
        decStr (7600 + (26 + uint.nat i))⟩]
    isplitr
    · ipureintro; simp
    iintro %lsl ⟨Hlit, -⟩
    wp_apply wp_slice_append (V := raxos.configuration.ReplicaInstance) _ _ _ _ _ $$
      [$Hsl $Hcap $Hlit] as %s1 ⟨Hsl, Hcap, -⟩
    wp_for_post
    iframe
    iexists i + W64 1, s1
    iframe
    have hn' : uint.nat (i + W64 1) - 1 = (uint.nat i - 1) + 1 := by word
    rw [hn', List.take_add_one, hpeer]
    iframe
    ipureintro; word
  · have hn' : uint.nat i - 1 = n := by
      have : ¬ uint.nat i ≤ uint.nat (W64 (n : Int)) := by word
      have : uint.nat (W64 (n : Int)) = n := by rcases hn with rfl | rfl <;> rfl
      omega
    rw [hn', List.take_of_length_le (by simp [peersCfg_length])]
    ihave HJ : (∃ (cv : w64) (sl2 : GoSlice),
        "c" ∷ c_ptr ↦ cv ∗
        "Hc" ∷ «$r0_ptr» ↦ (⟨sl, sl2⟩ : raxos.configuration.InstanceConfig) ∗
        "Hcl" ∷ sl2 ↦* clientsCfg.take (uint.nat cv) ∗
        "Hccap" ∷ ownSliceCap raxos.configuration.ClientInstance sl2 (DFrac.own 1) ∗
        "%Hcv" ∷ ⌜uint.nat cv ≤ 6⌝ : IProp GF) $$ [c Hc]
    · iexists W64 0, slice.nil
      iframe c
      isplitl [Hc]
      · iexact Hc
      rw [show List.take (uint.nat (W64 0)) clientsCfg = [] from rfl]
      isplitr
      · iapply ownSlice_nil
      isplitr
      · iapply ownSliceCap_nil
      ipureintro; decide
    iapply wp_fupd
    wp_for HJ
    wp_if_destruct
    · have Hlt : uint.nat cv < 6 := by
        exact cv_lt6 cv Hif
      have hix : (sint.Z (W64 1 + cv)).toNat = 1 + uint.nat cv := by word
      have ha := addrsL_get (1 + uint.nat cv) (by omega)
      have hsp := split_portAddr (1 + uint.nat cv) (by omega)
      have hcl := client_fields (uint.nat cv) Hlt
      rw [ite_t (by word)]
      wp_apply wp_load_slice_index asl (sint.Z (W64 1 + cv)) addrsL _ _ (by word) $$ [Hasl] as -
      · iframe Hasl; ipureintro; rw [hix]; exact ha
      wp_apply wp_Split _ go!":" (by decide) as %psl ⟨Hp, -⟩
      rw [hsp]
      wp_apply wp_digits
      rw [show uint.nat (W64 21 + cv) = 21 + uint.nat cv by word]
      ihave %Hplen := ownSlice_len _ _ _ $$ Hp
      simp only [List.length_cons, List.length_nil] at Hplen
      rw [ite_t (by word)]
      wp_apply wp_load_slice_index psl (sint.Z (W64 0)) _ _ go!"127.0.0.1" (by word)
        $$ [Hp] as Hp
      · iframe Hp; ipureintro; rfl
      repeat (first | wp_load | wp_pure)
      rw [ite_t (by word)]
      wp_apply wp_load_slice_index psl (sint.Z (W64 1)) _ _ (decStr (7600 + (1 + uint.nat cv)))
        (by word) $$ [Hp] as Hp
      · iframe Hp; ipureintro; rfl
      wp_pure
      wp_pure
      wp_bind (App (Val (GoInstruction (CompositeLiteral raxos.configuration.ClientInstance.ty))) _)
      wp_pures
      wp_apply wp_slice_literal (V := raxos.configuration.ClientInstance)
        [⟨opid.bstr (toString (21 + uint.nat cv)), go!"127.0.0.1",
          decStr (7600 + (1 + uint.nat cv))⟩]
      isplitr
      · ipureintro; simp
      iintro %lsl ⟨Hlit, -⟩
      wp_apply wp_slice_append (V := raxos.configuration.ClientInstance) _ _ _ _ _ $$
        [$Hcl $Hccap $Hlit] as %s2 ⟨Hcl, Hccap, -⟩
      wp_for_post
      iframe
      iexists cv + W64 1, s2
      iframe
      obtain ⟨hn'', hle⟩ := cv_succ cv Hlt
      rw [hn'', List.take_add_one, hcl]
      iframe
      ipureintro; rw [← hn'']; exact hle
    · have hc6 : uint.nat cv = 6 := by
        exact cv_eq6 cv Hcv Hif
      rw [hc6, List.take_of_length_le (by simp [clientsCfg_length])]
      ipersist Hc
      ipersist Hsl
      ipersist Hcl
      iapply HΦ
      iexists _
      iframe Hc
      unfold cfgVal
      iframe Hsl Hcl

end config

/-! ## The server machine -/

section server
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : raxos.examples.quepaxanet.Assumptions]
variable [π : NetProtoGS] [ρ : RemoteGS] [qv : hyp.QpVocab GF]
variable [net.Assumptions] [go.BasicIntoValInj]
variable [_root_.Perennial.io.Assumptions] [strings.Assumptions]

attribute [local instance] HeapGS.goose_globalGS

local notation "kpkg" => pkg_id.raxos.examples.quepaxanet

set_option goose.wp.extras true

theorem srv_idx (k : w64) (csl : GoSlice) (hk : 1 ≤ uint.nat k ∧ uint.nat k ≤ 5)
    (Hcl : cfgAddrsL.length = sint.nat csl.len ∧ 0 ≤ sint.Z csl.len) :
    0 ≤ sint.Z (W64 6 + k) ∧ sint.Z (W64 6 + k) < sint.Z csl.len := by
  have : cfgAddrsL.length = 12 := rfl
  obtain ⟨h1, h2⟩ := Hcl
  have h3 : ((sint.nat csl.len : Nat) : Int) = sint.Z csl.len := Int.toNat_of_nonneg h2
  have h4 : sint.Z (W64 6 + k) = 6 + uint.nat k := by word
  omega

theorem kn_le (k : w64) (c : QConf) (hc : c.ok) (h : uint.Z k ≤ uint.Z (W64 (c.n : Int))) :
    uint.nat k ≤ c.n := by
  have : c.n ≤ 5 := by rcases hc.1 with h | h <;> omega
  word

/-- The replica's share from the server's and the configuration's. -/
theorem replicaRes_of (γ : QNames) (c : QConf) (k : Nat) (hc : c.ok) (hk : 1 ≤ k ∧ k ≤ c.n) :
    serverRes (GF := GF) γ k ∗ confIs γ c ⊢ replicaRes γ c k := by
  unfold serverRes sharedRes
  iintro ⟨⟨Htok, Hrec, Hfr, #Hsh⟩, #Hconf⟩
  icases Hsh with ⟨#Hc, #Hs, #Hn, #Hb, #Hsp⟩
  unfold replicaRes
  isplitr
  · ipureintro; exact ⟨hc, hk⟩
  iframe
  iframe Hconf Hc Hs Hn Hb Hsp

/-- **`Server(k)`**: the configuration, then replica `k` if `k ≤ c.n`; it never returns. -/
theorem Server.wp_proof
    (wp_Split : strings.Split.spec (GF := GF) (hG := hG))
    (wp_New : raxos.New.spec (GF := GF) (hG := hG))
    (wp_NI : raxos.Server.NetworkInit.spec (GF := GF) (hG := hG))
    (wp_SP : raxos.Server.StartProposers.spec (GF := GF) (hG := hG))
    (wp_Run : raxos.Server.Run.spec (GF := GF) (hG := hG))
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_ReadFull : raxos.ioLt.ReadFull.spec (GF := GF) (hG := hG)) :
    Server.spec (GF := GF) (hG := hG) := by
  intro γ k hk
  wp_start as Hres
  wp_auto
  wp_apply wp_Addrs as %asl Hasl
  wp_apply wp_RecAddrs as %rsl Hrsl
  wp_apply wp_CfgAddrs as %csl Hcsl
  iapply fupd_wp
  imod ownSlice_persist _ _ _ $$ Hasl with #Hasl
  imod ownSlice_persist _ _ _ $$ Hrsl with #Hrsl
  imod ownSlice_persist _ _ _ $$ Hcsl with #Hcsl
  imodintro
  wp_func_call
  wp_call
  wp_auto
  wp_apply (wp_make_bag1 (confP γ)) as %ch ⟨%γc, #Hch⟩
  have hk' : (sint.Z (W64 6 + k)).toNat = 6 + uint.nat k := by word
  ihave %Hcl := ownSlice_len _ _ _ $$ Hcsl
  have hidx : 0 ≤ sint.Z (W64 6 + k) ∧ sint.Z (W64 6 + k) < sint.Z csl.len :=
    srv_idx k csl hk Hcl
  rw [ite_t hidx]
  wp_apply wp_load_slice_index csl (sint.Z (W64 6 + k)) cfgAddrsL _ (portAddr (7640 + (6 + uint.nat k)))
    hidx.1 $$ [Hcsl] as -
  · iframe Hcsl; ipureintro; rw [hk']; exact cfgAddrsL_get _ (by omega)
  unfold serverRes
  icases Hres with ⟨Htok, Hrec, Hfr, #Hsh⟩
  ihave #Hpr := confProto_of_shared γ (6 + uint.nat k) (by omega) $$ Hsh
  wp_apply wp_fork $$ []
  · wp_apply wp_awaitConf_of wp_Listen wp_Accept wp_Read wp_Write wp_Close wp_ReadFull γ _ ch γc
      $$ [$Hpkg $Hpr $Hch]
    itrivial
  wp_apply (wp_bag_receive γc ch (confP γ)) $$ [$Hch] as %v Hv
  unfold confP
  icases Hv with ⟨%c, ⟨%Hv, %hc⟩, #Hconf⟩
  subst Hv
  wp_auto
  wp_if_destruct
  · have hkn : uint.nat k ≤ c.n := kn_le k c hc Hif
    wp_apply wp_registerProto
    have hn : c.n = 3 ∨ c.n = 5 := hc.1
    wp_apply wp_config wp_Split c.n hn asl rsl $$ [$Hasl $Hrsl] as %cfg ⟨%cv, #Hcfg, #Hcv⟩
    have hkw : k = W64 (uint.nat k : Int) := by word
    rw [show (LogPath : val) = #(go!"/tmp/quepaxa-net/") from rfl]
    ihave Hrr := replicaRes_of γ c (uint.nat k) hc ⟨hk.1, hkn⟩ $$ [Htok Hrec Hfr]
    · unfold serverRes; iframe Htok Hrec Hfr Hsh Hconf
    have hNew := wp_New γ c (uint.nat k) cfg cv go!"/tmp/quepaxa-net/"
    simp only [callV, List.foldl_cons, List.foldl_nil] at hNew
    rw [← hkw] at hNew
    wp_apply hNew $$ [$Hcfg $Hcv $Hrr] as %srv Hsrv
    ihave #Hsrc : isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src $$ []
    · iPkgInit
    wp_apply wp_NI γ c (uint.nat k) srv $$ [$Hsrc $Hsrv] as Hsrv
    wp_apply wp_SP γ c (uint.nat k) srv $$ [$Hsrc $Hsrv] as Hsrv
    wp_apply wp_Run γ c (uint.nat k) srv $$ [$Hsrc $Hsrv]
    ihave HT : (True : IProp GF) $$ []
    · itrivial
    wp_for HT
    (try rw [if_pos (by simp)])
    (try wp_auto)
    wp_apply time.wp_Sleep
    wp_for_post
    iframe
  · ihave HT : (True : IProp GF) $$ []
    · itrivial
    wp_for HT
    (try rw [if_pos (by simp)])
    (try wp_auto)
    wp_apply time.wp_Sleep
    wp_for_post
    iframe

end server

end raxos.examples.quepaxanet
end Perennial
