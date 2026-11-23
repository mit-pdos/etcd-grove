/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/layers/network/MsgSerializer.lean`, run `rabia-r1wake-1`.)

The proof of `rabia/roles/server/layers/network.(*Network).MsgSerializer`.
-/
module

public import Dsverify.Proof.rabia.internal.message.SpecPure
public import Dsverify.Proof.rabia.roles.server.layers.network.Basics

@[expose] public section

noncomputable section

namespace Perennial.rabia.roles.server.layers.network

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model Net rabia.internal.message
  rabia.internal.config rabia rabia.internal.tcp

set_option linter.unusedSectionVars false

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable [package_sem : rabia.roles.server.layers.network.Assumptions]

set_option goose.wp.extras true

set_option maxHeartbeats 4000000 in
theorem Network.MsgSerializer.wp_proof (hM : Msg.Marshal.spec (GF := GF)) :
    Network.MsgSerializer.spec (GF := GF) := fun γ cf k γl n => by
  wp_start as ⟨#Hconf, #Hsh, #Hcfg, Hres⟩
  ihave %hnS := cfgIs_n_le γ cf $$ Hcfg
  unfold networkSerRes
  icases Hres with ⟨%nv, %γts, %γsl, %γs, %hk, #Hn, #Hsend, #Hts, Hloop⟩
  unfold netTcpSend
  icases Hsend with ⟨%ssl, %chs, #Hssl, #Hchs, %Hlens, #Hchans⟩
  ihave %Hchslen := ownSlice_len _ _ _ $$ Hchs
  wp_apply wp_with_defer as %defer Hdefer
  iStructNamed Hn
  wp_auto
  wp_for_core
  wp_auto
  cleanup_bool_decide
  unfold serLoop
  icases Hloop with ⟨%R, %bl, %Ex, %B, Hcons, #Hslb, %Hbl, #Hexlb, %HEx, Hmine, %HB, Htoks, Hprods⟩
  wp_apply wp_spsc_receive γts nv.ToSerializer' (toSerP γ cf k γl γsl) (fun _ => iprop(False)) R $$
    [$Hts $Hcons] as %v %ok Hv
  cases ok
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hv with ⟨Hv, -⟩
    iexfalso; iexact Hv
  simp only [↓reduceIte]
  icases Hv with ⟨Hv, Hcons⟩
  unfold toSerP
  icases Hv with ⟨%m, %bl', #Hrep, Hok, #Hslb', %Hbl', Hrest⟩
  wp_auto_lc 1
  have hRn : ((R.length : Int)).toNat = R.length := by simp
  rw [hRn] at Hbl'
  rw [hRn]
  unfold serLb
  ihave %Hpre := mono_list_lb_valid _ _ _ $$ Hslb Hslb'
  obtain ⟨b, hb⟩ : ∃ b, bl'[R.length]? = some b := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hbl' : bl' = bl ++ [b] := snoc_of_prefix bl bl' b Hpre (by omega) (by rw [Hbl.1]; exact hb)
  subst hbl'
  rw [← Hbl.1]
  icases ser_step γl B Ex bl b m Hbl.2 HEx HB.1 HB.2 $$ [$Hexlb $Htoks $Hrest] with
    ⟨%Ex', #Hexlb', Htoks, %Hst⟩
  icases bmsgOk_encBound γ cf k m $$ Hok with ⟨Hok, %Hbnd⟩
  iapply fupd_wp
  imod bcast_append γ cf k B m hk Hst.2.1 $$ [$Hsh $Hcfg $Hlc1 $Hmine $Hok] with ⟨Hmine, #Hblb⟩
  imodintro
  wp_apply hM msg_ptr v m (DFrac.own 1) $$ [$msg $Hrep] as %dsl ⟨msg, Hd⟩
  · ipureintro; exact Hbnd
  iapply fupd_wp
  imod (ownSlice_persist dsl _ _) $$ Hd with #Hd
  imodintro
  have hlen3 : sint.Z ssl.len = (cf.n : Int) := by
    have h1 := Hchslen.1; rw [Hlens.1] at h1; have h2 := Hchslen.2
    unfold maxS at hnS; word
  have hγs3 : γs.length = cf.n := Hlens.2
  have hchs3 : chs.length = cf.n := Hlens.1
  ihave HI : (∃ (i : w64) (tv : GoChan), "i" ∷ i_ptr ↦ i ∗ "t" ∷ t_ptr ↦ tv ∗ "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ (cf.n : Int)⌝ ∗
      "Hdone" ∷ ([∗list] γo ∈ γs.take (sint.nat i), ordProd γo 0 (B.length + 1)) ∗
      "Hrest" ∷ ([∗list] γo ∈ γs.drop (sint.nat i), ordProd γo 0 B.length) : IProp GF) $$ [i t Hprods]
  · iexists W64 0, _
    iframe
    isplitr
    · ipureintro; constructor <;> simp
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
    iframe
    iapply BigSepL.bigSepL_nil.2; iempintro
  wp_for HI
  wp_if_destruct
  · rw [hlen3] at Hif
    have Hid : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z ssl.len := ⟨Hi.1, by rw [hlen3]; exact Hif⟩
    simp only [Hid, _root_.and_self, ↓reduceIte]
    have hin : sint.nat i < cf.n := by unfold maxS at hnS; word
    have hγlt : sint.nat i < γs.length := by omega
    obtain ⟨cj, Hcj⟩ : ∃ cj, chs[sint.nat i]? = some cj := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨γo, Hγo⟩ : ∃ γo, γs[sint.nat i]? = some γo := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    wp_apply wp_load_slice_index ssl (sint.Z i) chs _ cj Hid.1 $$ [$Hchs] as -
    · ipureintro; exact Hcj
    ihave #Hcho := BigSepL.bigSepL_lookup Hcj $$ Hchans
    icases Hcho with ⟨%γo', %Hγo', #Hcho⟩
    rw [Hγo] at Hγo'; cases Hγo'
    have hdrop : γs.drop (sint.nat i) = γo :: γs.drop (sint.nat i + 1) := by
      rw [List.drop_eq_getElem_cons hγlt]
      congr
      rw [List.getElem?_eq_getElem hγlt] at Hγo
      exact Option.some.inj Hγo
    rw [hdrop]
    icases BigSepL.bigSepL_cons.1 $$ Hrest with ⟨Hprod, Hrest⟩
    wp_apply wp_ord_send γo cj 2 (sendP γ cf k (sint.nat i)) 0 B.length dsl $$ [$Hcho $Hprod] as Hprod
    · unfold sendP
      simp only [↓reduceIte]
      iexists B ++ [m], m
      iframe Hblb Hd
      ipureintro; simp
    wp_for_post
    iframe
    iexists i + W64 1, cj
    iframe
    have hsucc : sint.nat (i + W64 1) = sint.nat i + 1 := by unfold sint.nat; word
    rw [hsucc]
    isplitr
    · ipureintro; word
    have htk : γs.take (sint.nat i + 1) = γs.take (sint.nat i) ++ [γo] := by
      rw [List.take_add_one, Hγo]; rfl
    rw [htk]
    isplitl [Hdone Hprod]
    · iapply BigSepL.bigSepL_snoc.2
      iframe
    iexact Hrest
  · -- the broadcast done: the next forward
    have hi3 : sint.nat i = cf.n := by rw [hlen3] at Hif; unfold maxS at hnS; word
    rw [hi3, show γs.drop cf.n = [] by rw [← hγs3]; simp, show γs.take cf.n = γs by rw [← hγs3]; simp]
    wp_for_post
    iframe
    iexists R ++ [v], bl ++ [b], Ex', B ++ [m]
    iframe
    isplitr
    · iexact Hslb'
    isplitr
    · ipureintro; exact ⟨by simp [Hbl.1], Hst.2.2.2⟩
    isplitr
    · iexact Hexlb'
    isplitr
    · ipureintro; exact Hst.1
    isplitr
    · ipureintro; exact ⟨Hst.2.1, Hst.2.2.1⟩
    simp only [List.length_append, List.length_singleton]
    iexact Hdone

end proof
end Perennial.rabia.roles.server.layers.network
