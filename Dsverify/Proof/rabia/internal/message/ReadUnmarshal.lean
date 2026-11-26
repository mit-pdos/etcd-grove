/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/message/ReadUnmarshal.lean`,
run `rabia-r1wake-1`, onto the revised bufio: the frame's payload property `frameIs` is the
protocol's, reached through the reader by `net.connReader_proto` one step later (a later credit
taken at the start); the lab's `MsgPkgDeps` is the package fact.)

`(*Msg).ReadUnmarshal`'s and `(*Command).ReadUnmarshal`'s proofs: `BufRead` (`BufRead.wp_ofB`,
with the payload's `2^32` bound), the payload's property from the protocol (`frameIs`: an
encoding), then `Unmarshal` of `readBuf[:n]` (C1's proofs).
-/
module

public import Dsverify.Proof.rabia.internal.message.SpecInternal
public import Dsverify.Proof.rabia.internal.message.Internal
public import Net.Proof.net.ConnIo

@[expose] public section

noncomputable section

namespace Perennial.rabia.internal.message

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode model Net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : rabia.internal.message.Assumptions]
variable [_root_.Perennial.bufio.Assumptions] [_root_.Perennial.io.Assumptions]
variable [net.Assumptions] [π : NetProtoGS]

/-- The payload's property from `frameIs`, the protocol's fact of the bytes read (one step later:
a later credit). -/
theorem frameIs_use (br : Loc) (ri : GoInterfaceOk) (cn : Nat) (s : Bool) (P : Proto GF)
    (E : List w8 → GoInterface → IProp GF) (R bs : List w8) (D : List w8 → Prop)
    (hbs : bs.length < 2 ^ 32) :
    £ 1 -∗ frameIs P cn R D -∗
      EtcdGrove.bufio.ownBufReader br ri connPre (recvTokL (Gg := hG.goose_globalGS) cn s P) E
        (R ++ frame bs) ={⊤}=∗
      EtcdGrove.bufio.ownBufReader br ri connPre (recvTokL (Gg := hG.goose_globalGS) cn s P) E
        (R ++ frame bs) ∗ ⌜D bs⌝ := by
  iintro Hlc #HF Hown
  ihave ⟨Hown, Hpp⟩ := net.connReader_proto br ri connPre cn s P E (R ++ frame bs) $$ Hown
  imod (lc_fupd_elim_later (GF := GF) (E := ⊤)) $$ Hlc Hpp with #Hpp
  iunfold frameIs at HF
  ihave %HD := HF $$ %bs %hbs Hpp
  imodintro
  iframe Hown
  ipureintro; exact HD

set_option maxHeartbeats 1000000 in
theorem Msg.ReadUnmarshal.wp_proof (hBR : BufRead.specB (GF := GF))
    (hU : Msg.Unmarshal.spec (GF := GF)) :
    Msg.ReadUnmarshal.spec (GF := GF) := by
  intro l br ri cn s P E R sl ds
  wp_start as ⟨Hl, Hown, #HF, Hsl⟩
  wp_auto_lc 1
  wp_apply hBR br ri _ E R sl ds $$ [$Hpkg $Hown $Hsl] as %n %e Hres
  icases Hres with (⟨%He, %bs, %Hbs, Hsl, Hown⟩ | ⟨%He, %R', %ds', %HR, Hsl, Hown⟩)
  · subst He
    obtain ⟨rfl, hbl, hb32⟩ := Hbs
    iapply fupd_wp
    imod frameIs_use br ri cn s P E R bs _ hb32 $$ Hlc1 HF Hown with ⟨Hown, %HD⟩
    imodintro
    obtain ⟨m, rfl⟩ := HD
    wp_auto
    ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
    ihave %Hwf := ownSlice_wf _ _ _ $$ Hsl
    have hsl : sint.Z sl.len = (ds.length : Int) := by
      have hds : ds.length = sint.nat sl.len := by have := Hlen.1; simp at this; omega
      rw [hds]; exact (Int.toNat_of_nonneg Hlen.2).symm
    have hk : sint.Z (W64 ((encMsg m).length : Int)) = (encMsg m).length := by word
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by rw [hk]; simp, by rw [hk]; omega⟩)]
    have hkn : sint.nat (W64 ((encMsg m).length : Int)) = (encMsg m).length := by
      have h2 := hk; simp only [sint.Z] at h2; simp only [sint.nat]; rw [h2]; simp
    ihave ⟨Hs1, Hs2⟩ := (ownSlice_split_all (W64 ((encMsg m).length : Int)) sl _ _
      ⟨by omega, by omega⟩).1 $$ Hsl
    rw [hkn, List.take_left]
    wp_auto
    wp_apply hU l _ _ m $$ [$Hl $Hs1] as ⟨%v, Hl, #Hrep, Hs1⟩
    ihave Hsl := slice_rejoin sl _ _ _ _ ⟨by omega, by omega⟩ (by rw [hkn]) $$ [$Hs1 $Hs2]
    iapply HΦ
    iexists _
    iframe Hsl
    ileft
    isplitr
    · ipureintro; rfl
    iexists v, m
    iframe Hl Hrep Hown
    ipureintro; omega
  · rcases e with ei | _
    · wp_auto
      iapply HΦ
      iexists ds'
      iframe Hsl
      iright
      isplitr
      · ipureintro; exact He
      iexists R', _
      iframe Hl Hown
      ipureintro; exact HR
    exact absurd rfl He

set_option maxHeartbeats 1000000 in
theorem Command.ReadUnmarshal.wp_proof (hBR : BufRead.specB (GF := GF))
    (hU : Command.Unmarshal.spec (GF := GF)) :
    Command.ReadUnmarshal.spec (GF := GF) := by
  intro l br ri cn s P E R sl ds
  wp_start as ⟨Hl, Hown, #HF, Hsl⟩
  wp_auto_lc 1
  wp_apply hBR br ri _ E R sl ds $$ [$Hpkg $Hown $Hsl] as %n %e Hres
  icases Hres with (⟨%He, %bs, %Hbs, Hsl, Hown⟩ | ⟨%He, %R', %ds', %HR, Hsl, Hown⟩)
  · subst He
    obtain ⟨rfl, hbl, hb32⟩ := Hbs
    iapply fupd_wp
    imod frameIs_use br ri cn s P E R bs _ hb32 $$ Hlc1 HF Hown with ⟨Hown, %HD⟩
    imodintro
    obtain ⟨m, rfl⟩ := HD
    wp_auto
    ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
    ihave %Hwf := ownSlice_wf _ _ _ $$ Hsl
    have hsl : sint.Z sl.len = (ds.length : Int) := by
      have hds : ds.length = sint.nat sl.len := by have := Hlen.1; simp at this; omega
      rw [hds]; exact (Int.toNat_of_nonneg Hlen.2).symm
    have hk : sint.Z (W64 ((encCmd m).length : Int)) = (encCmd m).length := by word
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by rw [hk]; simp, by rw [hk]; omega⟩)]
    have hkn : sint.nat (W64 ((encCmd m).length : Int)) = (encCmd m).length := by
      have h2 := hk; simp only [sint.Z] at h2; simp only [sint.nat]; rw [h2]; simp
    ihave ⟨Hs1, Hs2⟩ := (ownSlice_split_all (W64 ((encCmd m).length : Int)) sl _ _
      ⟨by omega, by omega⟩).1 $$ Hsl
    rw [hkn, List.take_left]
    wp_auto
    wp_apply hU l _ _ m $$ [$Hl $Hs1] as ⟨%v, Hl, #Hrep, Hs1⟩
    ihave Hsl := slice_rejoin sl _ _ _ _ ⟨by omega, by omega⟩ (by rw [hkn]) $$ [$Hs1 $Hs2]
    iapply HΦ
    iexists _
    iframe Hsl
    ileft
    isplitr
    · ipureintro; rfl
    iexists v, m
    iframe Hl Hrep Hown
    ipureintro; omega
  · rcases e with ei | _
    · wp_auto
      iapply HΦ
      iexists ds'
      iframe Hsl
      iright
      isplitr
      · ipureintro; exact He
      iexists R', _
      iframe Hl Hown
      ipureintro; exact HR
    exact absurd rfl He

end proof

end Perennial.rabia.internal.message
