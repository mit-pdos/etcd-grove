/-
The proof of `serverCodec.ReadRequestHeader` (`Net/Spec/net/rpc/serverCodec__ReadRequestHeader.lean`):
`readFrame`, then the payload parsed: its first 8 bytes (`getU64`), a string (`getString` on
`p[8:]`), nothing after it; the fields stored.
-/
module

public import Net.Spec.net.rpc.serverCodec__ReadRequestHeader
public import Net.Spec.net.rpc.getU64
public import Net.Spec.net.rpc.getString

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions]

theorem serverCodec.ReadRequestHeader.wp_proof (wp_readFrame : readFrame.spec (GF := GF) (hG := hG))
    (wp_getU64 : getU64.spec (GF := GF) (hG := hG))
    (wp_getString : getString.spec (GF := GF) (hG := hG)) :
    serverCodec.ReadRequestHeader.spec (GF := GF) (hG := hG) := by
  intro c t cn s a la ra r rv P F eof ueof ed ef
  wp_start as ⟨#Hrwc, #Hc, #Hio, #Heof, #Hueof, #Hed, #Hef, #HefV, Hr, HP, #Hacc⟩
  wp_auto
  wp_apply wp_readFrame t cn s a la ra P F eof ueof ed ef
      $$ [$Hc $Hio $Heof $Hueof $Hed $Hef $HefV $HP $Hacc]
    as %p %err ⟨%got, HP, Hres⟩
  unfold errors.newVar
  icases HefV with ⟨%xf, #Hxf, -⟩
  icombine Hef Hxf gives %Hf
  subst Hf
  icases Hres with (⟨%pl, ⟨%Hnil, %Hgot, %Hpl⟩, Hp, Hpcap⟩ | ⟨%Hne, HE⟩)
  rotate_left
  · cases err with
    | nil => exact absurd rfl Hne
    | ok e =>
      wp_auto
      iapply HΦ
      iexists got
      iframe HP
      iright
      iframe Hr
      isplitr
      · ipureintro; exact Hne
      icases HE with (%HE | HE)
      · ileft; ipureintro; exact HE.1
      · iright; iexact HE
  subst Hnil
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hp
  wp_if_destruct
  · -- shorter than 8 bytes
    iapply HΦ
    iexists got
    iframe HP
    iright
    iframe Hr
    isplitr
    · ipureintro; simp [interface.mkOk]
    ileft; ipureintro; first | rfl | trivial
  rename_i Hge8
  have hb8 : 8 ≤ pl.length := by
    have : sint.Z (W64 8) = 8 := by decide
    have : sint.nat p.len = (sint.Z p.len).toNat := rfl
    omega
  rw [← List.take_append_drop 8 pl]
  wp_apply wp_getU64 p _ (pl.take 8) (pl.drop 8) (by simp; omega) $$ Hp as Hp
  rw [List.take_append_drop]
  ihave %Hwf := ownSlice_wf $$ Hp
  have hb : 0 ≤ sint.Z (W64 8) ∧ sint.Z (W64 8) ≤ sint.Z p.len := by
    have : sint.Z (W64 8) = 8 := by decide
    have : sint.nat p.len = (sint.Z p.len).toNat := rfl
    omega
  rw [ite_eq_left ⟨hb.1, hb.2, Hwf.2⟩]
  icases (ownSlice_split_all (W64 8) p _ pl hb).1 $$ Hp with ⟨Hp1, Hp2⟩
  have h8 : sint.nat (W64 8) = 8 := by decide
  rw [h8]
  wp_apply wp_getString _ _ (pl.drop 8) $$ Hp2 as %sm %rest %ok Hres1
  (try wp_auto)
  cases ok
  · -- not a string
    simp only [Bool.false_eq_true, ite_false]
    icases Hres1 with %Hno
    (try wp_auto)
    iapply HΦ
    iexists got
    iframe HP
    iright
    iframe Hr
    isplitr
    · ipureintro; simp [interface.mkOk]
    ileft; ipureintro; first | rfl | trivial
  simp only [ite_true]
  icases Hres1 with ⟨%r1, %Hr1, Hrest⟩
  ihave %Hl1 := ownSlice_len $$ Hrest
  (try wp_auto)
  by_cases hr1 : r1 = []
  · subst hr1
    have hz : rest.len = W64 0 := by
      simp at Hl1; word
    rw [hz]
    (try wp_auto)
    iapply HΦ
    iexists got
    iframe HP
    ileft
    iexists (leToU64 (pl.take 8)), sm
    iframe Hr
    ipureintro
    have hlen8 : (pl.take 8).length = 8 := by rw [List.length_take, Nat.min_eq_left hb8]
    have hpl : reqHdr (leToU64 (pl.take 8)) sm = pl := by
      rw [reqHdr, leToU64_le _ hlen8]
      rw [List.append_nil] at Hr1
      rw [← Hr1, List.take_append_drop]
    rw [hpl]
    exact ⟨rfl, Hgot, Hpl⟩
  · have hnz : rest.len ≠ W64 0 := by
      intro h; apply hr1; rw [h] at Hl1
      exact List.length_eq_zero_iff.mp (Hl1.1.trans (by decide))
    rw [decide_eq_false hnz]
    (try wp_auto)
    iapply HΦ
    iexists got
    iframe HP
    iright
    iframe Hr
    isplitr
    · ipureintro; simp [interface.mkOk]
    ileft; ipureintro; first | rfl | trivial

end proof

end net.rpc
end Perennial
