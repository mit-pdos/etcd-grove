/-
The proof of `Spec/os/RemoveN.lean` (and, with `N = .only [b]`, of `Spec/os/Remove.lean`'s
`specFileSnc`, `Proof/os/Remove.lean`). `os.Remove` is Go's (since 2026-11-24, Go-model overlays S5):
`ignoringEINTR` around a closure calling `syscall.Unlink(name)`, whose model runs the stub `fsUnlink`
(`CallBegin`, then the extension's `Unlink`); for an error, `ignoringEINTR` around `syscall.Rmdir(name)`
(the stub `fsRmdir`), then `&PathError{"remove", name, e}` (`e` the unlink's error when the rmdir's
is `ENOTDIR`, else the rmdir's). Each unlink attempt is a `CallBegin` (the log's length at least the
claim's last change, `osNames_next`). Before the unlink took effect, an attempt opens the atomic
update around the step (`wp_aunc_step`; the claim whole, `wp_osUnlinkSN`): an `EINTR` with no effect
aborts, any other result commits. After it took effect, the name is gone in the caller's fraction and
a retry fails (`wp_osUnlinkSN_none`). Each rmdir attempt fails, the name holding no directory
(`wp_osRmdirSN_none`).
-/
module

public import Spec.os.RemoveN
public import Proof.os.ErrorOk
public import Proof.os.SharedExt
public import Proof.os.UnlinkN
public import Proof.os.IgnoringEINTR

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

theorem os.Remove.wp_proofFileSncN : os.Remove.specFileSncN (GF := GF) (hG := hG) := by
  intro d b j i N R dq h q r qc Q hb hbN hi hq
  have habs : ∀ x s, (h.log x (⟨.remove j b (.file i), s⟩ : LogEntry)
      (restrictN N (GMap.delete b h.cur))).cur !! b = none := by
    intro x s; simp only [NamesH.log]
    rw [restrictN_lookup _ _ _ hbN]; exact GMap.lookup_delete _ _
  wp_start as ⟨#Hos, #Hsi, Hp, Hperm, Hn, Hau⟩
  imod osNames_next R j _ _ h CoPset.subseteq_top $$ Hsi Hn with ⟨Hn, #Hlb⟩
  try wp_auto
  rw [recv_eq_func_mk]
  -- the unlink loop
  wp_apply (os.wp_ignoringEINTR _
    iprop(name_ptr ↦ child d b ∗ osPathS R d dq j ∗ osCallPerm (callKey R d) qc ∗
      ((osAUnc (osNames j N (DFrac.own r) h) (rmFileOutN j N b i h (DFrac.own r)) Q ∗
          osNames j N (DFrac.own q) h) ∨
        (∃ xs, Q (some xs) ∗ rmFileOutN j N b i h (DFrac.own q) (some xs))))
    (fun e => iprop(name_ptr ↦ child d b ∗ osPathS R d dq j ∗ osCallPerm (callKey R d) qc ∗
      ∃ (o : Option (Nat × Nat)) (h' : NamesH), ⌜e = 0 → o.isSome⌝ ∗
        ⌜∀ J, h'.cur !! b ≠ some (.dir J)⌝ ∗ Q o ∗ osNames j N (DFrac.own q) h' ∗
        (osNames j N (DFrac.own q) h' -∗ rmFileOutN j N b i h (DFrac.own q) o))))
    $$ [name Hp Hperm Hn Hau] as %e ⟨Hname, Hp, Hperm, %o, %h', %ho, %hnd, HQ, Hn, Hback⟩
  · iframe
    isplitl [Hn Hau]
    · ileft; iframe
    iintro !>
    unfold os.eintrCall
    iintro %Φ' ⟨Hname, Hp, Hperm, HSt⟩ HΦ'
    rw [← recv_eq_func_mk]
    wp_call
    try wp_auto
    irename : (_ ↦ (_ : GoInterface) : IProp GF) => Hres0c
    wp_func_call; wp_call
    try wp_auto
    irename «$res0» => Hres0u
    icases osCallPerm_child R d b _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
    wp_stub syscall.fsUnlink.impl
    wp_apply +noauto wp_osCallBeginS R _ qc h.next CoPset.subseteq_top CoPset.subseteq_top
      $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
    iclear Hls
    icases HSt with (⟨Hau, Hn⟩ | ⟨%xs, HQ, Hout⟩)
    · wp_apply +noauto (wp_aunc_step "Unlink" _ (osNames j N (DFrac.own r) h)
        (rmFileOutN j N b i h (DFrac.own r)) Q) $$ Hau [Hn Hk Hp HΦ' Hname Hres0c Hres0u]
      iintro Hr
      ihave Hw := (osNames_join j _ q r h hq).1 $$ [Hn Hr]
      · iframe
      iapply wp_osUnlinkSN R d b j i N dq h t s0 qc hb hbN hi hs osN_sub_au osShN_sub_au
        $$ Hos Hsi Hp Hw Hk
      iintro %e Hperm Hp Hres
      unfold osNamesAfter
      icases Hres with (⟨%he, Hw⟩ | ⟨%x, Hlog, Hw⟩)
      · -- no effect
        icases (osNames_join j _ q r h hq).2 $$ Hw with ⟨Hn, Hr'⟩
        by_cases he4 : e = W64 4
        · ileft
          iframe Hr'
          iintro Hau
          try wp_auto
          wp_apply wp_errnoErr
          try wp_auto
          iapply HΦ'
          try dsimp only
          ileft
          isplitr
          · ipureintro; exact he4
          iframe
          ileft; iframe
        · iright
          iexists none
          isplitl [Hr']
          · dsimp only [rmFileOutN, logOut, claimOut]; iframe
          iintro HQ
          try wp_auto
          wp_apply wp_errnoErr
          try wp_auto
          iapply HΦ'
          try dsimp only
          iright
          isplitr
          · ipureintro; exact he4
          iframe
          (try iexists none, h)
          isplitr
          · ipureintro; exact fun h0 => absurd h0 he
          isplitr
          · ipureintro; exact fun J hJ => by rw [hi] at hJ; cases hJ
          iintro Hn
          dsimp only [rmFileOutN, logOut, claimOut]
          iframe
      · -- the unlink logged
        icases (osNames_join j _ q r _ hq).2 $$ Hw with ⟨Hn, Hr'⟩
        unfold osLogged
        icases Hlog with ⟨%hst, #He, #Hl⟩
        iright
        iexists some (x, s0)
        isplitl [Hr']
        · dsimp only [rmFileOutN, logOut, claimOut, osLogged, rmFileEnt]; iframe; iframe #
          ipureintro; exact ⟨hs, hst⟩
        iintro HQ
        try wp_auto
        wp_apply wp_errnoErr
        try wp_auto
        iapply HΦ'
        try dsimp only
        by_cases he4 : e = W64 4
        · ileft
          isplitr
          · ipureintro; exact he4
          iframe
          iright; iexists (x, s0)
          dsimp only [rmFileOutN, logOut, claimOut, osLogged, rmFileEnt]; iframe; iframe #
          ipureintro; exact ⟨hs, hst⟩
        · iright
          isplitr
          · ipureintro; exact he4
          iframe
          (try iexists some (x, s0), (h.log x (rmFileEnt j b i s0) (restrictN N (GMap.delete b h.cur))))
          isplitr
          · ipureintro; exact fun _ => rfl
          isplitr
          · ipureintro; exact fun J hJ => by simp [rmFileEnt, habs] at hJ
          iintro Hn
          dsimp only [rmFileOutN, logOut, claimOut, osLogged, rmFileEnt]; iframe; iframe #
          ipureintro; exact ⟨hs, hst⟩
    · -- committed: the name is gone in the caller's fraction
      obtain ⟨x, sx⟩ := xs
      isimp only [rmFileOutN, logOut, claimOut] at Hout
      icases Hout with ⟨⟨%hlo, Hlo⟩, Hn⟩
      unfold osLogged
      icases Hlo with ⟨%hlo2, #Hle, #Hll⟩
      wp_apply +noauto wp_osUnlinkSN_none R d b j N dq (DFrac.own q)
        (h.log x (rmFileEnt j b i sx) (restrictN N (GMap.delete b h.cur))) t s0 qc hb hbN
        (fun i' hJ => by simp [rmFileEnt, habs] at hJ) CoPset.subseteq_top CoPset.subseteq_top
        $$ Hos Hsi Hp Hn Hk as %e %he Hperm Hp Hn
      try wp_auto
      wp_apply wp_errnoErr
      try wp_auto
      iapply HΦ'
      try dsimp only
      by_cases he4 : e = W64 4
      · ileft
        isplitr
        · ipureintro; exact he4
        iframe
        iright; iexists (x, sx)
        dsimp only [rmFileOutN, logOut, claimOut, osLogged]; iframe; iframe #
        ipureintro; exact ⟨hlo, hlo2⟩
      · iright
        isplitr
        · ipureintro; exact he4
        iframe
        (try iexists some (x, sx), (h.log x (rmFileEnt j b i sx) (restrictN N (GMap.delete b h.cur))))
        isplitr
        · ipureintro; exact fun _ => rfl
        isplitr
        · ipureintro; exact fun J hJ => by simp [rmFileEnt, habs] at hJ
        iintro Hn
        dsimp only [rmFileOutN, logOut, claimOut, osLogged]; iframe; iframe #
        ipureintro; exact ⟨hlo, hlo2⟩
  -- after the unlink loop
  by_cases h0 : e = 0
  · subst h0
    simp only [errnoErr, ↓reduceIte]
    try wp_auto
    iapply HΦ
    ihave Hout := Hback $$ Hn
    iframe
    (try iexists o)
    (try iframe)
    ipureintro; intro _; exact ho rfl
  simp only [errnoErr, h0, ↓reduceIte]
  try wp_auto
  rw [recv_eq_func_mk]
  -- the rmdir loop
  wp_apply (os.wp_ignoringEINTR _
    iprop(name_ptr ↦ child d b ∗ osPathS R d dq j ∗ osCallPerm (callKey R d) qc ∗
      osNames j N (DFrac.own q) h')
    (fun e1 => iprop(⌜e1 ≠ W64 0⌝ ∗ name_ptr ↦ child d b ∗ osPathS R d dq j ∗
      osCallPerm (callKey R d) qc ∗ osNames j N (DFrac.own q) h')))
    $$ [Hname Hp Hperm Hn] as %e1 ⟨%he1, Hname, Hp, Hperm, Hn⟩
  · iframe
    iintro !>
    unfold os.eintrCall
    iintro %Φ' ⟨Hname, Hp, Hperm, Hn⟩ HΦ'
    rw [← recv_eq_func_mk]
    wp_call
    try wp_auto
    irename : (_ ↦ (_ : GoInterface) : IProp GF) => Hres0c
    wp_func_call; wp_call
    try wp_auto
    irename «$res0» => Hres0u
    icases osCallPerm_child R d b _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
    wp_stub syscall.fsRmdir.impl
    wp_apply +noauto wp_osCallBeginS R _ qc h.next CoPset.subseteq_top CoPset.subseteq_top
      $$ Hos Hsi Hperm Hlb as %t1 %s1 %hs1 Hk1 Hls1
    iclear Hls1
    wp_apply +noauto wp_osRmdirSN_none R d b j N dq (DFrac.own q) h' t1 s1 qc hb hbN hnd
      CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hp Hn Hk1 as %e1 %he1 Hperm Hp Hn
    try wp_auto
    wp_apply wp_errnoErr
    try wp_auto
    iapply HΦ'
    try dsimp only
    by_cases he4 : e1 = W64 4
    · ileft
      isplitr
      · ipureintro; exact he4
      iframe
    · iright
      isplitr
      · ipureintro; exact he4
      iframe
      ipureintro; exact he1
  have he1' : ¬ e1 = 0 := he1
  simp only [errnoErr, he1', ↓reduceIte]
  try wp_auto
  by_cases h20 : e1 = W64 20
  · subst h20
    try simp only [decide_true, Bool.not_true]
    try wp_auto
    try wp_alloc pe as Hpe
    try wp_auto
    iapply HΦ
    ihave Hout := Hback $$ Hn
    iframe
    (try iexists o)
    (try iframe)
    ipureintro; intro hc; cases hc
  · try simp only [decide_eq_false h20, Bool.not_false]
    try wp_auto
    try wp_alloc pe as Hpe
    try wp_auto
    iapply HΦ
    ihave Hout := Hback $$ Hn
    iframe
    (try iexists o)
    (try iframe)
    ipureintro; intro hc; cases hc

end proof

end EtcdGrove
end Perennial
