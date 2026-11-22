/-
The proof of `Run` (`Net/Spec/.../lib/remote/Run.lean`): `perclient.Run` with the library state
`pendLib`, the inputs `iv i`, the mask `R.Eop ∪ pendN` and the counter clock at
`nroot.@"remoteClock"` (disjoint from `lintestN`). Its `applySpecId` for the closure
`apply(c, in) = Do(addrs[c], in, codec, d)`: the update lintest hands over (its `▷` stripped by a
later credit) becomes `Do`'s choice through `pend_choice`, with `K o` lintest's continuation; `Do`
returns `ov o` or `unk i` with `K` of it, applied at the value returned (`S.ioOk` from `PendDec`).
`pend_choice` and `readNoop` open `pendCtx` without a credit, so `R.sysState` must be timeless.
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.Run
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.Do
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.lintest.perclient.Run
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.lintest.CounterClock

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine EtcdGrove.lintest

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.mit_pdos.etcd_grove.examples.lib.remote.Assumptions]
variable [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable {St I O : Type} [DecidableEq I] [Pos.Countable I] [Pos.Countable O]

theorem Run.wp_proof
    (wp_Do : Do.spec (GF := GF) (hG := hG) (St := St) (I := I) (O := O))
    (wp_perclientRun : EtcdGrove.perclient.Run.spec (GF := GF) (hG := hG))
    (wp_CounterClock : CounterClock.spec (GF := GF) (hG := hG)) :
    Run.spec (GF := GF) (hG := hG) (St := St) (I := I) (O := O) := by
  intro R S γ m addrs addrL cd gen ops d tmo HpE HlE HS Hinj HT Hrb H31 Hops Hmul
  haveI := HT
  wp_start as ⟨#Hcc, #Hm, #Hgen, #Haddrs, #Hra, #Hmap, #Hcd, #Hpend, Hlib⟩
  wp_auto
  ipersist addrs
  ipersist codec
  ipersist d
  wp_apply wp_CounterClock (nroot.@"remoteClock") Hrb as %clock ⟨%clockVal, #Hclock, Ht0⟩
  ihave %Hal := ownSlice_len _ _ _ $$ Haddrs
  wp_apply wp_perclientRun (EtcdGrove.linkv.PSet St I) S m _ gen clock (fun x => iprop(∃ i, ⌜x = R.iv i⌝))
    (pendLib S γ) clockVal (W64 0) (R.Eop ∪ ↑pendN) ↑(nroot.@"remoteClock") addrs.len ops tmo
    HlE (mask_ndot_ne' nroot "lintest" "remoteClock" (by decide)) Hal.2 H31 Hops Hmul $$ [Hlib Ht0]
  · iframe
    iframe #
    unfold EtcdGrove.perclient.applySpecId
    iintro %id %x
    imodintro
    iintro %Φ' ⟨%Hid, ⟨%i, %Hx⟩, Htt⟩ HAU
    subst Hx
    wp_auto_lc 1
    simp only [Hid, and_self, ↓reduceIte]
    have hlt : (sint.Z id).toNat < addrL.length := by
      have e : sint.nat addrs.len = (sint.Z addrs.len).toNat := rfl
      omega
    obtain ⟨a, ha⟩ : ∃ a, addrL[(sint.Z id).toNat]? = some a := ⟨_, List.getElem?_eq_getElem hlt⟩
    ihave #Ha := BigSepL.bigSepL_lookup
      (Φ := fun _ a => remoteAddr (Gg := hG.goose_globalGS) R a) ha $$ Hra
    wp_apply wp_load_slice_index addrs (sint.Z id) addrL DFrac.discard a Hid.1 $$ [Haddrs] as -
    · iframe Haddrs
      ipureintro
      exact ha
    ihave Hch := pend_choice (Gg := hG.goose_globalGS) R HpE S HS Hinj γ i
      (fun o => iprop(∀ o', (⌜∀ s, S.M.step s (R.iv i, o') = S.M.step s (R.iv i, o)⌝ ∗
        S.ioOk (R.iv i) o' ∗ threadTok) -∗ Φ' #o')) $$ Hpend Hlc1 [HAU]
    · inext
      unfold linAU
      iexact HAU
    wp_apply wp_Do R a i _ _ cd d $$ [Hch] as %v Hv
    · iframe #
      iframe Hch
      cases hw : R.B.isWrite i
      · simp only [Bool.false_eq_true, ↓reduceIte]
        iapply readNoop (Gg := hG.goose_globalGS) R HpE S γ i hw
        iexact Hpend
      · simp only [↓reduceIte]
        itrivial
    icases Hv with (⟨%o, %Hvo, HK⟩ | ⟨%Hvu, HK⟩)
    · iapply HK
      iframe Htt
      isplit
      · ipureintro; intro s; rw [Hvo]
      · rw [Hvo]; iapply HS.ioOk_ok
    · iapply HK
      iframe Htt
      isplit
      · ipureintro; intro s; rw [Hvu]
      · rw [Hvu]; iapply HS.ioOk_err
  iintro %r %Hr
  wp_auto
  iapply HΦ
  ipureintro
  exact Hr

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.remote
end Perennial
