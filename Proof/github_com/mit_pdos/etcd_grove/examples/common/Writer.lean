/- Lean-first (no Rocq counterpart). The proof of `writer`: the loop over `tried[lo:hi]`; each Put
in a timeout context (`client.wp_WithTimeout_bg`, over the trust-boundary spec of
`context.WithTimeout(Background(), d)` and `context.ErrAny`); each through the client's `KV` field
(`client.client_Put_kv`, `kv.Put.spec`) with the caller's write update of the put; each successful
Put's reply gives the caller's fact (`OkF`, from the update's result and the reply's revision),
logged under the lock. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.common.Writer
public import Perennial.Proof.context.Link
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.common.Assumptions]

theorem Writer.wp_proof
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG)) :
    Writer.spec (GF := GF) (hG := hG) := by
  intro CS CRE CEC cl api γk QW OkF w tsl tried lo hi hP hAs hlo hlh hhi hsz
  wp_start as ⟨#Hkvf, #Hkv, #Ht, #Hau, #Hconv, #Hmu⟩
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave %Htl := ownSlice_len $$ Ht
  (try wp_auto)
  ihave #Hnil : optsAt (GF := GF) slice.nil [] $$ []
  · iunfold optsAt
    iexists ([] : List GoFunc)
    isplitl
    · iapply ownSlice_nil
    isplitl
    · ipureintro; rfl
    imodintro
    iintro %i %f %g %Hf %Hg
    simp at Hf
  ihave HI : (∃ (k : w64), "k" ∷ k_ptr ↦ k ∗
      "%Hk" ∷ ⌜sint.Z lo ≤ sint.Z k ∧ sint.Z k ≤ sint.Z hi⌝ : IProp GF) $$ [k]
  · iexists lo
    iframe
    ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z tsl.len := ⟨by word, by have := Htl.1; word⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    list_elem tried (sint.nat k) as x
    wp_apply wp_load_slice_index tsl (sint.Z k) tried DFrac.discard x Hb'.1 $$ [Ht] as -
    · iframe #; ipureintro; exact Hx_lookup
    have hxP : (x.Key', x.Val') ∈ tried.map pairOf :=
      List.mem_map.2 ⟨x, List.mem_of_getElem? Hx_lookup, rfl⟩
    ihave Hau1 := Hau $$ %x.Key' %x.Val' %hxP
    (try wp_auto)
    -- `ctx, cancel := context.WithTimeout(context.Background(), RequestTimeout)`
    wp_apply context.wp_Background
    (try wp_auto)
    wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
      as %cctx %cd %cancel ⟨#Hcancel, #Hctx, #Hce, -⟩
    (try wp_auto)
    wp_apply (client.client_Put_kv cl api γk false cctx cd x.Key' x.Val' slice.nil
        (QW x.Key' x.Val') (hsz x (List.mem_of_getElem? Hx_lookup)).put) $$ [Hau1] as %resp %err Hout
    · iframe #
    -- `cancel()`
    (try wp_auto)
    wp_apply Hcancel
    icases Hout with (⟨%Herr, %m, %σ, #Hm, HQ, %Hs⟩ | ⟨%Herr, -⟩)
    · subst Herr
      ihave #Hok : OkF ⟨m.hdr.revision, x.Key', x.Val'⟩ $$ [HQ]
      · rw [Hs.1]
        iapply Hconv $$ HQ
        ipureintro; exact ⟨Hs.2.1, Hs.2.2.1⟩
      (try wp_auto)
      wp_apply sync.Mutex.wp_Lock $$ [] as ⟨Hown, Hinv⟩
      · iframe #
      iunfold wsInvF at Hinv
      icases Hinv with ⟨%osl, %oks, Hof, Hos, Hocap, #Hoks⟩
      iunfold putRespMsg at Hm
      icases Hm with ⟨%Hnn, %h, %pk, #Hhd, #Hhf, -⟩
      iunfold hdrFull at Hhf
      icases Hhf with ⟨%Hhn, -, -, #Hrevf, -, -⟩
      (try wp_auto)
      wp_apply wp_slice_literal (l := [(⟨m.hdr.revision, x.Key', x.Val'⟩ : wrec)])
      isplitr
      · ipureintro; rfl
      iintro %l1 ⟨Hl1, _⟩
      simp only [go.arrayLiteralSize, List.foldl]
      (try wp_auto)
      wp_apply wp_slice_append $$ [$Hos $Hocap $Hl1] as %osl' ⟨Hos, Hocap, -⟩
      (try wp_auto)
      wp_apply (sync.Mutex.wp_Unlock (structFieldRef github_com.mit_pdos.etcd_grove.examples.common.Writes go!"Mu" w) (wsInvF w OkF)) $$ [Hown Hof Hos Hocap]
      · iframe #
        iframe Hown
        iunfold wsInvF
        iexists osl', oks ++ [⟨m.hdr.revision, x.Key', x.Val'⟩]
        iframe
        inext
        imodintro
        iapply BigSepL.bigSepL_snoc.2
        iframe #
      (try wp_auto)
      wp_for_post
      iframe
      iexists k + W64 1
      iframe
      ipureintro; constructor <;> word
    · cases err with
      | nil => exact absurd rfl Herr
      | ok e => ?_
      (try wp_auto)
      wp_for_post
      iframe
      iexists k + W64 1
      iframe
      ipureintro; constructor <;> word
  · (try wp_auto)
    iapply HΦ; itrivial

end proof

end common
end EtcdGrove
end Perennial
