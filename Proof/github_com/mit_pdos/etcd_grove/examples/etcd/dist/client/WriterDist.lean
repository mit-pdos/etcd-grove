/-
Proof of `Spec/.../dist/client/WriterDist.lean` (#50 N10a). Lean-first (no Rocq counterpart).

`etcdstart.Writer.wp_proof`'s loop verbatim, with each `cli.Put` the promoted `(*kv).Put` of the
client's `KV` field (`ptr_Put_unfold`) and its contract the interim `KV_Put_dist` (a hypothesis) at
the cluster's view, as `wp_cliPut` does (N9a's `KVCallsDist.lean`), keeping the reply's revision.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.WriterDist
public import Spec.context.WithTimeoutBackground
public import Spec.context.ErrAny
public import Perennial.Proof.context.Link
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net client go_etcd_io.etcd.server.v3.etcdserver
open etcd_dist etcdstart

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

set_option maxHeartbeats 800000 in
theorem Writer_dist.wp_proof
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_KV_Put : KV_Put_dist.spec (GF := GF) (hG := hG)) :
    Writer_dist.spec (GF := GF) (hG := hG) := by
  intro π cl api eps V Γ QW OkF w γt tsl tried lo hi hauth hP hAs hlo hlh hhi hsz
  wp_start as ⟨Hlt, Htk, #Hkc, #Ht, #Hau, #Hconv, #Hmu⟩
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave %Htl := ownSlice_len $$ Ht
  ihave #Hkc' := Hkc
  iunfold kvClientAt at Hkc'
  icases Hkc' with ⟨-, -, #Hkvf, -⟩
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
  ihave HI : (∃ (k : w64), "k" ∷ k_ptr ↦ k ∗ "Hlt" ∷ levelTok 0 ∗ "Htk" ∷ token γt ∗
      "%Hk" ∷ ⌜sint.Z lo ≤ sint.Z k ∧ sint.Z k ≤ sint.Z hi⌝ : IProp GF) $$ [k Hlt Htk]
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
    -- `resp, err := cli.Put(ctx, p.Key, p.Val)`: the promoted `(*kv).Put`, `KV_Put_dist`
    rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Put_unfold.method_unfold]
    wp_pures
    wp_auto
    have hnp : ¬ (opPutModel x.Key' x.Val' []).putPanics := by
      simp [OpFull.putPanics, opPutModel, opFold, OpFull.putInit, OpFull.newOp, OpModel.zero]
    have ht : (opPutModel x.Key' x.Val' []).t = W64 2 := by
      simp [opPutModel, opFold, OpFull.putInit, OpFull.newOp, OpModel.zero]
    have hl : (putWireOf (opPutModel x.Key' x.Val' [])).leaseID = W64 0 := by
      simp [putWireOf, opPutModel, opFold, OpFull.putInit, OpFull.newOp, OpModel.zero]
    have hs := (hsz x (List.mem_of_getElem? Hx_lookup)).put
    wp_apply (wp_KV_Put cl api eps V Γ cctx cd x.Key' x.Val' slice.nil [] (QW x.Key' x.Val') hauth)
      $$ [Hlt Hau1] as %resp %err ⟨Hlt, Hout⟩
    · iframe Hlt Hau1
      iframe #
      (try (ipureintro; first | exact ⟨⟨hnp, ht, hl⟩, hs⟩ | exact ⟨hnp, ht, hl, hs⟩ | exact hs |
        exact ⟨hnp, ht, hl⟩))
    -- `cancel()`
    (try wp_auto)
    wp_apply Hcancel
    icases Hout with (⟨%Herr, %m, %σ, #Hm, HQ, %Hs, -⟩ | %Herr)
    · subst Herr
      ihave #Hok : OkF ⟨m.hdr.revision, x.Key', x.Val'⟩ $$ [HQ]
      · rw [Hs.1]
        iapply Hconv $$ HQ
        ipureintro; exact ⟨Hs.2.2.1, Hs.2.2.2.1⟩
      (try wp_auto)
      wp_apply sync.Mutex.wp_Lock $$ [] as ⟨Hown, Hinv⟩
      · iframe #
      iunfold wsInvT at Hinv
      icases Hinv with (Hinv | ⟨%sl0, -, Htk'⟩)
      rotate_left
      · iexfalso; iapply (token_exclusive γt) $$ Htk Htk'
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
      wp_apply (sync.Mutex.wp_Unlock (structFieldRef github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Writes go!"Mu" w) (wsInvT w OkF γt)) $$ [Hown Hof Hos Hocap]
      · iframe #
        iframe Hown
        iunfold wsInvT
        ileft
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
    · obtain ⟨Herr, -⟩ := Herr
      cases err with
      | nil => exact absurd rfl Herr
      | ok e => ?_
      (try wp_auto)
      wp_for_post
      iframe
      iexists k + W64 1
      iframe
      ipureintro; constructor <;> word
  · (try wp_auto)
    iapply HΦ; iframe Hlt Htk

end proof

end etcd_dist_client
end EtcdGrove
end Perennial
