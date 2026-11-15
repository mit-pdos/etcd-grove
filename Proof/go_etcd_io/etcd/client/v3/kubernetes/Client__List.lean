/-
Lean-first (no Rocq counterpart).

The proof of `kubernetes.Client.List` (k8s 7e-1): the range `[start, GetPrefixRangeEnd prefix)` with
the options `[WithRange, WithLimit(opts.Limit), WithRev(opts.Revision)]` (`start` the continue key or
the prefix), then `client_range_any` through the client's `*kv` (as `Client.Get`'s proof); the
answer is a page (`rangeReply_state_at`, `srvRangeOk_page`); the reply's `Kvs` slice is owned
(`rangeRespKvsOwn`, the K1 ownership claim); an error's future-revision soundness from
`client_range_any`'s `rangeErrOut` (`rangeErrReply_future`). The prophecy (`NewProph`, then
`ResolveU64` of the response's revision) picks the read update `Q R` at the response's revision.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet
public import Proof.go_etcd_io.etcd.client.v3.kubernetes.ListPage
public import Spec.go_etcd_io.etcd.client.v3.kubernetes.Client__List
public import Spec.go_etcd_io.etcd.client.v3.WithRev
public import Spec.go_etcd_io.etcd.client.v3.WithLimit
public import Spec.go_etcd_io.etcd.client.v3.WithRange
public import Spec.go_etcd_io.etcd.client.v3.GetPrefixRangeEnd
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Proph
public import Perennial.Proof.github_com.goose_lang.primitive.Link

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kubernetes

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open go_etcd_io.etcd.server.v3.etcdserver etcd_txnlin EtcdGrove.k8s

/-- `List`'s range passes the server's checks when its start key is not empty. -/
theorem rangeCheck_page (pfx start : GoString) (rev lim : w64) (hk : start ≠ []) :
    v3rpc.rangeCheck (pageOp pfx start rev lim) = none := by
  unfold v3rpc.rangeCheck
  simp [txn.rangeOpOf, hk, v3rpc.sortOrderKnown, v3rpc.sortTargetKnown]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.kubernetes.Assumptions]

theorem sepL2_of_kvsIs (ps : List Loc) (kvs : List EtcdKv) :
    txn.kvsIs (GF := GF) ps kvs ⊢ [∗list] q;kv ∈ ps;kvs, txn.kvIs q kv := by
  unfold txn.kvsIs
  iintro ⟨%Hl, #H⟩
  iapply BigSepL2.bigSepL2_intro
  isplit
  · ipureintro; exact Hl
  imodintro
  iintro %k %p %v %Hp %Hv
  iapply H $$ %k %p %v %Hp %Hv

theorem Client.List.wp_proof (wp_WithRev : WithRev.spec (GF := GF) (hG := hG))
    (wp_WithLimit : WithLimit.spec (GF := GF) (hG := hG))
    (wp_WithRange : WithRange.spec (GF := GF) (hG := hG))
    (wp_GetPrefixRangeEnd : GetPrefixRangeEnd.spec (GF := GF) (hG := hG)) :
    Client.List.spec (GF := GF) (hG := hG) := by
  intro _ _ kc ms V ci cd pfx opts Q0 hpl hcl hrev hlim hcont
  wp_start as ⟨#Hcl, #Hregs, #Hctx, #Hce, Hau0⟩
  wp_auto
  wp_apply (linkv.wp_NewProph_typed (τ := w64) github_com.goose_lang.primitive.wp_NewProph)
    as %pr %xs Hpr
  ispecialize Hau0 $$ %(xs.getD 0 (W64 0))
  imod Hau0 with #Hau
  generalize hQ : Q0 (xs.getD 0 (W64 0)) = Q
  (try wp_auto)
  generalize hstart : (if opts.Continue' = [] then pfx else opts.Continue') = start
  have hpst : pfx <+: start := by
    rw [← hstart]; split
    · exact List.prefix_refl _
    · rcases hcont with h | h
      · contradiction
      · exact h
  have hstl : start.length ≤ opKeyMax := by rw [← hstart]; split <;> assumption
  wp_if_destruct
  all_goals (try wp_auto)
  all_goals (
    ihave rangeStart : rangeStart_ptr ↦ start $$ [rangeStart]
    · rw [← hstart]; simp only [Hif, ↓reduceIte]; iexact rangeStart
    wp_apply wp_GetPrefixRangeEnd
    (try wp_auto)
    wp_apply wp_WithRange as %f1 #Hf1
    wp_apply wp_WithLimit as %f2 #Hf2
    wp_apply wp_WithRev as %f3 #Hf3
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    ipersist Hsl
    wp_auto
    generalize hsl : slice.mk sl _ _ = optsSl
    have hfs : ([f1, zero_val GoFunc, zero_val GoFunc].set (sint.nat (W64 (0 + 1))) f2).set
        (sint.nat (W64 (0 + 1 + 1))) f3 = [f1, f2, f3] := by
      show ([f1, zero_val GoFunc, zero_val GoFunc].set 1 f2).set 2 f3 = [f1, f2, f3]; rfl
    ihave #Hopts : optsAt optsSl ([withRangeM (prefixRangeEnd pfx), withLimitM opts.Limit',
        withRevM opts.Revision'] : List (OpFull → OpFull)) $$ []
    · iunfold optsAt
      iexists _
      iframe Hsl
      isplitr
      · ipureintro; rw [hfs]; rfl
      imodintro
      iintro %i %f %g %Hf %Hg
      rw [hfs] at Hf
      rcases i with _ | _ | _ | i
      · cases Hf; cases Hg; iexact Hf1
      · cases Hf; cases Hg; iexact Hf2
      · cases Hf; cases Hg; iexact Hf3
      · simp at Hf
    iunfold isNewClient at Hcl
    icases Hcl with ⟨-, -, ⟨%api, #Hkvf, #Hkv⟩, -⟩
    imod (client.srvStart_alloc (GF := GF) ms) with #Hst
    ihave #Hopts' := optsAt_res optsSl _ iprop(True) $$ Hopts
    ihave #Hrr := client.kvRegs_range ms $$ Hregs
    ihave #Hst' := client.srvStart_both ms $$ Hst
    have hm : ∀ (k : Nat) (x : client.SrvAt GF), ms[k]? = some x →
        iprop(⌜Q = fun _ => iprop(True)⌝ ∨ kvReadAu x.γr.kv Q) ⊢
        iprop(⌜Q = fun _ => iprop(True)⌝ ∨
          (⌜(rangeWireOf (opGetModel start [withRangeM (prefixRangeEnd pfx), withLimitM opts.Limit',
              withRevM opts.Revision'])).base.serializable = false⌝ ∗ kvReadAu x.γr.kv Q)) :=
      fun _ _ _ => by
        iintro (%h | #h)
        · ileft; ipureintro; exact h
        · iright; iframe h; ipureintro; rfl
    ihave #Hau' := (BigAndL.bigAndL_mono hm) $$ Hau
    have hel : (prefixRangeEnd pfx).length ≤ 2 ^ 27 := by
      have := prefixRangeEnd_length_le pfx
      simp only [opKeyMax] at hpl
      omega
    wp_auto
    iapply wp_fupd
    wp_apply (client.client_range_any api ms (W64 0) ci cd start optsSl
        [withRangeM (prefixRangeEnd pfx), withLimitM opts.Limit', withRevM opts.Revision']
        iprop(True) Q []
        (opSizeOk_opGetModel (K := 2 ^ 27) (E := 2 ^ 27) (V := 0)
          (optsKeep_cons (withRangeM_keep hel) (optsKeep_cons (withLimitM_keep _)
            (optsKeep_cons (withRevM_keep _) (optsKeep_nil _ _ _))))
          hstl (by decide))) $$ []
      as %resp %err ⟨-, Hout, #Heo⟩
    · iframe #
      isplitl []
      · rw [show (opGetModel start [withRangeM (prefixRangeEnd pfx), withLimitM opts.Limit',
            withRevM opts.Revision']).base.sortSet = false from rfl]
        iapply sortNamesIf_false
      ipureintro
      first
        | rfl
        | (refine ⟨?_, rfl⟩; unfold opGetPanics opFold OpFull.newOp; simp [withRevM, withLimitM, withRangeM])
    icases Hout with (⟨%Herr, %m, Hm, %x, %hx, #Hq⟩ | ⟨⟨%Herr, %Hrn⟩, #Hke⟩)
    · subst Herr
      ihave Hs := rangeReply_state_at x.E x.γr (W64 0) x.cid x.mid _ [] Q m rfl $$ Hq
      icases Hs with ⟨%σ, #HQ, %Hσ⟩
      obtain ⟨hsel, hcnt, hrevσ, hle, hb, -⟩ := Hσ
      rw [rangeWireOf_page] at hsel hcnt hle
      have hbr : (pageOp pfx start opts.Revision' opts.Limit').base.rev = opts.Revision' := rfl
      rw [hbr] at hsel hcnt hle
      obtain ⟨hkvs, hcount⟩ :=
        srvRangeOk_page pfx start opts.Revision' opts.Limit' _ m.kvs m.more hpst hlim hsel
      iunfold rangeRespMsgO at Hm
      icases Hm with ⟨Hrecv, Hown⟩
      iunfold rangeRespRecv at Hrecv
      icases Hrecv with ⟨%Hnn, %h, #Hh, #Hhf, #Hmore, #Hcount⟩
      iunfold rangeRespKvsOwn at Hown
      icases Hown with ⟨%sl2, %ps, #Hkvf2, Hsl2, #Hkvs⟩
      iunfold hdrFull at Hhf
      icases Hhf with ⟨%Hhn, -, -, #Hrevf, -, -⟩
      wp_auto
      wp_apply (linkv.wp_ptr_ResolveU64_typed github_com.goose_lang.primitive.ProphId.wp_ResolveU64)
        $$ [$p $Hpr] as %xs1 ⟨%Hx1, p, Hpr⟩
      (try wp_auto)
      subst Hx1; subst hQ
      isimp only [List.getD_cons_zero] at HQ
      imodintro
      iapply HΦ
      ileft
      isplitl []
      · ipureintro; rfl
      iexists σ
      rw [← hrevσ]
      iframe HQ
      isplitl []
      · ipureintro; exact ⟨hle, hb⟩
      unfold listRespIs
      isplitl []
      · ipureintro
        simp only []
        refine ⟨hrevσ, ?_⟩
        rw [hcnt, hcount]
        simp [limN]
      iexists ps
      simp only []
      iframe Hsl2
      simp only [↓reduceIte]
      rw [← hkvs]
      iapply sepL2_of_kvsIs
      iexact Hkvs
    · cases err with
      | nil => exact absurd rfl Herr
      | ok ei => ?_
      wp_auto
      imodintro
      iapply HΦ
      iright
      iunfold kvErr at Hke
      icases Hke with ⟨%Hce, #Hse, #Hcl⟩
      iframe Hse Hcl
      isplitl []
      · ipureintro; exact Herr
      isplitl []
      · ipureintro; exact Hce
      -- the future-revision error's soundness
      iintro %Hg
      iunfold k8s.rangeErrSound
      imodintro
      iintro %Hd
      ihave Ho := Heo $$ %rfl
      iunfold client.rangeErrOut at Ho
      have hg2 := And.intro Herr Hg.2
      ihave Ho2 := Ho $$ %hg2
      iunfold client.rangeErrΨ at Ho2
      have hsne : start ≠ [] := by
        intro h; rw [h] at hpst; exact Hg.1 (List.prefix_nil.1 hpst)
      have hck : v3rpc.rangeCheck
          (rangeWireOf (opGetModel start [withRangeM (prefixRangeEnd pfx), withLimitM opts.Limit',
            withRevM opts.Revision'])) = none := by
        rw [rangeWireOf_page]; exact rangeCheck_page pfx start _ _ hsne
      ihave Ho3 := Ho2 $$ %hck
      icases Ho3 with ⟨Hf, -⟩
      ihave Hf2 := Hf $$ %Hd
      icases Hf2 with ⟨%x, %hx, #Hr⟩
      ihave Hs := rangeErrReply_future x.E x.γr (W64 0) [] _ Q rfl $$ Hr
      icases Hs with ⟨%σ, #HQ, %Hσ⟩
      subst hQ
      iexists (xs.getD 0 (W64 0)), σ
      iframe HQ
      ipureintro
      have hbr : (rangeWireOf (opGetModel start [withRangeM (prefixRangeEnd pfx),
          withLimitM opts.Limit', withRevM opts.Revision'])).base.rev = opts.Revision' := rfl
      rw [hbr] at Hσ
      unfold sint.nat
      word)

end proof

end kubernetes
end EtcdGrove
end Perennial
