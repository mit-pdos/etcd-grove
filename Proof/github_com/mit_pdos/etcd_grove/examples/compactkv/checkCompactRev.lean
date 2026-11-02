/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/compactkv/checkCompactRev.lean` (C3's watch
side, 2026-11-02). Lean-first (no Rocq counterpart).

The steps: the client's watcher (`isNewClient_watcher`); a watch of `key` from revision `2` at the
rounds' read update (`oneValAu`), its channel at `stateCmpOk` (each response's compaction revision
the cluster's permit, `isRespChan_of_state_cmp`); `CompactRev`: on `false`, return; on `true`, the
response's permit (`cmpOkOf_permit`: the revision plus the retention `1` reached), the rounds'
counter's bound (`roundsInv_revLb`, the read-side law), and a latest `Get` reading at a revision at
least it (`client_Get_rev`): the check takes its `else` branch.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.compactkv.checkCompactRev
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.CompactRev
public import Spec.go_etcd_io.etcd.client.v3.WithRev
public import Spec.go_etcd_io.etcd.client.v3.watcher__Watch
public import Perennial.Spec.context.Background
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx
public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace compactkv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver client

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.compactkv.Assumptions]

set_option maxHeartbeats 800000 in
theorem checkCompactRev.wp_proof
    (wp_Background : context.Background.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_WithRev : WithRev.spec (GF := GF) (hG := hG))
    (wp_Watch : watcher.Watch.spec (GF := GF) (hG := hG))
    (wp_CompactRev : common.CompactRev.spec (GF := GF) (hG := hG)) :
    checkCompactRev.spec (GF := GF) (hG := hG) := by
  intro CS CRE CEC cl key R E γr cid mid γf γl γv keys val hkl hcr hAs
  wp_start as ⟨#Hnc, #HWF, #Hregs, #H00, #Hinv, #Hkvi⟩
  ihave #Hcci : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  ihave #Pcom : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.common $$ []
  · iPkgInit
  -- the client's `Watcher`, with the watch server's facts (D19f)
  ihave ⟨%w, %conn, %wc, %lgw, %ics, #HWf, #Hcw⟩ := isNewClient_watcher wp_ErrAny hAs cl
    [go!"127.0.0.1:23794"] (srvWEnv R go!"127.0.0.1:23794" [] null null go!"k" null γr.kv)
    rfl rfl rfl $$ [Pcli Ppb Pctx Hnc HWF]
  · iframe #
  (try wp_auto)
  -- `cctx, ccancel := context.WithCancel(context.Background())`
  wp_apply context.wp_Background
  wp_apply context.wp_WithCancel_Background iprop(True) $$ [$Pctx $Hcci]
    as %cctx %γctx %ccancel ⟨#Hccancel, #Hcctx, -⟩
  (try wp_auto)
  -- the watch's option, `WithRev(2)`
  wp_apply wp_WithRev (W64 2) as %f2 #Hf2
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %osl ⟨Hosl, -⟩
  ipersist Hosl
  (try wp_auto)
  generalize hosl : slice.mk osl _ _ = optsSl
  ihave #Hopts : optsAt optsSl ([withRevM (W64 2)] : List (OpFull → OpFull)) $$ []
  · iunfold optsAt
    iexists _
    iframe Hosl
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %f %g %Hf %Hg
    rcases i with _ | i
    · cases Hf; cases Hg; iexact Hf2
    · simp at Hf
  -- the rounds' read update
  ihave #Hau := oneValAu γr γf γl γv keys val $$ Hinv
  iunfold kvReadAu at Hau
  iunfold kvAu at Hau
  -- `cch := cli.Watcher.Watch(cctx, key, clientv3.WithRev(2))`
  wp_apply (wp_Watch w _ γr.kv cctx
      ({ Values := ∅, Deadline := none, Done_gn := γctx, PDone := iprop(True) } :
        context.ContextDesc (IProp GF))
      key optsSl ([withRevM (W64 2)] : List (OpFull → OpFull)) (W64 2)
      (fun σ => iprop(⌜oneValW val σ.changes⌝)) 0) $$ [] as %wch %γw ⟨#Hsp, Hcons, Hcur⟩
  · iframe #
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro
      refine ⟨?_, ?_, by decide, ?_⟩
      · simp [opWatchModel, opFold, OpFull.getInit, withRevM, OpFull.isRangeWatch, OpFull.newOp,
          OpModel.zero]
      · simp [opWatchPanics, OpFull.watchPanics, opWatchModel, opFold, OpFull.getInit, withRevM,
          OpFull.newOp, OpModel.zero]
      · unfold watchSizeOk
        simp [opWatchModel, opFold, OpFull.getInit, withRevM, OpFull.newOp, OpModel.zero]
        omega
    iintro !> %h
    exact absurd h.2 (Nat.lt_irrefl 0)
  ihave #Hwch := common.isRespChan_of_state_cmp wch _ γw _ (fun σ => iprop(⌜oneValW val σ.changes⌝)) _
    $$ Hsp
  (try wp_auto)
  ihave Hcons : etcdWatchConsumer γw 0 (W64 2 - W64 1) $$ [Hcons Hcur]
  · unfold etcdWatchConsumer
    iexists []
    iframe Hcons Hcur
    ipureintro; rfl
  -- `crev, cok := common.CompactRev(cch)`
  wp_apply (wp_CompactRev _ wch γw (W64 2 - W64 1)) $$ [Hcons] as %crev %cok Hcr
  · iframe; iframe #
  (try wp_auto)
  wp_apply Hccancel $$ [] as -
  · itrivial
  (try wp_auto)
  cases cok
  · (try wp_auto)
    iapply HΦ; itrivial
  (try wp_auto)
  ihave ⟨%c', %v, %r, Hok, %Hv⟩ := Hcr $$ %rfl
  iunfold common.stateCmpOk at Hok
  icases Hok with ⟨-, #Hcmp0⟩
  ihave #Hcmp : cmpOkOf γr.kv crev $$ []
  · rw [← Hv.1]; iexact Hcmp0
  -- the response's permit: its revision plus the retention reached
  ihave ⟨%Hpos, #Hlb⟩ := cmpOkOf_permit γr.kv crev Hv.2 $$ Hcmp
  have hn : ((((sint.Z crev + γr.kv.cret).toNat : Nat) : Int)) = sint.Z crev + 1 := by
    rw [hcr]; omega
  imod (roundsInv_revLb γr γf γl γv keys val (sint.Z crev + γr.kv.cret).toNat) $$ Hkvi Hinv []
    with #HrvLb
  · rw [hn]; iExactEq Hlb; rw [hcr]; rfl
  -- `lctx, lcancel := context.WithTimeout(...)`; `lresp, err := cli.Get(lctx, key)`
  (try wp_auto)
  wp_apply wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
    as %lctx %lcd %lcancel ⟨#Hlcancel, #Hlctx, #Hlce, -⟩
  (try wp_auto)
  ihave #Hnil : optsAt (GF := GF) slice.nil [] $$ []
  · iunfold optsAt
    iexists ([] : List GoFunc)
    isplitl
    · iapply ownSlice_nil
    isplitl
    · ipureintro; rfl
    iintro !> %i %f %g %Hf
    simp at Hf
  imod monoNatLbOwn_0 (GF := GF) γr.committed with #Hc0
  wp_apply (client_Get_rev cl go!"127.0.0.1:23794" _ E γr γf γl γv keys val key
      (sint.Z crev + γr.kv.cret).toNat (W64 0) cid mid lctx lcd slice.nil []
      (opSizeOk_opGetModel (K := 2) (E := 0) (V := 0) (optsKeep_nil _ _ _) hkl (by decide)))
      as %lresp %lerr Hget
  · iframe #
    iunfold committedAtLeast
    iExactEq Hc0; rfl
  (try wp_auto)
  wp_apply Hlcancel
  icases Hget with (⟨%Hgerr, %mg, #Hmg, %Hgrev⟩ | %Hgfail)
  rotate_left
  · obtain ⟨Hgerr, -⟩ := Hgfail
    cases lerr with
    | nil => exact absurd rfl Hgerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Hgerr
  (try wp_auto)
  iunfold rangeRespMsg at Hmg
  icases Hmg with ⟨%Hnn', %h', %sl, %ps, #Hh', #Hhf', -⟩
  iunfold hdrFull at Hhf'
  icases Hhf' with ⟨%Hhn', -, -, #HrevF', -, -⟩
  have Hnlt : ¬ sint.Z mg.hdr.revision < sint.Z (crev + W64 1) := by
    have : sint.Z (crev + W64 1) = sint.Z crev + 1 := by
      have := mg.hdr.revision
      rw [hn] at Hgrev
      word
    rw [this]; rw [hn] at Hgrev; omega
  wp_auto
  try simp only [Hnlt, decide_false, ↓reduceIte]
  wp_auto
  iapply HΦ; itrivial

end proof

end compactkv
end EtcdGrove
end Perennial
