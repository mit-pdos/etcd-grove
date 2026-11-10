/- Lean-first (no Rocq counterpart). The proof of `stream.act` (proved).

The callees in call order: `pick` (the weights), `watch`, `cancel`, `stream.pick`,
`RequestProgress`, `RequestProgressAll`, `Rev` (through `shapes.law`), `inBounds`, `genKey`
`context.TODO`, `Watch`, `check`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.stream__act
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__genKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.pick
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.stream__watch
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.stream__cancel
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.stream__pick
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.inBounds
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.check
public import Spec.context.TODO
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.StreamLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

set_option maxHeartbeats 3200000 in
theorem stream.act.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (errVars : mvcc.api.errVars.law (GF := GF))
    (wp_pickA : EtcdGrove.mvccfull.pick.spec (GF := GF) (hG := hG))
    (wp_stream_watch : stream.watch.spec (GF := GF) (hG := hG))
    (wp_stream_cancel : stream.cancel.spec (GF := GF) (hG := hG))
    (wp_stream_pick : stream.pick.spec (GF := GF) (hG := hG))
    (wp_inBounds : inBounds.spec (GF := GF) (hG := hG))
    (wp_runner_genKey : runner.genKey.spec (GF := GF) (hG := hG))
    (wp_ctxTODO : context.TODO.spec (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG)) :
    stream.act.spec (GF := GF) (hG := hG) := by
  intro T q C
  haveI : ∀ ws γ ι, Persistent (isMvccWatchStream (GF := GF) ws γ ι) := hpers.2.1
  haveI : ∀ kv γ, Persistent (isMvcc (GF := GF) kv γ) := hpers.1
  haveI := streamCtx_persistent hpers T
  wp_start as ⟨#Hctx0, Hreg⟩
  ihave Hctx := Hctx0
  iunfold streamCtx at Hctx
  icases Hctx with ⟨Hep, #Fx, #Fm, #Fkv, #Fws, #Fwm, #Hws, #Hinv, #Hmu, #Hstop⟩
  iunfold epCtx at Hep
  icases Hep with ⟨Hrn, #Hinc, #Hregs⟩
  iunfold rnCtx at Hrn
  icases Hrn with ⟨#Hpkg, #Hmpkg, #Hkeys, %Hkne, #HrH, #Hhist, #Hcfg, #Hwa, #Hwst, #Cev, #Cpr, #Ccp, #Ccn⟩
  icases Hwa with ⟨%wa, #Hwa⟩
  wp_auto
  ihave #Hcf := typedPointsto_split _ _ _ $$ Hcfg
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hcf
  ihave #Hmx := typedPointsto_split _ _ _ $$ Mix
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hmx
  wp_auto
  wp_apply (wp_pickA T.ep.cfg.Mix'.Act' wa DFrac.discard (W64 6)) $$ [$Hwa] as %sw ⟨-, %Hsw⟩
  wp_if_destruct
  · -- watch
    wp_apply (wp_stream_watch T q C) $$ [Hreg] as Hreg
    · iframe Hreg; iexact Hctx0
    (try wp_auto)
    iapply HΦ; iexists C; iframe
  wp_if_destruct
  · -- cancel
    wp_apply (wp_stream_cancel T q C) $$ [Hreg] as ⟨%C', Hreg⟩
    · iframe Hreg; iexact Hctx0
    (try wp_auto)
    iapply HΦ; iexists C'; iframe
  iunfold regOwn at Hreg
  icases Hreg with ⟨Hrd, Hcl, Hcn⟩
  icases (epRd_split T.ep q).1 $$ Hrd with ⟨Hrdr, Hlive, Hkvf⟩
  ihave %Hsh := hsh.2.2.2 T.ws T.ep.ι.kv T.σs.ws $$ Hws
  obtain ⟨tyW, vW, hwsv, hWatch, -, hProg, hProgAll, -, -, hRev⟩ := Hsh
  ihave #Hws2 : isMvccWatchStream (interface.mkOk tyW vW) T.ep.ι.kv T.σs.ws $$ []
  · rw [← hwsv]; iexact Hws
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_if_destruct
  · -- a watcher's progress
    wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HL⟩
    iunfold smuInv at HL
    icases HL with ⟨%rs0, %W, %Hl, %P, HB⟩
    wp_apply (wp_stream_pick T rs0 W Hl P) $$ [HB] as %id %ok ⟨HB, -⟩
    · iframe HB; iexact Hctx0
    (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock (sF go!"mu" T.s) (smuInv T) $$ [$Hmu $Hlocked HB]
    · iunfold smuInv; iexists rs0, W, Hl, P; iexact HB
    (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      iapply HΦ
      iexists C
      iunfold regOwn
      iframe
      iapply (epRd_split T.ep q).2
      iframe
    · rw [hwsv]
      (try wp_auto)
      wp_apply (hProg T.ep.ι.kv T.σs.ws id) $$ [$Hws2 $Hrdr] as Hrdr
      (try wp_auto)
      iapply HΦ
      iexists C
      iunfold regOwn
      iframe
      iapply (epRd_split T.ep q).2
      iframe
  wp_if_destruct
  · -- the stream's progress
    rw [hwsv]
    (try wp_auto)
    wp_apply (hProgAll T.ep.ι.kv T.σs.ws) $$ [$Hws2 $Hrdr] as %b Hrdr
    (try wp_auto)
    iapply HΦ
    iexists C
    iunfold regOwn
    iframe
    iapply (epRd_split T.ep q).2
    iframe
  wp_if_destruct
  · -- the stream's revision
    iunfold epLive at Hlive
    wp_apply_core sync.atomic.Int64.wp_Load (mF go!"revLo" T.ep.mp) (DFrac.own 1) $$ [] [-]
    · iPkgInit
    imod revLo_acc T.ep.ks T.ep.γh T.ep.i T.ep.mp T.ep.m T.ep.ι T.ep.kv q $$ Hlive
      with ⟨%lo, Hlo, Hcl⟩
    imodintro
    inext
    iexists lo
    iframe Hlo
    iintro Hlo
    imod Hcl $$ Hlo with ⟨Hlive, %nn, #Hnn, %Hlon⟩
    imodintro
    wp_auto
    rw [hwsv]
    (try wp_auto)
    iunfold incLive at Hlive
    icases Hlive with ⟨-, Hret⟩
    imod (monoNatLbOwn_0 (GF := GF) T.ep.m.crev) with #Hc0
    ihave Hau := reader_au hpers hreach T.ep.ks T.ep.γh T.ep.i T.ep.mp T.ep.m T.ep.ι T.ep.kv q
      nn 0 $$ [$Hinc $Hnn $Hc0]
    ihave Hau := Hau $$ Hret
    wp_apply (hRev T.ep.ι.kv T.σs.ws
        (fun σ => iprop(ghostVar T.ep.ι.ret q () ∗ readQ T.ep.ks T.ep.γh T.ep.m σ ∗
          ⌜nn ≤ σ.rev ∧ 0 ≤ Int.toNat (σ.crev + 1)⌝))) $$ [$Hws2 $Hrdr $Hau]
      as %rv ⟨Hrdr, %σ, ⟨Hret, #HQ, %Hnc⟩, %Hrv⟩
    ihave #HQ' := HQ
    iunfold readQ at HQ'
    icases HQ' with ⟨%Hl, -, #Lrev, -, -, %Hq''⟩
    have hrvZ : sint.Z rv = σ.rev := by
      rw [Hrv]; have := Hq''.2.2; unfold MvccState.rev; word
    ihave Hlive : incLive (GF := GF) T.ep.ks T.ep.γh T.ep.i T.ep.mp T.ep.m T.ep.ι T.ep.kv q $$ [Hret]
    · iunfold incLive; iframe Hret; iexact Hinc
    (try wp_auto)
    wp_apply (wp_inBounds lo rv (mF go!"revHi" T.ep.mp) _ (by omega)) $$ [] [-]
    imod revHi_acc T.ep.ks T.ep.γh T.ep.i T.ep.mp T.ep.m T.ep.ι T.ep.kv q _ $$ [$Hlive $Lrev]
      with ⟨%vh, Hvh, %Hvhb, Hcl⟩
    imodintro
    inext
    iexists DFrac.own 1, vh
    iframe Hvh
    isplitr
    · ipureintro; omega
    iintro Hvh
    imod Hcl $$ Hvh with Hlive
    imodintro
    (try wp_auto)
    iapply HΦ
    iexists C
    iunfold regOwn
    iframe
    iapply (epRd_split T.ep q).2
    iframe
  · -- an empty watch
    wp_apply wp_runner_genKey T.ep.x T.ep.ks $$ [] as %sk ⟨%k, Hsk, %Hkin⟩
    · iframe #
    (try wp_auto)
    imod ownSlice_persist $$ Hsk with #Hsk
    wp_apply wp_ctxTODO
    (try wp_auto)
    ihave #Hflt : filtersImpl (GF := GF) slice.nil ([] : List (EvM → Bool)) $$ []
    · iunfold filtersImpl
      iexists []
      isplitl
      · iapply ownSlice_nil
      simp
      isplitl
      · itrivial
      · iempintro
    rw [hwsv]
    (try wp_auto)
    have hkne : k ≠ [] := Hkne k Hkin
    wp_apply (hWatch T.ep.ι.kv T.σs.ws todoCtxVal
        { Values := GMap.empty, Deadline := none, Done_gn := ⟨0, 0⟩, PDone := iprop(True) }
        sk sk slice.nil k k [] (W64 0) (fun _ _ _ => iprop(True)))
      $$ [Hrdr] as %id %err ⟨Hrdr, Hres⟩
    · iframe #
      iframe Hrdr
      isplitl []
      · ileft; ipureintro; rfl
      isplitl []
      · ipureintro; decide
      ileft; ipureintro; exact ⟨hkne, go.goStringLt_irrefl k⟩
    icases Hres with (⟨%Hc, #Herr⟩ | ⟨%Hc, -⟩)
    rotate_left
    · exfalso; rcases Hc with h | h
      · exact hkne h
      · exact go.goStringLt_irrefl k h
    obtain ⟨-, -, rfl⟩ := Hc
    ihave Hinit := errVars $$ Hmpkg
    icases Hinit with ⟨-, -, #HeEmp, -, -⟩
    iunfold errorsNewVar at HeEmp
    icases HeEmp with ⟨%xe, #HeEmp, -⟩
    ihave %Hag := typedPointsto_agree_wand _ _ _ _ _ $$ Herr HeEmp
    subst Hag
    (try wp_auto)
    wp_apply wp_check
    · ipureintro; simp
    (try wp_auto)
    iapply HΦ
    iexists C
    iunfold regOwn
    iframe
    iapply (epRd_split T.ep q).2
    iframe

end proof

end mvccfull
end EtcdGrove
end Perennial
