/- Lean-first (no Rocq counterpart). The proof of `stream.cancel` (proved: `RegLemmas.mark_upd`, `cancel_au`).

The callees in call order: `stream.pick`, `Cancel` (through `shapes.law`; its error compared with
`ErrWatcherNotExist`, whose identity `errVars.law` gives since the Freeze of 2026-11-10), `check`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.stream__cancel
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.stream__pick
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.check
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.RegLemmas
public import Perennial.Spec.sync.atomic.Int64__Add

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
theorem stream.cancel.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (errVars : mvcc.api.errVars.law (GF := GF))
    (wp_stream_pick : stream.pick.spec (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG)) :
    stream.cancel.spec (GF := GF) (hG := hG) := by
  intro T q C
  haveI : ∀ ws γ ι, Persistent (isMvccWatchStream (GF := GF) ws γ ι) := hpers.2.1
  haveI := streamCtx_persistent hpers T
  haveI : ∀ N l, Persistent (ctrInv (GF := GF) N l) := by intro N l; unfold ctrInv; infer_instance
  wp_start as ⟨#Hctx0, Hreg⟩
  ihave Hctx := Hctx0
  iunfold streamCtx at Hctx
  icases Hctx with ⟨Hep, #Fx, #Fm, #Fkv, #Fws, #Fwm, #Hws, #Hinv, #Hmu, #Hstop⟩
  iunfold epCtx at Hep
  icases Hep with ⟨Hrn, #Hinc, #Hregs⟩
  iunfold rnCtx at Hrn
  icases Hrn with ⟨#Hpkg, #Hmpkg, #Hkeys, %Hkne, #HrH, #Hhist, #Hcfg, #Hwa, #Hwst, #Cev, #Cpr, #Ccp, #Ccn⟩
  iunfold regOwn at Hreg
  icases Hreg with ⟨Hrd, Hcl, Hcn⟩
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HL⟩
  iunfold smuInv at HL
  icases HL with ⟨%rs0, %W, %Hl, %P, HB⟩
  wp_apply (wp_stream_pick T rs0 W Hl P) $$ [HB] as %id %ok ⟨HB, %Hok⟩
  · iframe HB; iexact Hctx0
  cases ok
  · (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock (sF go!"mu" T.s) (smuInv T) $$ [$Hmu $Hlocked HB]
    · iunfold smuInv; iexists rs0, W, Hl, P; iexact HB
    (try wp_auto)
    iapply HΦ
    iexists C
    iunfold regOwn
    iframe
  obtain ⟨x, hx, hcm⟩ := Hok rfl
  iunfold smuBody at HB
  icases HB with ⟨Hwm, ⟨%osl, %ids, Hord, Hids, Hcap, %Hids⟩, Hevl, Hrl, Hrcv0, #Hlb, %Hknown, Hwats⟩
  (try wp_auto)
  wp_apply (wp_map_lookup1 go_etcd_io.etcd.server.v3.storage.mvcc.WatchID.ty
    watcher.ty.PointerType T.wm (GMap.fmap Reg.wp W) id (DFrac.own 1)) $$ [$Hwm] as Hwm
  rw [hx]
  simp only [Option.map_some, Option.getD_some]
  icases (BigSepM.bigSepM_delete (PROP := IProp GF)
    (Φ := fun (id : w64) (x : Reg) => watcherOwn' (GF := GF) Hl rs0 T.σs.ws id x) (m := W) hx).1
    $$ Hwats with ⟨Hw, Hwats⟩
  iunfold watcherOwn' at Hw
  icases Hw with ⟨%wv, Hp, #Hk, #He, Hlbk, %Hwok⟩
  (try wp_auto)
  imod mark_upd hpers T.σs W C id x hx hcm $$ [$Hinv $Hrl $Hcl $Hcn] with ⟨Hrl, Hcl, Hcn, #Hf, %HnC⟩
  wp_apply sync.Mutex.wp_Unlock (sF go!"mu" T.s) (smuInv T)
    $$ [$Hmu $Hlocked Hwm Hord Hids Hcap Hevl Hrl Hrcv0 Hwats Hp Hlbk]
  · iunfold smuInv
    iexists rs0, <[id := { x with cm := true }]> W, Hl, P
    iunfold smuBody
    rw [fmap_insert_wp W id x { x with cm := true } hx rfl]
    iframe Hwm Hevl Hrl Hrcv0
    iframe #
    isplitl [Hord Hids Hcap]
    · iexists osl, ids
      iframe
      ipureintro
      exact ⟨Hids.1, fun k => by rw [isSome_insert_iff W id x { x with cm := true } hx]; exact Hids.2 k⟩
    isplitr
    · ipureintro
      refine ⟨fun r hr hne => by rw [isSome_insert_iff W id x { x with cm := true } hx]; exact Hknown.1 r hr hne,
        Hknown.2⟩
    iapply (BigSepM.bigSepM_insert_delete (PROP := IProp GF)
      (Φ := fun (id : w64) (x : Reg) => watcherOwn' (GF := GF) Hl rs0 T.σs.ws id x)
      (m := W) (i := id) (x := { x with cm := true })).2
    iframe Hwats
    iunfold watcherOwn'
    iexists { wv with cancelled' := true }
    iframe
    iframe #
    ipureintro
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -, h12, h13, h14⟩ := Hwok
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, rfl, h12, h13, h14⟩
  (try wp_auto)
  ihave %Hsh := hsh.2.2.2 T.ws T.ep.ι.kv T.σs.ws $$ Hws
  obtain ⟨tyW, vW, hwsv, -, -, -, -, hCancel, -, -⟩ := Hsh
  ihave #Hws2 : isMvccWatchStream (interface.mkOk tyW vW) T.ep.ι.kv T.σs.ws $$ []
  · rw [← hwsv]; iexact Hws
  rw [hwsv]
  (try wp_auto)
  wp_apply (hCancel T.ep.ι.kv T.σs.ws id
      (fun S => iprop(ghostVar (GF := GF) T.σs.cl (1 : Qp).half false ∗
        ghostVar T.σs.cn (1 : Qp).half (C ++ [id]) ∗
        ⌜S.closed = false ∧ (id ∉ C → ∃ w, S.ws !! id = some w ∧ w.live = true)⌝)))
    $$ [Hcl Hcn] as %err ⟨%S1, ⟨Hcl, Hcn, %HS1⟩, Hres⟩
  · iframe #
    iapply cancel_au hpers T.σs C id { x with cm := true } rfl $$ [Hcl Hcn]
    iframe #; iframe
  icases Hres with (%Hn | ⟨%Hc, -⟩)
  rotate_left
  · exfalso
    obtain ⟨w, hw, hl⟩ := HS1.2 HnC
    have := Hc w hw hl; rw [HS1.1] at this; cases this
  obtain ⟨rfl, -, -⟩ := Hn
  (try wp_auto)
  wp_apply wp_check
  · ipureintro; simp
  (try wp_auto)
  wp_apply (hCancel T.ep.ι.kv T.σs.ws id
      (fun S => iprop(ghostVar (GF := GF) T.σs.cl (1 : Qp).half false ∗
        ghostVar T.σs.cn (1 : Qp).half (C ++ [id] ++ [id]) ∗
        ⌜S.closed = false ∧ (id ∉ C ++ [id] → ∃ w, S.ws !! id = some w ∧ w.live = true)⌝)))
    $$ [Hcl Hcn] as %err2 ⟨%S2, ⟨Hcl, Hcn, -⟩, Hres2⟩
  · iframe #
    iapply cancel_au hpers T.σs (C ++ [id]) id { x with cm := true } rfl $$ [Hcl Hcn]
    iframe #; iframe
  ihave #Hpk : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iexact Hmpkg
  icases Hres2 with (%Hn2 | ⟨-, #Herr2⟩)
  · obtain ⟨rfl, -, -⟩ := Hn2
    (try wp_auto)
    wp_apply wp_check
    · ipureintro; simp
    (try wp_auto)
    wp_apply_core sync.atomic.Int64.wp_Add (rF go!"cancels" T.ep.x) (W64 1) $$ [] [-]
    · iPkgInit
    iunfold ctrInv at Ccn
    iinv Ccn with ⟨%a, >Ha⟩ Hclose
    all_goals (try exact (fun _ _ => CoPset.mem_full))
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑(sCtrN .@ "cancels") from
      Std.LawfulSet.empty_subset)
    iintro Hcl2
    inext
    iexists a
    iframe
    iintro Ha
    imod Hcl2 with -
    imod Hclose $$ [Ha] with -
    · inext; iexists _; iframe
    imodintro
    (try wp_auto)
    iapply HΦ
    iexists C ++ [id] ++ [id]
    iunfold regOwn
    iframe
  · ihave Hinit := errVars $$ Hmpkg
    icases Hinit with ⟨-, -, -, #HeNE, -⟩
    iunfold errorsNewVar at HeNE
    icases HeNE with ⟨%xn, #HeNE, -⟩
    ihave %Hag2 := typedPointsto_agree_wand _ _ _ _ _ $$ Herr2 HeNE
    subst Hag2
    (try wp_auto)
    wp_apply wp_check
    · ipureintro; simp
    (try wp_auto)
    wp_apply_core sync.atomic.Int64.wp_Add (rF go!"cancels" T.ep.x) (W64 1) $$ [] [-]
    · iPkgInit
    iunfold ctrInv at Ccn
    iinv Ccn with ⟨%a, >Ha⟩ Hclose
    all_goals (try exact (fun _ _ => CoPset.mem_full))
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑(sCtrN .@ "cancels") from
      Std.LawfulSet.empty_subset)
    iintro Hcl2
    inext
    iexists a
    iframe
    iintro Ha
    imod Hcl2 with -
    imod Hclose $$ [Ha] with -
    · inext; iexists _; iframe
    imodintro
    (try wp_auto)
    iapply HΦ
    iexists C ++ [id] ++ [id]
    iunfold regOwn
    iframe

end proof

end mvccfull
end EtcdGrove
end Perennial
