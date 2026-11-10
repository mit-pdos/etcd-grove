/- Lean-first (no Rocq counterpart). The proof of `stream.watch`: Draft, to come (`sorry`).

The callees in call order: `genKey`, `genEnd` `choose`, `pick` (the
start's weights), `context.TODO`, `Watch` (through `shapes.law`), `check`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.stream__watch
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__genKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__genEnd
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.choose
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.pick
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.check
public import Spec.context.TODO
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.WatchLemmas
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

theorem stream.watch.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (errVars : mvcc.api.errVars.law (GF := GF))
    (wp_runner_genKey : runner.genKey.spec (GF := GF) (hG := hG))
    (wp_runner_genEnd : runner.genEnd.spec (GF := GF) (hG := hG))
    (wp_choose : choose.spec (GF := GF) (hG := hG))
    (wp_pick : EtcdGrove.mvccfull.pick.spec (GF := GF) (hG := hG))
    (wp_ctxTODO : context.TODO.spec (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG)) :
    stream.watch.spec (GF := GF) (hG := hG) := by
  intro T q C
  haveI : ∀ ws γ ι, Persistent (isMvccWatchStream (GF := GF) ws γ ι) := hpers.2.1
  haveI : ∀ ι n, Persistent (wsSentLb (GF := GF) ι n) := hpers.2.2.1
  haveI := streamCtx_persistent hpers T
  haveI : ∀ kv γ, Persistent (isMvcc (GF := GF) kv γ) := hpers.1
  haveI : ∀ N l, Persistent (ctrInv (GF := GF) N l) := by intro N l; unfold ctrInv; infer_instance
  wp_start as ⟨#Hctx0, Hro⟩
  ihave Hctx := Hctx0
  iunfold streamCtx at Hctx
  icases Hctx with ⟨Hep, #Fx, #Fm, #Fkv, #Fws, #Fwm, #Hws, #Hinv, #Hmu, #Hstop⟩
  iunfold epCtx at Hep
  icases Hep with ⟨Hrn, #Hinc, #Hregs⟩
  iunfold rnCtx at Hrn
  icases Hrn with ⟨#Hpkg, #Hmpkg, #Hkeys, %Hkne, #HrH, #Hhist, #Hcfg, #Hwa, #Hwst, #Cev, #Cpr, #Ccp, #Ccn⟩
  iunfold regOwn at Hro
  icases Hro with ⟨Hrd, Hcl, Hcn⟩
  icases (epRd_split T.ep q).1 $$ Hrd with ⟨Hrdr, Hlive, Hkvf⟩
  iunfold epLive at Hlive
  wp_auto
  wp_apply_core sync.atomic.Int64.wp_Add (mF go!"regs" T.ep.mp) (W64 1) $$ [] [-]
  · iPkgInit
  iunfold ctrInv at Hregs
  iinv Hregs with ⟨%a, >Ha⟩ Hclose
  all_goals (try exact (fun _ _ => CoPset.mem_full))
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑(sCtrN .@ "regs") from
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
  ihave #Hcf := typedPointsto_split _ _ _ $$ Hcfg
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hcf
  ihave #Hmx := typedPointsto_split _ _ _ $$ Mix
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hmx
  wp_auto
  wp_if_destruct
  · iapply HΦ
    iunfold regOwn
    iframe
    iapply (epRd_split T.ep q).2
    iframe
  wp_apply (wp_runner_genKey T.ep.x T.ep.ks) $$ [$Hkeys] as %ksl ⟨%kk, Hksl, %Hkk⟩
  imod ownSlice_persist _ _ _ $$ Hksl with #Hksl
  (try wp_auto)
  wp_apply (wp_runner_genEnd T.ep.x T.ep.ks) $$ [$Hkeys] as %esl ⟨%e0, Hesl, %He0⟩
  imod ownSlice_persist _ _ _ $$ Hesl with #Hesl
  (try wp_auto)
  wp_apply wp_choose as %flt %Hflt
  (try wp_auto)
  generalize «$r0_ptr» = wpl at *
  -- the end, `nil` when it would make the range empty
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ w_ptr ↦ wpl ∗
      ∃ (endk : GoSlice) (e : GoString), wpl ↦ (watcher.mk ksl endk flt 0 0 0 0 false false false) ∗ endk ↦*□ e ∗ ⌜e = [] ∨ go.GoStringLt kk e⌝))) $$ [w «$r0»]
  · wp_if_destruct
    · (try wp_auto)
      wp_apply wp_bytes_to_string esl e0 DFrac.discard $$ [$Hesl] as -
      (try wp_auto)
      wp_apply wp_bytes_to_string ksl kk DFrac.discard $$ [$Hksl] as -
      (try wp_auto)
      wp_if_destruct
      · ihave #Hnil : (slice.nil ↦*□ ([] : List w8) : IProp GF) $$ []
        · iapply ownSlice_nil
        iframe
        iexists []
        iframe
        iframe #
        ipureintro; left; rfl
      · iframe
        iexists e0
        iframe
        iframe #
        ipureintro; right
        by_cases hlt : go.GoStringLt kk e0
        · exact hlt
        · exfalso; apply Hif
          by_cases h2 : go.GoStringLt e0 kk
          · exact Or.inr h2
          · exact Or.inl (go.goStringLt_eq_of_not_lt h2 hlt)
    · ihave %Hel := ownSlice_len $$ Hesl
      have he0 : e0 = [] := by
        apply List.eq_nil_of_length_eq_zero
        have := Hel.1; have h0 : sint.Z (W64 0) = 0 := rfl; word
      iframe
      iexists e0
      iframe
      iframe #
      ipureintro; left; exact he0
  iintro %v ⟨%hv, w, %endk, %e, «$r0», #Hend, %Hend⟩
  subst hv
  wp_auto
  trace_state
  sorry

end proof

end mvccfull
end EtcdGrove
end Perennial
