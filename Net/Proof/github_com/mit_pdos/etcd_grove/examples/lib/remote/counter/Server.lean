/-
The proof of `Server.spec`: `New` gives the counter and its state's half at `0`, which with the
start's half of `γs` (also at `0`) goes into the invariant `syncInv`; the operation meets `opMaybe`
over `srvTok`: its update for `Counter.Apply` (`CounterApply.spec`) opens `syncInv` (the mask
`syncN`, the store's `Eop`), fires the store's update `lin` (its `sysState` is the start's half of
`γs`, which agrees with the invariant's), gives the counter's state to `Apply`, and at its commit
moves both variables to the step and closes; `Apply`'s answer is the step's output, returned as
`Out{N: n}`. Then `Codec()`, `attempt()` and `remote.Serve`.
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Server
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.CounterApply
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Codec
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.attempt
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.Serve
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.lintest.counter.New

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote.counter

open github_com.mit_pdos.etcd_grove.examples.lib.remote EtcdGrove.lintest.counter

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Assumptions]
variable [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]

theorem cB_step_eq (b : Bool) (n : w64) :
    cB.step b n = (counterNext n (boxB b), counterNext n (boxB b)) := by
  rw [counterNext_boxB]; cases b <;> rfl

theorem Server.wp_proof
    (wp_New : EtcdGrove.lintest.counter.New.spec (GF := GF) (hG := hG))
    (wp_Apply : CounterApply.spec (GF := GF) (hG := hG))
    (wp_Codec : Codec.spec (GF := GF) (hG := hG))
    (wp_attempt : attempt.spec (GF := GF) (hG := hG))
    (wp_Serve : remote.Serve.spec (GF := GF) (hG := hG) (I := Bool) (O := w64)) :
    Server.spec (GF := GF) (hG := hG) := by
  intro γs a
  wp_start as ⟨#Hra, Hs⟩
  wp_auto
  ihave #Hlc : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.lintest.counter $$ []
  · iPkgInit
  wp_apply wp_New $$ [Hlc] as %c ⟨%γc, #Hc, Hcs⟩
  imod inv_alloc syncN ⊤ iprop(∃ n : w64, ghostVar γs (1 : Qp).half n ∗ counterState γc n)
    $$ [Hs Hcs] with #Hsync
  · inext
    iexists W64 0
    iframe Hs Hcs
  wp_apply (wp_Codec γs) as %cd #Hcd
  wp_apply wp_attempt as %d -
  wp_apply wp_Serve (RBase.svc (Gg := hG.goose_globalGS) (cR γs)) a _ _ cd d (srvTok γs) $$ []
    as ⟨⟩
  iframe #
  isplit
  · iapply codecOk_wireOk $$ Hcd
  isplit
  · -- the operation
    iapply opMaybe_svcOp
    unfold opMaybe
    iintro %sys %i %Φ
    iintro !> %Φr ⟨Htok, HL, -⟩ HΦr
    ihave HL : lin (Gg := hG.goose_globalGS) (cR γs) i Φ $$ [HL]
    · cases hw : (cR (GF := GF) γs).B.isWrite ((cR (GF := GF) γs).mi i)
      · rw [slotUpd_read _ hw]
        icases HL with #HL
        iexact HL
      · rw [slotUpd_write _ hw]
        iexact HL
    unfold srvTok
    icases Htok with ⟨%c', %γc', %Hsys, #Hc', #Hsync', #Hlc'⟩
    subst Hsys
    wp_auto
    wp_apply wp_Apply γc' c' i (fun n => Φ n) $$ [HL] as %v ⟨%n, %Hv, HR⟩
    · iframe Hc'
      unfold syncInv
      iinv Hsync' with >Hi Hclose
      icases Hi with ⟨%n, Hg, Hcs⟩
      unfold lin
      have hE : (cR (GF := GF) γs).Eop = ↑syncN := rfl
      rw [hE]
      imod HL with ⟨%st, Hst, Hk⟩
      have hs0 : (cR (GF := GF) γs).sysState st ⊢ ghostVar γs (1 : Qp).half st := by
        simp only [cR]; exact .rfl
      ihave Hst := hs0 $$ Hst
      ihave %Heq := ghostVar_agree γs n (1 : Qp).half st (1 : Qp).half $$ Hg Hst
      subst Heq
      imodintro
      iexists n
      iframe Hcs
      iintro Hcs
      imod ghostVar_update_halves (counterNext n (boxB i)) γs _ _ $$ Hg Hst with ⟨Hg, Hst⟩
      have hst : (cR (GF := GF) γs).B.step ((cR (GF := GF) γs).mi i) n = (counterNext n (boxB i), counterNext n (boxB i)) :=
        cB_step_eq i n
      rw [hst]
      have hs1 : ghostVar γs (1 : Qp).half (counterNext n (boxB i)) ⊢
          (cR (GF := GF) γs).sysState (counterNext n (boxB i)) := by
        simp only [cR]; exact .rfl
      ihave Hst := hs1 $$ Hst
      imod Hk $$ Hst with HR
      imod Hclose $$ [Hg Hcs] with -
      · inext
        iexists _
        iframe Hg Hcs
      imodintro
      iexact HR
    subst Hv
    wp_auto
    iapply HΦr
    isplitr [HR]
    · iexists c', γc'
      iframe #
      ipureintro; rfl
    · ileft
      iexists n
      iframe HR
      ipureintro; rfl
  · -- the system
    unfold srvTok syncInv
    iexists c, γc
    iframe #
    ipureintro; rfl

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.remote.counter
end Perennial
