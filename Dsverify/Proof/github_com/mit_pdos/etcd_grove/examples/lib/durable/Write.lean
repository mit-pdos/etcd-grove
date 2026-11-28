-- The copy for the part `Dsverify/` of `WalTester/Proof/github_com/mit_pdos/etcd_grove/examples/lib/durable/Write.lean` (etc/copy-part.py; rerun it, do not edit).
/-
The proof of `Spec/.../examples/lib/durable/Write.lean`: the mutex taken (it guards nothing),
`tryWrite` retried until it returns `true`; before each attempt the handle's physical state's facts
are read off the invariant (`durInv_okHandle`, at a step). What the call still owes its client
(`durWOwe`) goes from attempt to attempt: both updates until a rename commits the first, then the
second, which the attempt that returns `true` commits. The deferred `Unlock` releases the mutex.
Lean-first (no Rocq counterpart).
-/
module

public import Dsverify.Spec.github_com.mit_pdos.etcd_grove.examples.lib.durable.Write
public import Dsverify.Spec.github_com.mit_pdos.etcd_grove.examples.lib.durable.tryWrite
public import Dsverify.Proof.github_com.mit_pdos.etcd_grove.examples.lib.durable.Inv
public import Perennial.GooseLang.NotCrashed

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs DurFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.durable.Assumptions]

theorem github_com.mit_pdos.etcd_grove.examples.lib.durable.Write.wp_proof
    (wp_tryWrite : github_com.mit_pdos.etcd_grove.examples.lib.durable.tryWrite.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.etcd_grove.examples.lib.durable.Write.spec (GF := GF) (hG := hG) := by
  intro γ f R qc data hf hdata
  iintro %Φ #Hpkg #Hos #Hsi #Hdi Hh Hperm Hau
  ihave #Hdeps := isPkgInit_unfold_deps pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.durable $$ Hpkg
  isimp only [isPkgInitDeps] at Hdeps
  ihave #Hmu := github_com.mit_pdos.etcd_grove.examples.lib.durable.mu_of_pkgInit $$ Hpkg
  icases Hdeps with ⟨-, #Hospkg, #Hfp, #Hsync, -⟩
  iunfold durHandle at Hh
  icases Hh with ⟨%p, Hh, %halt⟩
  ihave Howe : durWOwe γ f data p iprop(durHandle γ f R -∗ osCallPerm (callKey R f.d) qc -∗ Φ #()) $$ [Hau]
  · iunfold durWOwe; ileft; iframe Hau; ipureintro; exact halt
  wp_func_call; (try wp_call); (try wp_auto)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock (globalAddr github_com.mit_pdos.etcd_grove.examples.lib.durable.mu)
    iprop(True) $$ [$Hmu $Hsync] as ⟨Hlocked, -⟩
  (try wp_auto)
  ihave Hst : ∃ p : DurPhys, durHandleP γ f R p ∗
      durWOwe γ f data p iprop(durHandle γ f R -∗ osCallPerm (callKey R f.d) qc -∗ Φ #()) $$ [Hh Howe]
  · iexists p; iframe
  wp_for
  icases Hst with ⟨%p', Hh, Howe⟩
  iapply wp_notCrashed_acc _ _ rfl
  iintro Hnc
  imod durInv_okHandle γ f R p' $$ Hdi Hnc Hh with ⟨Hnc, Hh, %hok⟩
  iframe Hnc
  imodintro
  wp_apply wp_tryWrite γ f R qc p' data _ hf hdata hok $$ [Hospkg Hfp Hos Hsi Hdi Hh Hperm Howe]
    as %ok ⟨Hperm, %p'', Hh, Hres⟩
  · iframe; iframe #
  icases Hres with (⟨%hok', HΨ⟩ | ⟨%hok', Howe⟩)
  · obtain ⟨rfl, halt'⟩ := hok'
    simp only [Bool.not_true]; cleanup_bool_decide
    (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock (globalAddr github_com.mit_pdos.etcd_grove.examples.lib.durable.mu)
      iprop(True) $$ [$Hmu $Hsync $Hlocked]
    (try wp_auto)
    iapply HΨ $$ [Hh] Hperm
    iunfold durHandle; iexists p''; iframe Hh; ipureintro; exact halt'
  · subst hok'
    simp only [Bool.not_false]; cleanup_bool_decide
    (try wp_auto)
    wp_for_post
    iframe
    iexists p''; iframe

end proof

end EtcdGrove
end Perennial
