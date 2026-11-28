-- The copy for the part `Dsverify/` of `WalTester/Proof/github_com/mit_pdos/etcd_grove/examples/lib/durable/Read.lean` (etc/copy-part.py; rerun it, do not edit).
/-
The proof of `Spec/.../examples/lib/durable/Read.lean`: the mutex taken (it guards nothing),
`tryRead` retried until it is done; before each attempt the handle's physical state's facts are read
off the invariant (`durInv_okHandle`, at a step), and when one is done the client's update is
committed at the next step with the state whose `cur` the result is (`durInv_readHandle`). The
deferred `Unlock` releases the mutex. Lean-first (no Rocq counterpart).
-/
module

public import Dsverify.Spec.github_com.mit_pdos.etcd_grove.examples.lib.durable.Read
public import Dsverify.Spec.github_com.mit_pdos.etcd_grove.examples.lib.durable.tryRead
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

theorem github_com.mit_pdos.etcd_grove.examples.lib.durable.Read.wp_proof
    (wp_tryRead : github_com.mit_pdos.etcd_grove.examples.lib.durable.tryRead.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.etcd_grove.examples.lib.durable.Read.spec (GF := GF) (hG := hG) := by
  intro γ f R qc hf
  iintro %Φ #Hpkg #Hos #Hsi #Hdi Hh Hperm Hau
  ihave #Hdeps := isPkgInit_unfold_deps pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.durable $$ Hpkg
  isimp only [isPkgInitDeps] at Hdeps
  ihave #Hmu := github_com.mit_pdos.etcd_grove.examples.lib.durable.mu_of_pkgInit $$ Hpkg
  icases Hdeps with ⟨-, #Hospkg, -, #Hsync, -⟩
  iunfold durHandle at Hh
  icases Hh with ⟨%p, Hh, %halt⟩
  wp_func_call; (try wp_call); (try wp_auto)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock (globalAddr github_com.mit_pdos.etcd_grove.examples.lib.durable.mu)
    iprop(True) $$ [$Hmu $Hsync] as ⟨Hlocked, -⟩
  (try wp_auto)
  wp_for
  iapply wp_notCrashed_acc _ _ rfl
  iintro Hnc
  imod durInv_okHandle γ f R p $$ Hdi Hnc Hh with ⟨Hnc, Hh, %hok⟩
  iframe Hnc
  imodintro
  wp_apply wp_tryRead γ f R qc p hf hok $$ [Hospkg Hos Hsi Hh Hperm] as %str %ok %done ⟨Hh, Hperm, %hdone⟩
  · iframe; iframe #
  cases done with
  | false =>
    (try wp_auto)
    wp_for_post
    iframe
  | true =>
    obtain ⟨v, hv, rfl, rfl⟩ := hdone rfl
    iapply wp_notCrashed_acc _ _ rfl
    iintro Hnc
    imod durInv_readHandle γ f R p v _ hv $$ Hdi Hnc Hh Hau with ⟨Hnc, Hh, %s, %hs, HQ⟩
    iframe Hnc
    imodintro
    (try wp_auto)
    wp_for_post
    wp_apply sync.Mutex.wp_Unlock (globalAddr github_com.mit_pdos.etcd_grove.examples.lib.durable.mu)
      iprop(True) $$ [$Hmu $Hsync $Hlocked]
    (try wp_auto)
    have hr : readRes s.cur = PairV (#(v.getD [])) (#v.isSome) := by rw [hs]; rfl
    rw [← hr]
    iapply HQ $$ [Hh] Hperm
    iunfold durHandle; iexists p; iframe Hh; ipureintro; exact halt

end proof

end EtcdGrove
end Perennial
