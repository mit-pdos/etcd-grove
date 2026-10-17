/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/syncSnapDir.lean`. Lean-first (no Rocq
counterpart); etcd PR #22518 (branch `pr-verify/etcd-22518`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.syncSnapDir
public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.OpenDir
public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.Fsync
public import Spec.os.File__Close

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]

theorem storage.syncSnapDir.wp_proof
    (wp_OpenDir : fileutil.OpenDir.spec (GF := GF) (hG := hG))
    (wp_Fsync : fileutil.Fsync.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG)) :
    storage.syncSnapDir.spec (GF := GF) (hG := hG) := by
  intro dir dst
  wp_start as ⟨Hpend, %Hdir⟩
  wp_apply wp_with_defer as %defer defer
  wp_apply wp_OpenDir as %f %err Hres
  unfold fsResult
  icases Hres with (⟨%Herr, Hh⟩ | ⟨%e, %Herr, #He, -⟩)
  · subst Herr
    wp_auto
    wp_apply wp_Fsync $$ [$Hh $Hpend] as %err2 ⟨Hh, Hres2⟩
    · ipureintro; exact Hdir
    wp_apply wp_Close $$ [$Hh] as %err3 -
    iapply HΦ
    iunfold fsResult at Hres2
    iexact Hres2
  · subst Herr
    wp_auto
    iapply HΦ
    iright
    iexists e
    isplitr
    · ipureintro; rfl
    isplitr
    · iexact He
    iexact Hpend

end proof

end EtcdGrove
end Perennial
