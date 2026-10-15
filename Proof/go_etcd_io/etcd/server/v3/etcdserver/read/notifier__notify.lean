/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/read/notifier__notify.lean`. Lean-first (no Rocq
counterpart); the request path's unit 4a.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.read.notifier__notify

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.read

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.read.Assumptions]

theorem read.notifier.notify.wp_proof : read.notifier.notify.spec (GF := GF) (hG := hG) := by
  intro nc γn γr err
  wp_start as ⟨Hown, #Herr, Hfz⟩
  iunfold notifierOwn at Hown
  icases Hown with ⟨%ch, %γ, %e, #Hc, Hbc, He⟩
  wp_auto
  ipersist He
  ihave #HQ : notified nc γn γr $$ [Hfz]
  · iunfold notified
    iexists err
    iframe He Herr
    cases err with
    | ok ei => ileft; ipureintro; intro h; cases h
    | nil => iright; iapply Hfz; ipureintro; rfl
  wp_apply wp_broadcast_chan_close ch γ (notified nc γn γr) $$ [Hbc] as -
  · iframe Hbc HQ
  wp_end

end proof

end EtcdGrove
end Perennial
