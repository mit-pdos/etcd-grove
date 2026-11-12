/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/streamType__endpoint.lean`.
Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamType__endpoint
public import Spec.path.Join

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.streamType.endpoint.wp_proof (hJoin : path.Join.spec (GF := GF) (hG := hG)) :
    rafthttp.streamType.endpoint.spec (GF := GF) (hG := hG) := by
  intro ty lg
  wp_start as #Hpfx
  ihave #Hpath : isPkgInit (PROP := IProp GF) pkg_id.path $$ []
  · iPkgInit
  have hj1 : path.joinModel [go!"/raft/stream", go!"msgapp"] = StreamTy.msgAppV2.endpoint := by
    decide
  have hj2 : path.joinModel [go!"/raft/stream", go!"message"] = StreamTy.message.endpoint := by
    decide
  cases ty
  all_goals
    simp only [StreamTy.str]
    wp_auto
  all_goals
    wp_apply wp_slice_literal (V := GoString)
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    (try wp_auto)
    wp_apply hJoin _ _ _ (by decide) $$ [$Hsl] as %r ⟨%Hr, -⟩
    (try wp_auto)
    rw [Hr]
    simp only [show sint.nat (W64 (0 + 1)) = 1 by rfl, List.set_cons_succ, List.set_cons_zero]
    first | rw [hj1] | rw [hj2]
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
