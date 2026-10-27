/-
A compaction request's points-to, `compactReqIs`: what the auto-compactor builds
(`&pb.CompactionRequest{Revision: r}`) and the server's `Compact` takes. Here, with the request type,
so that neither the compactor nor the server depends on the other's definitions (the spec-first
pilot's freeze, 2026-10-27; it was the compactor's, `v3compactor.compactReqIs`).
-/
module

public import GeneratedProof.go_etcd_io.etcd.api.v3.etcdserverpb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A non-physical compaction request at revision `r`. -/
def compactReqIs (p : Loc) (r : Int) : IProp GF :=
  iprop(∃ v : etcdserverpb.CompactionRequest, p ↦ v ∗ ⌜sint.Z v.Revision' = r ∧ v.Physical' = false⌝)

/-- The request a client builds: a points-to of a request with that revision, not physical. -/
theorem compactReqIs_of (p : Loc) (v : etcdserverpb.CompactionRequest) (r : Int)
    (h : sint.Z v.Revision' = r ∧ v.Physical' = false) :
    p ↦ v ⊢ compactReqIs (GF := GF) p r := by
  unfold compactReqIs
  iintro H
  iexists v
  iframe H
  ipureintro; exact h

end defs

end EtcdGrove
end Perennial
