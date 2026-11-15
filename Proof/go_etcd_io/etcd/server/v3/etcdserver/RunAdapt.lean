/-
# The gRPC runs' bundle and adapters, for etcd's server (per-type stage B3)

Scope r5 §3.3-§3.4: a run of one of etcd's KV, lease or auth handlers, or of the watch loops, holds
one loan per level of its thread token: `raftPool`'s `lgMu` reader at level 1, the inner pool `I`
(`leadTimeMu` ∗ `E.RD`) at level 2, the run pool (a store reader token, a reader slot of the read
loop's lock and one of `bemu`) at level 3.

* `srvRunBundle s E γr`: the run's level 0 (which the lease handlers' level-0 pools take) and the
  three pools' resources, which the handlers are proved against
  (`grpcMethodOkMd` at this resource).
* `srvStreamBundle s E γr`: a stream run's bundle, `srvRunBundle`'s with the run's level 4, which a
  stream handler lends a weak context's `Err()` (k8s 7f-4, Freeze addendum T-f').
* `srvRunOk_of_pools`, `srvStreamRunOk_of_pools`: a handler proved at the bundle meets grpc's run
  contract, from the built part (`srvRevokeBuilt`: levels 1 and 2) and the run pool (`srvRunPool`,
  level 3), given `srvLevels` (levels 0-4 of a token exist).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvServe
public import Proof.google_golang_org.grpc.InvGrpcRun

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A gRPC run's bundle** (see the file header): its own level 0 (the lease handlers' lessor and
lease pools) and the loans of its levels 1, 2 and 3. -/
def srvRunBundle (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  iprop(levelTok 0 ∗ srvLgReader s ∗ (srvLeadTimeReader s ∗ E.RD) ∗
    (mvcc.api.mvccReaders E.γ 1 ∗ srvReadReader s γr ∗ srvBemuReader s))

/-- **A gRPC stream run's bundle** (see the file header): `srvRunBundle`'s parts and the run's
level 4 (`v3rpc.ctxErrLvl`). -/
def srvStreamBundle (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  iprop(levelTok 0 ∗ levelTok 4 ∗ srvLgReader s ∗ (srvLeadTimeReader s ∗ E.RD) ∗
    (mvcc.api.mvccReaders E.γ 1 ∗ srvReadReader s γr ∗ srvBemuReader s))

end defs

section slot
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A method meeting `Spec` with the slot `S` meets it with any slot `S'` that holds `S` and
gives it back** (through `S' ⊢ S ∗ F` and `S ∗ F ⊢ S'`; the closed lease example: the KV methods
at the slot that also holds the lease reads' thread token). -/
theorem grpcMethodOkMd_slot {Req Rep : ProtoMsg GF} (mh : val) (srv : GoInterface)
    (ics : List GoFunc) (S S' F : IProp GF) (Spec : GrpcSpecMd Req Rep)
    (h1 : S' ⊢ S ∗ F) (h2 : S ∗ F ⊢ S') :
    grpcMethodOkMd mh srv ics S Spec ⊢ grpcMethodOkMd mh srv ics S' Spec := by
  iintro #Hh
  unfold grpcMethodOkMd
  iintro %m %Φ %Ψe %ci %cd %dec %ui !> %Ψ ⟨HS', #Hctx, #Hrc, #Hdec, #Hch, HSpec⟩ HΨ
  ihave ⟨HS, HF⟩ := h1 $$ HS'
  iapply Hh $$ %m %Φ %Ψe %ci %cd %dec %ui [HS HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, Hres, Hed⟩
  iapply HΨ
  iframe Hres Hed
  iapply h2
  iframe

/-- A service method meeting the metadata-indexed `Spec` with `S` meets it with any `S'` that
holds `S` and gives it back (as `grpcMethodOkMd_slot`, for a service method). -/
theorem grpcHandlerOkMd_slot {Req Rep : ProtoMsg GF} (h : val) (S S' F : IProp GF)
    (Spec : GrpcSpecMd Req Rep) (h1 : S' ⊢ S ∗ F) (h2 : S ∗ F ⊢ S') :
    grpcHandlerOkMd h S Spec ⊢ grpcHandlerOkMd h S' Spec := by
  iintro #Hh
  unfold grpcHandlerOkMd
  iintro %m %Φ %Ψe %ci %cd %r !> %Ψ ⟨HS', #Hctx, #Hrc, #Hr, HSpec⟩ HΨ
  ihave ⟨HS, HF⟩ := h1 $$ HS'
  iapply Hh $$ %m %Φ %Ψe %ci %cd %r [HS HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, Hres⟩
  iapply HΨ
  iframe Hres
  iapply h2
  iframe

/-- `grpcHandlerOkMd_slot`'s, for an owning service method. -/
theorem grpcHandlerOwnOk_slot {Req Rep : ProtoMsg GF} (h : val) (S S' F : IProp GF)
    (Spec : GrpcSpec Req Rep) (h1 : S' ⊢ S ∗ F) (h2 : S ∗ F ⊢ S') :
    grpcHandlerOwnOk h S Spec ⊢ grpcHandlerOwnOk h S' Spec := by
  iintro #Hh
  unfold grpcHandlerOwnOk
  iintro %m %Φ %ci %cd %r !> %Ψ ⟨HS', #Hctx, #Hrc, #Hr, Hown, HSpec⟩ HΨ
  ihave ⟨HS, HF⟩ := h1 $$ HS'
  iapply Hh $$ %m %Φ %ci %cd %r [HS Hown HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, Hres⟩
  iapply HΨ
  iframe Hres
  iapply h2
  iframe

/-- `grpcHandlerOkMd_slot`'s, for a plain spec. -/
theorem grpcHandlerOk_slot {Req Rep : ProtoMsg GF} (h : val) (S S' F : IProp GF)
    (Spec : GrpcSpec Req Rep) (h1 : S' ⊢ S ∗ F) (h2 : S ∗ F ⊢ S') :
    grpcHandlerOk h S Spec ⊢ grpcHandlerOk h S' Spec := by
  iintro #Hh
  unfold grpcHandlerOk
  iintro %m %Φ %ci %cd %r !> %Ψ ⟨HS', #Hctx, #Hrc, #Hr, HSpec⟩ HΨ
  ihave ⟨HS, HF⟩ := h1 $$ HS'
  iapply Hh $$ %m %Φ %ci %cd %r [HS HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, Hres⟩
  iapply HΨ
  iframe Hres
  iapply h2
  iframe

/-- A big separating conjunction over a cons, from its head and its tail (in the index-free form,
so that it applies again to the tail: the method lists of the served theorems). -/
theorem bigSepL_cons_intro' {α : Type _} {P : α → IProp GF} {a : α} {l : List α} :
    P a ∗ ([∗list] x ∈ l, P x) ⊢ [∗list] x ∈ a :: l, P x :=
  (BigSepL.bigSepL_cons (Φ := fun _ x => P x)).2

end slot

section adapt
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **A unary handler proved at the bundle meets grpc's run contract** (r5 §3.4): from the built
part's pools (levels 1 and 2) and the run pool (level 3), with `srvLevels`. -/
theorem srvRunOk_of_pools {Req Rep : ProtoMsg GF} (s : Loc) (E : apply.AEnv GF) (γr : ReadNames)
    (mh : val) (srv : GoInterface) (ics : List GoFunc) (Spec : GrpcSpecMd Req Rep)
    (HL : srvLevels (GF := GF)) :
    □ grpcMethodOkMd mh srv ics (srvRunBundle s E γr) Spec ∗ srvRevokeBuilt s E ∗
      srvRunPool s E γr ⊢
    grpcRunOkMd mh srv ics Spec := by
  iintro ⟨#Hm, #Hb, #Hr⟩
  ihave ⟨%γ₁, %γ₂, #H1, #H2⟩ := srvRevokeBuilt_runPools s E $$ Hb
  iunfold srvRunPool at Hr
  icases Hr with ⟨%γ₃, #H3⟩
  iapply (grpcRunOkMd_of_pools mh srv ics Spec _ _ _ raftPoolN srvRevokeInnerN srvRunN γ₁ γ₂ γ₃
    (by have := HL; unfold srvLevels srvLevelK srvRevokeK at this; omega))
  unfold srvRunBundle
  iframe #

/-- **A stream handler proved at the bundle meets grpc's stream run contract** (r5 §3.4), as
`srvRunOk_of_pools`. -/
theorem srvStreamRunOk_of_pools {Req Rep : StreamMsg GF} (s : Loc) (E : apply.AEnv GF)
    (γr : ReadNames) (mh : val) (srv : GoInterface) (sics : List GoFunc)
    (Up : Nat → Req.M → IProp GF) (Spec : GrpcMd → StreamSpec Rep) (HL : srvLevels (GF := GF)) :
    □ grpcStreamMethodOk mh srv sics (srvStreamBundle s E γr) Up Spec ∗ srvRevokeBuilt s E ∗
      srvRunPool s E γr ⊢
    grpcStreamRunOk mh srv sics Up Spec := by
  iintro ⟨#Hm, #Hb, #Hr⟩
  ihave ⟨%γ₁, %γ₂, #H1, #H2⟩ := srvRevokeBuilt_runPools s E $$ Hb
  iunfold srvRunPool at Hr
  icases Hr with ⟨%γ₃, #H3⟩
  iapply (grpcStreamRunOk_of_pools mh srv sics Up Spec _ _ _ raftPoolN srvRevokeInnerN srvRunN
    γ₁ γ₂ γ₃ (by have := HL; unfold srvLevels srvLevelK srvRevokeK at this; omega))
  unfold srvStreamBundle
  iframe #

end adapt

end EtcdGrove
end Perennial
