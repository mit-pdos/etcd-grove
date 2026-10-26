/-
`metadata.FromIncomingContext`'s triple without the context's metadata (`weakSpec`, the shape
before the auth plan's E2c): what its callers that only read the map's values need.
-/
module

public import Spec.google_golang_org.grpc.metadata.FromIncomingContext

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode google_golang_org.grpc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `metadata.FromIncomingContext(ctx)`: `(md, ok)`; if `ok`, `md` is a fresh map, each of its
values a fresh slice of at least one string. -/
abbrev metadata.FromIncomingContext.weakSpec : Prop :=
  ∀ (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.metadata }}
    (App (Val (@! google_golang_org.grpc.metadata.FromIncomingContext)) (Val #ctx))
  {{ (md : GoMap) (ok : Bool), RET (PairV #md #ok);
      ⌜ok = false⌝ ∨ ∃ m : GMap GoString GoSlice, md ↦$ m ∗
        [∗map] _k ↦ sl ∈ m, ∃ vs : List GoString, sl ↦* vs ∗ ⌜vs ≠ []⌝ }}

theorem metadata.FromIncomingContext.weaken
    (h : metadata.FromIncomingContext.spec (GF := GF) (hG := hG)) :
    metadata.FromIncomingContext.weakSpec (GF := GF) (hG := hG) := by
  intro ctx
  iintro %Φ Hpre HΦ
  iapply h ctx $$ Hpre
  inext
  iintro %md %ok Hpost
  iapply HΦ
  icases Hpost with (⟨%Hok, -⟩ | ⟨%md0, %m, -, Hm, Hsls⟩)
  · ileft; ipureintro; exact Hok
  · iright
    iexists m
    iframe Hm
    iapply BigSepM.bigSepM_impl $$ Hsls
    imodintro
    iintro %k %v %Hkv ⟨%vs, Hvs, %Hne, -⟩
    iexists vs
    iframe Hvs
    ipureintro; exact Hne

end proof

end EtcdGrove
end Perennial
