/-
`(*ConfigChangeContext).JSONModelUnmarshal(data, v)` (jsongen's same-package method, membership's
`json_model_gen.go`; the encoding/json model's `Unmarshal` dispatches a `*ConfigChangeContext` to it)
on bytes `membership.ccDecode` decodes to `r`, into a zero `ConfigChangeContext`: `nil`, and `*p`
holds `r` (its URL slices fresh, holding `r`'s URL lists).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.JsonDec
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.membership

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Assumptions]

open go_etcd_io.etcd.server.v3.etcdserver.api in
/-- See the file header. -/
abbrev membership.ConfigChangeContext.JSONModelUnmarshal.spec : Prop :=
  ∀ (jr : Loc) (data : GoSlice) (dq : DFrac) (bs : List w8) (p : Loc)
    (v : membership.ConfigChangeContext) (r : membership.CcM),
  membership.ccDecode bs = some r →
  v.Member'.ID' = W64 0 → v.Member'.RaftAttributes'.PeerURLs' = slice.nil →
  v.Member'.RaftAttributes'.IsLearner' = false → v.Member'.Attributes'.Name' = [] →
  v.Member'.Attributes'.ClientURLs' = slice.nil → v.IsPromote' = false →
  {{ (data ↦*{dq} bs ∗ p ↦ v : IProp GF) }}
    (App (App (Val (jr @!! go.GoType.PointerType membership.ConfigChangeContext.ty
        @!! go!"JSONModelUnmarshal")) (Val #data))
      (Val #(interface.mkOk (go.GoType.PointerType membership.ConfigChangeContext.ty) #p)))
  {{ RET #GoInterface.nil; data ↦*{dq} bs ∗
      ∃ v' : membership.ConfigChangeContext, p ↦ v' ∗
        v'.Member'.RaftAttributes'.PeerURLs' ↦* r.m.peerURLs ∗
        v'.Member'.Attributes'.ClientURLs' ↦* r.m.clientURLs ∗
        ⌜v'.Member'.ID' = r.m.id ∧ v'.Member'.RaftAttributes'.IsLearner' = r.m.isLearner ∧
          v'.Member'.Attributes'.Name' = r.m.name ∧ v'.IsPromote' = r.promote⌝ }}

end spec

end EtcdGrove
end Perennial
