/-
The heap side of membership's JSON decoders (#24 J2 batch 2b): `membership.ccOwn p r seen`, a
`*ConfigChangeContext` `p` holding the decoded value `r` (`JsonDec.lean`), field by field (the
generated `jdecMember_ConfigChangeContext` writes `p.Member.ID`, `p.IsPromote`, ... and passes
`&p.Member.RaftAttributes.PeerURLs` to `jdec_S_string`), its URL lists owned, and nil while their
key has not been decoded (`seen`).
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

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Assumptions]

include sem package_sem in
open go_etcd_io.etcd.server.v3.etcdserver.api in
/-- **A `*ConfigChangeContext` `p` holding `r`**, field by field (see the file header). -/
def membership.ccOwn (p : Loc) (r : membership.CcM) (seen : List GoString) : IProp GF :=
  iprop(∃ (sp sc : GoSlice),
    structFieldRef membership.Member go!"ID" (structFieldRef membership.ConfigChangeContext go!"Member" p) ↦ (r.m.id : go_etcd_io.etcd.client.pkg.v3.types.ID) ∗
    structFieldRef membership.RaftAttributes go!"PeerURLs"
      (structFieldRef membership.Member go!"RaftAttributes" (structFieldRef membership.ConfigChangeContext go!"Member" p)) ↦ sp ∗
    structFieldRef membership.RaftAttributes go!"IsLearner"
      (structFieldRef membership.Member go!"RaftAttributes" (structFieldRef membership.ConfigChangeContext go!"Member" p)) ↦ r.m.isLearner ∗
    structFieldRef membership.Attributes go!"Name"
      (structFieldRef membership.Member go!"Attributes" (structFieldRef membership.ConfigChangeContext go!"Member" p)) ↦ r.m.name ∗
    structFieldRef membership.Attributes go!"ClientURLs"
      (structFieldRef membership.Member go!"Attributes" (structFieldRef membership.ConfigChangeContext go!"Member" p)) ↦ sc ∗
    structFieldRef membership.ConfigChangeContext go!"IsPromote" p ↦ r.promote ∗
    sp ↦* r.m.peerURLs ∗ sc ↦* r.m.clientURLs ∗
    ⌜(go!"peerURLs" ∉ seen → sp = slice.nil) ∧ (go!"clientURLs" ∉ seen → sc = slice.nil)⌝)

end defs

end EtcdGrove
end Perennial
