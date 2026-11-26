/-
`client.MainReady(w, eps, nodes, ready)` **for an auth workload** (#50 F7 S12, kind `Auth`, 5): past its guards
(`len(eps) == 0`, `len(nodes) != NodeCount(w)`) and with no early `ready()` (`hasSetUp(Auth)`), `RunAuth(eps, nodes,
ready)`. F8's `MainReady.spec` reaches this arm with a `False` share (D2); this is the arm's triple, as
`NodeMainAuth.spec` is the principal machines'.

**The triple:** from the auth workload's orchestrator share `authShare epsL ns` (`client/AuthShares.lean`, the
candidate for `wlShare`'s kind-5 arm), its thread token and the machine-level pure facts (`orchMachinePure`),
`MainReady` does not panic. It binds the three `Assumptions` instances `RunAuth.spec` binds, as `MainReady.spec`
does since F7 S13 (W-6's contract item). Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.MainReady
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthShares

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.etcd.dist
open Net client etcd_dist_client
open github_com.mit_pdos.etcd_grove.examples.lib.remote

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : client.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev MainReadyAuth.spec : Prop :=
  ∀ [π : NetProtoGS] [ρ : RemoteGS] [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    (w : Workload) (eps nodes : GoSlice) (epsL ns : List GoString) (ready : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      ⌜w.kind = W64 5 ∧ orchMachinePure (GF := GF)⌝ ∗ threadTok ∗ eps ↦*□ epsL ∗ nodes ↦*□ ns ∗
      readySpec ready ∗ authShare (Gg := hG.goose_globalGS) epsL ns }}
    (App (App (App (App (Val (@! client.MainReady)) (Val #w.val)) (Val #eps)) (Val #nodes)) (Val #ready))
  {{ (r : client.Result), RET #r; True }}

end spec

end etcd_dist
end EtcdGrove
end Perennial

end
