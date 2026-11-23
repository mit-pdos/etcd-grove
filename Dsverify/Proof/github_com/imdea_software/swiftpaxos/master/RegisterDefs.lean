/-
The definitions, specs and lemmas of `Register.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Perennial.Proof.fmt
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.Defs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.Addr
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.dlog.Logger__Printf

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv
  Perennial.fmt

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section spec
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [master.Assumptions]

/-- `m.Register(args, reply)` from replica node `k` of the configuration (`masterSpec`'s
`Register`): no error; `Ready` only with the membership (with the configuration's `N`) and the
caller's id, the index of its address; otherwise only `Ready` is written (false). -/
abbrev master.Master.Register.spec : Prop :=
  ∀ (m : Loc) (γc γm : GName) (N : Nat) (args reply : Loc) (ip : GoString) (port : w64)
    (c : Conf) (k : Nat) (rv : replica.defs.RegisterReply),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.master ∗
      master.isMaster m γc γm N ∗ args ↦ replica.defs.RegisterArgs.mk ip port ∗ reply ↦ rv ∗
      confIs γc c ∗ ⌜replicaAddrs[k]? = some (sp.addrPort ip port) ∧ k < c.n⌝ }}
    (App (App (Val (m @!! go.GoType.PointerType master.Master.ty @!! go!"Register"))
      (Val #args)) (Val #reply))
  {{ RET #(interface.nil : GoInterface);
      ∃ rv' : replica.defs.RegisterReply, reply ↦ rv' ∗
        (if rv'.Ready' then ∃ nodes : List GoString, rv'.NodeList' ↦*□ nodes ∗
            (∃ fr, sp.cfg γc γm nodes.length fr nodes) ∗
            ⌜nodes[rv'.ReplicaId'.toNat]? = some (sp.addrPort ip port)⌝
          else ⌜rv' = { rv with Ready' := false }⌝) }}

end spec

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [master.Assumptions] [dlog.Assumptions]

end proof

end Perennial.github_com.imdea_software.swiftpaxos
