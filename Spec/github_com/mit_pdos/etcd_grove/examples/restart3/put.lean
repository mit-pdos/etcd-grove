/-
`put(cli, k, v)` (`examples/restart3/restart3.go`; the restart plan's R2, 2026-11-02): `cli.Put` of
`k ↦ v` in a context with the request timeout, cancelled after the call. Lean-first (no Rocq
counterpart).

**`spec`, a put of the client invariant's key:** for `New`'s client `cl` of the endpoint `ep`, whose
registrations are a member's (`kvRegsAt`), under the client's invariant for `key ↦ val`
(`client.putGetInv`): an error, or `nil` and the put's flag (`monoNatLbOwn γf 1`: the put fired, so
`key`'s value is `val` from then on).

**`specOther`, a put of another key** (`key' ≠ key`): an error or `nil`; the invariant's key keeps
its value (`client.client_Put_other`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.restart3.Defs
public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace restart3

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.restart3.Assumptions]

/-- See the file header. -/
abbrev put.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)] [ContextErrsClient (GF := GF) (hG := hG)]
    (cl : Loc) (ep : GoString) (V : client.WEnv GF) (E : apply.AEnv GF) (γr : ReadNames)
    (γf : GName) (cid mid : w64) (key val : GoString),
  opSizeOk (opPutModel key val []) →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.restart3 ∗
      isNewClient cl [ep] V ∗ client.kvRegsAt (⟨ep, E, γr, cid, mid⟩ : client.SrvAt GF) ∗
      client.putGetInv γr γf key val }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.restart3.put))
      (Val #cl)) (Val #key)) (Val #val))
  {{ (err : GoInterface), RET #err;
      ⌜err ≠ GoInterface.nil⌝ ∨ (⌜err = GoInterface.nil⌝ ∗ monoNatLbOwn γf 1) }}

/-- See the file header (`specOther`). -/
abbrev put.specOther : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)] [ContextErrsClient (GF := GF) (hG := hG)]
    (cl : Loc) (ep : GoString) (V : client.WEnv GF) (E : apply.AEnv GF) (γr : ReadNames)
    (γf : GName) (cid mid : w64) (key val key' val' : GoString),
  key' ≠ key → opSizeOk (opPutModel key' val' []) →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.restart3 ∗
      isNewClient cl [ep] V ∗ client.kvRegsAt (⟨ep, E, γr, cid, mid⟩ : client.SrvAt GF) ∗
      client.putGetInv γr γf key val }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.restart3.put))
      (Val #cl)) (Val #key')) (Val #val'))
  {{ (err : GoInterface), RET #err; True }}

end spec

end restart3
end EtcdGrove
end Perennial
