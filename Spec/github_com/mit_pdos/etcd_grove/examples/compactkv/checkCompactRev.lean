/-
`checkCompactRev(cli, key)` (`examples/compactkv/compactkv.go`; C3's watch side, 2026-11-02): a
watch of `key` from revision `2`, its first response's compaction revision (`common.CompactRev`),
and, if it is a compaction's, a latest `Get` of `key`, panicking if the `Get` reads below the
compaction revision plus the retention (`1`). Lean-first (no Rocq counterpart).

**The triple:** from `Main`'s client of the one member at `127.0.0.1:23794` (`isNewClient`, with
its watcher's facts there, `watchAddrFacts`, and the member's KV methods, `kvRegsAt`, at the
member's read names `γr`, whose cluster retention is `1`), the rounds' invariant (`roundsInv`, its
revision counter) and the KV invariant (`kvInv`): it returns (it does not panic).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.compactkv.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.compactkv.RoundCalls
public import Proof.go_etcd_io.etcd.client.v3.InvClientNewResult

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace compactkv

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver client

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.compactkv.Assumptions]

/-- See the file header. -/
abbrev checkCompactRev.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]
    [ContextErrsClient (GF := GF) (hG := hG)]
    (cl : Loc) (key : GoString) (R : v3rpc.WSrv GF) (E : apply.AEnv GF) (γr : ReadNames)
    (cid mid : w64) (γf γl γv : GName) (keys : List GoString) (val : GoString),
  key.length ≤ 2 → γr.kv.cret = 1 →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.compactkv ∗
      isNewClient cl [go!"127.0.0.1:23794"]
        (srvWEnv R go!"127.0.0.1:23794" [] null null go!"k" null γr.kv) ∗
      watchAddrFacts (srvWEnv R go!"127.0.0.1:23794" [] null null go!"k" null γr.kv) ∗
      kvRegsAt (⟨go!"127.0.0.1:23794", E, γr, cid, mid⟩ : SrvAt GF) ∗ mvcc.idxCert E.γ.idx [] ∗
      roundsInv γr γf γl γv keys val ∗ kvInv γr.raft γr.kv }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.compactkv.checkCompactRev))
      (Val #cl)) (Val #key))
  {{ RET #(); True }}

end spec

end compactkv
end EtcdGrove
end Perennial
