/-
`Work(cli, who)` (`examples/authkv/authkv.go`; `notes/authkv-main-plan.md`, S2; draft,
2026-10-29). Lean-first (no Rocq counterpart).

Principal `who`'s workload on the client `cli`: puts, ranges, transactions, deletes inside and
outside `[a, b)`, and a watch of the prefix `c/` from revision 1, each reply checked (`refused`,
`checkKVs`, `checkTxnReads`, the watch's events).

**The triple:** `Work` does not panic, for a principal of the program (`principals`) on a client
of authkv's member with auth on (`isNewClient`) whose attempts carry the principal's tokens
(`clientTokAt` at `akTokP`), the member's KV methods with auth on (`akKVOn`), its TLS identity off
(`srvTLSId`, refuted: the member's configuration has `ClientCertAuthEnabled` false; round 1, F-W2),
and the watcher's facts as `Main` has them (`watchAddrFacts`; the auth-on watch, S4/G2, replaces
it), the watcher's one member the server `s` at `E` at authkv's address, its KV state variable
`ρ.kv`'s (round 3, F1: what `watcher_of_clientTokAt` and `watcher.Watch.spec` need), after the
set-up: the history invariant (S1, `akHistInv`) and the auth state fixed (S6,
`akAuthFixed`). Not panicking is
the workload's part of the auth result: every request the auth state refuses `who` returned an
error, every reply holds only keys `who` may read, and every write `who`'s client sends keeps the
history invariant (its update, `akHist_writeAu`, at the write's grant).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.WorkEnv
public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver client

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.authkv.Assumptions]

/-- See the file header. -/
abbrev Work.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [_root_.Perennial.errors.Assumptions]
    [_root_.Perennial.fmt.Assumptions] [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)] [ContextErrsClient (GF := GF) (hG := hG)]
    (cl : Loc) (who : GoString) (V : WEnv GF) (s : Loc) (E : apply.AEnv GF)
    (ρ : ReqNames) (cid mid : w64) (γa : auth.AuthNames) (Lset : List EntryModel) (n : Nat),
  who ∈ principals → E.authMode = .on γa →
  V.addr = go!"127.0.0.1:23916" ∧ V.mem = (fun _ => (V.addr, V.R)) ∧ V.nm = 1 ∧ V.R.s = s ∧
    V.R.E = E ∧ V.kst = ρ.kv.st →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.authkv ∗
      isNewClient cl [go!"127.0.0.1:23916"] V ∗ watchAddrFacts V ∗
      clientTokAt cl [go!"127.0.0.1:23916"] (akTokP γa who) ∗
      akKVOn go!"127.0.0.1:23916" s E ρ cid mid ∗ □ (srvTLSId s -∗ False) ∗
      akHistInv ρ.kv ∗ akAuthFixed γa ρ Lset n }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.authkv.Work)) (Val #cl))
      (Val #who))
  {{ RET #(); True }}

end spec

end authkv
end EtcdGrove
end Perennial
