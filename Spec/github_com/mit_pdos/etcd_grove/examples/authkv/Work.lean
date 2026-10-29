/-
`Work(cli, who)` (`examples/authkv/authkv.go`; `notes/authkv-main-plan.md`, S2; draft,
2026-10-29). Lean-first (no Rocq counterpart).

Principal `who`'s workload on the client `cli`: puts, ranges, transactions, deletes inside and
outside `[a, b)`, and a watch of the prefix `c/` from revision 1, each reply checked (`refused`,
`checkKVs`, `checkTxnReads`, the watch's events).

**The triple:** `Work` does not panic, for a principal of the program (`principals`) on a client
of authkv's member with auth on (`isNewClient`; its `KV` a `*kv` over `conn`, `clientTokAt`'s
parts) whose attempts carry the principal's token (`akPrincipal`), the member's KV methods with
auth on (`akKVOn`) and its watch server's facts (`watchAddrFacts`, S4), after the set-up: the
history invariant (S1, `akHistInv`) and the auth state fixed (S6, `akAuthFixed`). Not panicking is
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
    (cl api conn : Loc) (who : GoString) (V : WEnv GF) (s : Loc) (E : apply.AEnv GF)
    (ρ : ReqNames) (cid mid : w64) (γa : auth.AuthNames) (setupRev : Nat)
    (Lset : List EntryModel),
  who ∈ principals → E.authMode = .on γa →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.authkv ∗
      isNewClient cl [go!"127.0.0.1:23916"] V ∗ watchAddrFacts V ∗
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"KV" cl ↦□
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty) #api :
          GoInterface) ∗
      kvObjAtC api conn [go!"127.0.0.1:23916"] ∗ akPrincipal conn γa who ∗
      akKVOn go!"127.0.0.1:23916" s E ρ ρ.rd cid mid ∗
      akHistInv ρ.kv setupRev ∗ akAuthFixed ρ Lset }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.authkv.Work)) (Val #cl))
      (Val #who))
  {{ RET #(); True }}

end spec

end authkv
end EtcdGrove
end Perennial
