/- Lean-first (no Rocq counterpart).

`Main()` (`examples/authkv/authkv.go`; the auth plan's E2b, D-AU5): one etcd member started in
process with the simple token provider (on `authkv`'s ports), a client with no user name that
sets up the auth state and enables auth (`SetUp`: root with the root role, role `r` granted
`READWRITE` on `[a, b)`, users `u` with `r` and `v` with no role), clients that authenticate as
root, `u` and `v`, then the four principals' workloads at once (`Work`: `u`, `v`, the client with
no token, the same client with a token no provider issued), root's last write `z/end`, root's
watch of every key from revision `1` read up to it and the history's check (`CheckHistory`), and
`u`'s watch of `[a, b)`.

**The triple** (the closed theorem's form, as watchkv's): from the package's `isPkgInit`, the
right to listen on the client address `127.0.0.1:23916`, the main thread's token and `Main`'s
named premises (`authkv.premises`, putget's at authkv's configuration), `Main()` does not panic
and returns `Ok` (`0`: every check ran and passed), `Failed` (`1`: a step of the set-up failed) or
`WatchEnded` (`2`: a watch ended before it reported what it was read for). Not panicking is the
auth result (`notes/decisions.md`, "E2b of the auth plan"): every request the auth state
(`authkv.setupSt`) refuses its principal returned an error, every reply holds only keys its
principal may read (`u`'s ranges, transactions and watch), and every write of the history after
the set-up up to `z/end` is one its principal was permitted (`authkv.permittedK`, the model's
verdict at `setupSt`: `granted_setupSt_iff`).

The premises are watchkv's for the server's start, stated before the proof: an auth-enabled
server's proof may need others (the client's auth contract, `ClientAuth.lean`, and what E2a's
`NewAuthStore` gives).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.ClientAuth
public import Proof.go_etcd_io.etcd.client.v3.ErrorsNewOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.authkv.Assumptions]

/-- See the file header. -/
abbrev Main.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [_root_.Perennial.errors.Assumptions]
    [_root_.Perennial.fmt.Assumptions] [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)] [ContextErrsClient (GF := GF) (hG := hG)]
    (N : Nat) (id : w64) (bootLog : List EntryM),
  putget.BootFacts id bootLog →
  threadBound GF ≤ 2 ^ 29 → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota →
  storage.dbOpensOk → v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.authkv ∗
      netAddrFree (GF := GF) go!"127.0.0.1:23916" ∗ threadTok ∗ premises N id bootLog }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.authkv.Main)) (Val #()))
  {{ (r : w64), RET #r; ⌜r = W64 0 ∨ r = W64 1 ∨ r = W64 2⌝ }}

end spec

end authkv
end EtcdGrove
end Perennial
