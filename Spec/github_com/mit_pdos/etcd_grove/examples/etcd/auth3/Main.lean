/- Lean-first (no Rocq counterpart).

`Main()` (`examples/etcd/auth3/auth3.go`; the auth3 Scope's A1, `notes/auth3-scope.md`): three etcd
members of one new cluster started in process with auth on (the simple token provider, etcd's
default token TTL, the examples' no-snapshot settings; `startMember`, each serving its raft handler
on its own peer listener), then authkv's run on the first (`auth.Run`: its gRPC API served at its
client address, the auth state set up and auth enabled through a client of it, the four
principals' workloads through clients of it, root's last write and the history's check, `u`'s
watch check).

**The triple** (the closed theorem's form, as putget3's and authkv's): from the package's
`isPkgInit`, the members' start bundles (each member's WAL directory fresh, the right to listen on
its peer address with its HTTP protocol unregistered, and member 1's on its client address), the
main thread's token and `Main`'s named premises (`etcd_auth3.premises`, putget3's at auth3's
configuration), `Main()` does not panic and returns `Ok` (`0`), `Failed` (`1`: a member's start,
`Serve`, a client's creation, a step of the set-up or root's last put failed) or `WatchEnded`
(`2`). Not panicking is authkv's auth result (`auth/Main.lean`'s header), for the first member of a
three-member cluster whose followers apply every entry, the set-up's admin entries and the
`Authenticate` entries included, with auth on.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth3.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth3.Base
public import Proof.go_etcd_io.etcd.client.v3.ErrorsNewOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_auth3

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.auth3.Assumptions]

/-- See the file header. -/
abbrev Main.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [_root_.Perennial.errors.Assumptions]
    [_root_.Perennial.fmt.Assumptions] [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)] [ContextErrsClient (GF := GF) (hG := hG)]
    (N : Nat) (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8))
    (boot : List LogEntry),
  etcd_putget3.BootFacts id₁ id₂ id₃ ps ctxs boot →
  threadBound GF ≤ 2 ^ 28 →
  srvLevels (GF := GF) → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  N + 7 + bootWB ≤ backend.wbInit →
  authRecordsFit → apply.backendUnderQuota → grpcRepliesFit → storage.diskOk →
  v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.auth3 ∗
      etcdstart.memberStartRes (GF := GF) name₁ ⟨some peerAddr₁, some clientAddr₁⟩ ∗
      etcdstart.memberStartRes (GF := GF) name₂ ⟨some peerAddr₂, none⟩ ∗
      etcdstart.memberStartRes (GF := GF) name₃ ⟨some peerAddr₃, none⟩ ∗
      threadTok ∗ premises N id₁ id₂ id₃ ps ctxs boot }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.auth3.Main)) (Val #()))
  {{ (r : w64), RET #r; ⌜r = W64 0 ∨ r = W64 1 ∨ r = W64 2⌝ }}

end spec

end etcd_auth3
end EtcdGrove
end Perennial
