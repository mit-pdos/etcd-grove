/-
**`RenewHTTP`'s errors that are not `lease.ErrLeaseNotFound`** (mapkeys, 2026-11-26; the vocabulary of
`leasehttp.RenewHTTP.spec`'s third arm). Lean-first.

`RenewHTTP` returns some errors as they come from the libraries it calls: `http.NewRequest`'s and
`Client.Do`'s (`*url.Error`, with an `Unwrap`), `io.ReadAll`'s on the reply's body (over TLS a
`tls.RecordHeaderError`, a struct with fields; `*net.OpError`, ...), `proto.Marshal`'s, and the decode's
wrapped by `fmt.Errorf`'s `%w`. None is a leaf `status.FromError` takes, nor a key of `togRPCError`'s
map (`errKeyOk`), so `applyErrIs` is false of them (`notes/axiom-review/errkeys-proto-renewhttp.md`).
What its one caller, `EtcdServer.LeaseRenew`, needs of them is only that `errors.Is(err,
lease.ErrLeaseNotFound)` answers `false` (it then tries the next URL): the error is in an error tree
(`errors.errorIsTree`, Go's `Is` and `Unwrap` methods returning) of which no error is
`ErrLeaseNotFound`'s value and no `Is` method answers `true` for it. True of Go: `ErrLeaseNotFound` is
an `errors.New` pointer that only `lease` and its importers hold, and the libraries' `Is` methods
(`syscall.Errno`'s, `*internal/errors.wrapError`'s) compare with their own sentinels.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.leasehttp.Base
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base

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

/-- **An error for which `errors.Is(err, lease.ErrLeaseNotFound)` answers `false`** (persistent; see the
file header): for `ErrLeaseNotFound`'s value `e`, an error tree at `e` holding `err`, whose errors of
`e`'s type hold pointers (`TreeTyped`, Go's typing), none of which is `e` or has an `Is` method that may
answer `true` (`M`): `errors.noMatchTree` at `e` (nonleaf-status-errs, 2026-11-26: the tree stated
once for this and `notCtxTree`; the same statement, `ii ≠ e` read as `ok ii ≠ ok e`). -/
def leasehttp.notLeaseNotFound (err : GoInterface) : IProp GF :=
  iprop(□ ∀ e : GoInterfaceOk,
    globalAddr go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound ↦□ GoInterface.ok e -∗
    errors.noMatchTree (GF := GF) (fun S => _root_.Perennial.errors.TreeTyped S (GoInterface.ok e))
      (fun _ => True) err (GoInterface.ok e))

instance leasehttp.notLeaseNotFound_persistent (err : GoInterface) :
    Persistent (leasehttp.notLeaseNotFound (GF := GF) err) := by
  unfold leasehttp.notLeaseNotFound; infer_instance

end defs

end EtcdGrove
end Perennial
