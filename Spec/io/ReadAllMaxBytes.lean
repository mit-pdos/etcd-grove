/-
`io.ReadAll(lr)` of a `http.MaxBytesReader` `lr`: the trust boundary (`io.ReadAll` and
`net/http` are names-only; PR etcd#22243, the peer hashKV handler). Lean-first (no Rocq
counterpart).

What the two do together (Go 1.27, `net/http/request.go`'s `maxBytesReader.Read`): each read
asks the body for at most the bytes left plus one; once the body yields more than `n` bytes in
all, the reader returns `n` of them and `&MaxBytesError{n}` from then on, reading nothing more; a
body error before that is returned as it is. So `ReadAll` consumes `min(len data, n + 1)` bytes of
the body, whatever the body holds.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvHashKV

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3
  go_etcd_io.etcd.cache.v3
  go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `io.ReadAll(lr)`, `lr` a `MaxBytesReader(_, body, n)` with `c` left in `body`, consumes
`min(len c.data, n + 1)` bytes of the body and returns
* if the body has more than `n` bytes: its first `n` and a `*http.MaxBytesError` `m`;
* else, if it fails with `e`: its bytes and `e` (with `e`'s error tree, for `errors.As`);
* else: its bytes and `nil`. -/
abbrev io.ReadAllMaxBytes.spec : Prop :=
  ∀ (lr body : GoInterface) (n : w64) (c : http.BodyContent),
  {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ http.maxBytesR lr body n ∗ http.bodyR body c }}
    (App (Val (@! _root_.Perennial.io.ReadAll))
      (Val #(lr : GoInterface)))
  {{ (sl : GoSlice) (err : GoError), RET (PairV #sl #err);
      http.bodyR body (c.drop (min c.data.length (uint.nat n + 1))) ∗
      ((⌜uint.nat n < c.data.length⌝ ∗ sl ↦* c.data.take (uint.nat n) ∗
          ∃ m : Loc, ⌜err = interface.mkOk
            (go.GoType.PointerType _root_.Perennial.net.http.MaxBytesError.ty) #m⌝) ∨
       (⌜c.data.length ≤ uint.nat n⌝ ∗ sl ↦* c.data ∗
          ∃ e, ⌜c.err = some e ∧ err = GoInterface.ok e⌝ ∗
            ∃ S : GoError → Prop, ⌜S err⌝ ∗
              _root_.Perennial.errors.isErrorTree (GF := GF) S Loc
                (go.GoType.PointerType _root_.Perennial.net.http.MaxBytesError.ty)) ∨
       (⌜c.data.length ≤ uint.nat n ∧ c.err = none ∧ err = interface.nil⌝ ∗ sl ↦* c.data)) }}

end spec

end EtcdGrove
end Perennial
