/-
`checkTxnReads(who, ops)` (`examples/authkv/authkv.go`; the auth plan's E2f). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.Checks
public import Proof.go_etcd_io.etcd.client.v3.InvKVConn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI

/-- A transaction's operation's response holds only keys `who` may read: a range's key-values
(the responses of other kinds hold none `checkTxnReads` reads). -/
def respReadsOk [GooseExts] (who : GoString) : OpRespM → Prop
  | .range _ kvs _ _ => ∀ kv ∈ kvs, permittedK who kv.key
  | _ => True

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.authkv.Assumptions]

/-- `checkTxnReads(who, ops)` returns (does not panic) when every range response among the
responses `ops` holds (`opRespsMsg`, read-only, as a transaction reply's) holds only keys `who`
may read (`respReadsOk`). -/
abbrev checkTxnReads.spec : Prop :=
  ∀ (who : GoString) (sl : GoSlice) (ps : List Loc) (ms : List OpRespM),
  (∀ m ∈ ms, respReadsOk who m) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.authkv ∗
      sl ↦*□ ps ∗ opRespsMsg ps ms }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.authkv.checkTxnReads))
      (Val #who)) (Val #sl))
  {{ RET #(); True }}

end spec

end authkv
end EtcdGrove
end Perennial
