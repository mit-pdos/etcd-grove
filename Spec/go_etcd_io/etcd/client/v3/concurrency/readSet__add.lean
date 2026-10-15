/-
`concurrency.readSet.add(keys, txnresp)` (`client/v3/concurrency/stm.go`). Lean-first (no Rocq counterpart); see
`InvSTM.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvSTM

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- `rs.add(keys, txnresp)`: for each response `i` of `txnresp` (a range response, the read `es[i]`
of `keys[i]`), `rs[keys[i]]` becomes it (`readsAdd`; `keys` has at least as many keys). -/
abbrev readSet.add.spec : Prop :=
  ∀ (m : Loc) (pfx : GoString) (rsMap : GMap GoString Loc) (reads : GMap GoString ReadM)
    (ksl : GoSlice) (ks : List GoString) (resp : Loc) (rsl : GoSlice) (ps : List Loc)
    (es : List ReadM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ m ↦$ rsMap ∗ readsAt pfx rsMap reads ∗ ksl ↦*□ ks ∗
      structFieldRef etcdserverpb.TxnResponse go!"Responses" resp ↦□ rsl ∗ rsl ↦*□ ps ∗
      ⌜ps.length = es.length ∧ ps.length ≤ ks.length⌝ ∗
      □ (∀ (i : Nat) (p : Loc) (k : GoString) (e : ReadM),
        ⌜ps[i]? = some p ∧ ks[i]? = some k ∧ es[i]? = some e⌝ -∗ respOpReadAt pfx k p e) }}
    (App (App (Val (m @!! readSet.ty @!! go!"add")) (Val #ksl)) (Val #resp))
  {{ RET #(); ∃ rsMap' : GMap GoString Loc, m ↦$ rsMap' ∗
      readsAt pfx rsMap' (readsAdd reads (ks.zip es)) }}

end spec

end concurrency
end EtcdGrove
end Perennial
