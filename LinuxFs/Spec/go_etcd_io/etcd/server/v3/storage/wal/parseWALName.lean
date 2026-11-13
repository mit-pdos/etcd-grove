/-
`parseWALName(str)` (S/util.go:108-114): `errBadWALName` unless `str` ends in `.wal`, then
`fmt.Sscanf(str, "%016x-%016x.wal", &seq, &index)` (`fmt.SscanfWalName.spec`, `fmt.scanWalName`). A
segment's name (`fmt.walNameStr`) parses to its sequence number and index
(`fmt.scanWalName_walNameStr`). Proved in
`LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/parseWALName.lean`. W5 of
`notes/wal-fsext-plan.md`; Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.PkgInit
public import Spec.fmt.SscanfWalName
public import Spec.strings.HasSuffix

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- See the file header: a name that ends in `.wal` and scans returns its two numbers and `nil`;
one that does not end in `.wal`, or does not scan, returns an error. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.parseWALName.spec : Prop :=
  ∀ (str : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.parseWALName)) (Val #str))
  {{ (seq idx : w64) (err : GoInterface), RET (PairV (PairV #seq #idx) #err);
      ⌜(∀ x y, go!".wal" <:+ str → fmt.scanWalName str = .ok x y →
          err = GoInterface.nil ∧ seq = x ∧ idx = y) ∧
        (¬ go!".wal" <:+ str ∨ fmt.scanWalName str = .err → err ≠ GoInterface.nil)⌝ }}

end spec

end EtcdGrove
end Perennial
