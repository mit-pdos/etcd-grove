/-
The package fact of `server/v3/storage/wal/walpb` (the part's translation): `ErrCRCMismatch`
(record.go, `errors.New("walpb: crc mismatch")`, a translated initializer) holds for good an error whose
`Error()` returns (`errOk`), which `Record.Validate`'s spec takes, and on which `errors.Is` returns for every
pointer target (`errIsTerm`, an `*errorString` leaf; 2026-11-14, `wal-vsnap4`), its message in its field (`errors.New`'s
`*errorString`, 2026-11-22: `WalDecEnvSupply`'s proof). WAL package init, 2026-11-13.
-/
module

public import GeneratedProof.go_etcd_io.etcd.server.v3.storage.wal.walpb
public import Proof.go_etcd_io.raft.v3.Base
public import Spec.fmt.ErrorfErrs
public import Spec.fmt.ErrorfErrsNot

@[expose] public section

set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

namespace EtcdGrove

/-- `walpb`'s fact: `ErrCRCMismatch` holds an error whose `Error()` returns and on which `errors.Is` returns,
read-only: an `*errorString` whose field holds `"walpb: crc mismatch"` (2026-11-22, so that it differs from
`io.EOF`, `WalDecEnvSupply`). -/
abbrev walpb.walpbInit : IProp GF :=
  iprop(∃ e : GoInterfaceOk,
    globalAddr go_etcd_io.etcd.server.v3.storage.wal.walpb.ErrCRCMismatch ↦□ GoInterface.ok e ∗
    errOk e ∗ errIsTerm (GoInterface.ok e) ∗
    ∃ x : Loc, ⌜e = ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩⌝ ∗
      x.[errors.errorString, go!"s"] ↦□ go!"walpb: crc mismatch")

end EtcdGrove

namespace go_etcd_io.etcd.server.v3.storage.wal.walpb

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal.walpb :=
  define_is_pkg_init EtcdGrove.walpb.walpbInit
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal.walpb :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.storage.wal.walpb

end init

end Perennial
