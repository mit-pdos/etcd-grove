/-
The trust boundary: `fileutil.TouchDirAll` (names-only; WAL W4a, 2026-11-11). An axiom: why the
statement is true of the Go code is in its spec's docstring.
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.TouchDirAll

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt absDiskExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

axiom fileutil.TouchDirAll.wp_proof : fileutil.TouchDirAll.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
