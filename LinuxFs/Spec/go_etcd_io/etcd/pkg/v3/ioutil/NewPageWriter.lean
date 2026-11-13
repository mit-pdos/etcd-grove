/-
`NewPageWriter(w, pageBytes, pageOffset)` (pagewriter.go): a page writer through `w` with an empty
buffer. `pageBytes` is positive (`verify.Assert`'s condition) and at most the watermark
`defaultBufferBytes` (`128 KiB`; the WAL's is `4 KiB`); `pageOffset` is non-negative and below `2^62`
(a file offset). Proved in `LinuxFs/Proof/go_etcd_io/etcd/pkg/v3/ioutil/NewPageWriter.lean`. WAL W6,
2026-11-13; Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.pkg.v3.ioutil.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.pkg.v3.ioutil.NewPageWriter.spec : Prop :=
  ∀ (wi : GoInterfaceOk) (pB off : w64),
  0 < sint.Z pB → sint.Z pB ≤ 131072 → 0 ≤ sint.Z off → sint.Z off < 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.ioutil }}
    (App (App (App (Val (@! go_etcd_io.etcd.pkg.v3.ioutil.NewPageWriter))
      (Val #(GoInterface.ok wi))) (Val #pB)) (Val #off))
  {{ (pw : Loc), RET #pw; ioutil.ownPageWriter pw wi [] }}

end spec

end EtcdGrove
end Perennial
