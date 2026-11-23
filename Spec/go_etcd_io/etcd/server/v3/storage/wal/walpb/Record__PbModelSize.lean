/-
`(*walpb.Record).PbModelSize(cached)` (the protobuf model's size method, `pbmodel_gen.go`; #37 stage
S3) on a frozen record holding exactly `c` (`recRoC`), in the cache mode `Any` (`PbCache.lean`: the
size cache is in the record's invariant, `recHidden`, and nothing is known of it): uncached, it
returns `c`'s size (`recSize`, the length of `recEnc c`) and stores the cache (size + 1) atomically;
cached, it returns the cache minus one if the cache is above 0, else recomputes as uncached, so
nothing is claimed of its result. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.walpb.PbRecord

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open WalEnc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.server.v3.storage.wal.walpb.Assumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.PbModelSize.spec : Prop :=
  ∀ (l : Loc) (c : RecC) (cached : Bool), recSize c < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.sync.atomic ∗ recRoC (GF := GF) l c }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.ty
      @!! go!"PbModelSize")) (Val #cached))
  {{ (n : w64), RET #n; ⌜cached = false → sint.Z n = recSize c⌝ }}

end spec

end EtcdGrove
end Perennial
