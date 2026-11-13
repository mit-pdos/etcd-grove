/-
`e.flush()` (`server/storage/wal/encoder.go:110-114`): under `e.mu`, the page writer's `Flush`: hands
the pending bytes `pend` to the writer and drops the buffer whatever it returns (on success the writer
has all of `pend`; on an error it is broken, `B out pend`, `io.writerStream`). `specP`: the same over a
guarded stream (`io.writerStreamP wi ok W B`, `ok` prefix-closed, holding of `out ++ pend`), for the
WAL's tail (`wal.tailWriter`); `spec` (a length bound) is its instance. Proved in
`LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/encoder__flush.lean`. W6; Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.EncDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open WalEnc WalFs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.encoder.flush.spec : Prop :=
  ∀ (e : Loc) (wi : GoInterfaceOk) (W : List w8 → IProp GF) (B : List w8 → List w8 → IProp GF)
    (lim : Nat) (out pend : List w8) (c : w32),
  out.length + pend.length ≤ lim →
  ⊢ io.writerStream wi lim W B -∗
    {{ encEnv ∗ ownEncoder e wi c pend ∗ W out }}
      (App (Val (e @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.encoder.ty @!!
        go!"flush")) (Val #()))
    {{ (err : GoInterface), RET #err;
        ownEncoder e wi c [] ∗
        ((⌜err = GoInterface.nil⌝ ∗ W (out ++ pend)) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ B out pend)) }}

/-- See the file header. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.encoder.flush.specP : Prop :=
  ∀ (e : Loc) (wi : GoInterfaceOk) (W : List w8 → IProp GF) (B : List w8 → List w8 → IProp GF)
    (ok : List w8 → Prop) (out pend : List w8) (c : w32),
  (∀ xs ys, xs <+: ys → ok ys → ok xs) → ok (out ++ pend) →
  ⊢ io.writerStreamP wi ok W B -∗
    {{ encEnv ∗ ownEncoder e wi c pend ∗ W out }}
      (App (Val (e @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.encoder.ty @!!
        go!"flush")) (Val #()))
    {{ (err : GoInterface), RET #err;
        ownEncoder e wi c [] ∗
        ((⌜err = GoInterface.nil⌝ ∗ W (out ++ pend)) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ B out pend)) }}

end spec

end EtcdGrove
end Perennial
