/-
`encoder.encode` over a guarded stream writer (`io.writerStreamP`, `Proof/io/WriterStream.lean`), W6
of `notes/wal-fsext-plan.md`: `encoder.encode.spec` (over `io.writerStream`, a length bound) with the
bound generalized to a prefix-closed guard `ok` of the stream. The WAL's tail is crash-tracked, so its
writer accepts only its intended bytes (`tailOk`, `Handle.lean`; `wal.tailWriter`, `TailWriter.lean`);
`cut`'s fresh `N.tmp`, owned whole, takes `ok` the length bound (`os.File.writerStream` with
`io.writerStream_P`). Taken as a hypothesis by the WAL's proofs until the page writer's and the
encoder's proofs are re-run over `writerStreamP` (their writes are prefixes of `out ++ pend ++
frame`, which the premise guards). The error form is `encoder.encode.spec`'s (`B`). Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open WalEnc WalFs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- `encode(rec)` (encoder.go:66-95) over a guarded writer: as `encoder.encode.spec`, the guard
`ok` (prefix-closed) holding of everything the encoder may write (`out ++ pend ++` the record's
frame) in place of the length bound. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.encoder.encode.specG : Prop :=
  ∀ (e : Loc) (wi : GoInterfaceOk) (W : List w8 → IProp GF) (B : List w8 → List w8 → IProp GF)
    (ok : List w8 → Prop) (out pend : List w8) (c : w32) (rp : Loc) (t : w64) (d : List w8),
  recSize (recOf ⟨t, hash.crc32.crc32c c d, d⟩) < 2 ^ 47 →
  (∀ xs ys, xs <+: ys → ok ys → ok xs) →
  ok (out ++ pend ++ frame (walRecEnc ⟨t, hash.crc32.crc32c c d, d⟩)) →
  ⊢ io.writerStreamP wi ok W B -∗
    {{ encEnv ∗ ownEncoder e wi c pend ∗ W out ∗ encRecIn rp t d }}
      (App (Val (e @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.encoder.ty @!!
        go!"encode")) (Val #rp))
    {{ (err : GoInterface), RET #err;
        ∃ pend' : List w8, ownEncoder e wi (hash.crc32.crc32c c d) pend' ∗
          recRoC rp (recOf ⟨t, hash.crc32.crc32c c d, d⟩) ∗
          ((∃ ys : List w8, ⌜err = GoInterface.nil ∧
              ys ++ pend' = pend ++ frame (walRecEnc ⟨t, hash.crc32.crc32c c d, d⟩)⌝ ∗
              W (out ++ ys)) ∨
           (∃ a b : List w8, ⌜err ≠ GoInterface.nil ∧ pend' = [] ∧
              a ++ b <+: pend ++ frame (walRecEnc ⟨t, hash.crc32.crc32c c d, d⟩)⌝ ∗
              B (out ++ a) b)) }}

/-- `w.saveCrc(prevCrc)` (S/wal.go:1164-1166), for `cut` and `Create` (whose encoders write files
they own, or the tail): `encode(&Record{Type: CrcType, Crc: &prevCrc})`, the record without data,
whose CRC the encoder sets to its own (`crc32c c [] = c`); over any guarded writer. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.saveCrc.spec : Prop :=
  ∀ (w e : Loc) (wi : GoInterfaceOk) (W : List w8 → IProp GF) (B : List w8 → List w8 → IProp GF)
    (ok : List w8 → Prop) (out pend : List w8) (c prev : w32),
  (∀ xs ys, xs <+: ys → ok ys → ok xs) →
  ok (out ++ pend ++ frame (walRecEnc ⟨crcType, hash.crc32.crc32c c [], []⟩)) →
  ⊢ io.writerStreamP wi ok W B -∗
    {{ encEnv ∗ structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"encoder" w ↦ e ∗
        ownEncoder e wi c pend ∗ W out }}
      (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!!
        go!"saveCrc")) (Val #prev))
    {{ (err : GoInterface), RET #err;
        ∃ pend' : List w8, structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"encoder" w ↦ e ∗
          ownEncoder e wi (hash.crc32.crc32c c []) pend' ∗
          ((∃ ys : List w8, ⌜err = GoInterface.nil ∧
              ys ++ pend' = pend ++ frame (walRecEnc ⟨crcType, hash.crc32.crc32c c [], []⟩)⌝ ∗
              W (out ++ ys)) ∨
           (∃ a b : List w8, ⌜err ≠ GoInterface.nil ∧ pend' = [] ∧
              a ++ b <+: pend ++ frame (walRecEnc ⟨crcType, hash.crc32.crc32c c [], []⟩)⌝ ∗
              B (out ++ a) b)) }}

end spec

end EtcdGrove
end Perennial
