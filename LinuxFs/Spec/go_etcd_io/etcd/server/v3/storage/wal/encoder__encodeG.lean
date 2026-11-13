/-
`encoder.encode` over a writer with an acceptance guard (`io.writerStreamG`, `Handle.lean`), W6 of
`notes/wal-fsext-plan.md`: `encoder.encode.spec` (over `io.writerStream`) with the guard threaded.
The WAL's tail is crash-tracked, so its writer is only a `writerStreamG` (no `W` makes the plain
contract true of it). Taken as a hypothesis by the WAL's proofs until the page writer's and the
encoder's proofs are re-run over `writerStreamG` (their writes are prefixes of `out ++ pend ++
frame`, which the premise guards; `G` prefix-closed). Lean-first.
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
holding of everything the encoder may write (`out ++ pend ++` the record's frame; `G`
prefix-closed). -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.encoder.encode.specG : Prop :=
  ∀ (e : Loc) (wi : GoInterfaceOk) (W G : List w8 → IProp GF) (out pend : List w8) (c : w32)
    (rp : Loc) (t : w64) (d : List w8),
  recSize (recOf ⟨t, hash.crc32.crc32c c d, d⟩) < 2 ^ 47 →
  ⊢ io.writerStreamG wi W G -∗ (□ ∀ xs ys, ⌜xs <+: ys⌝ -∗ G ys -∗ G xs) -∗
    {{ encEnv ∗ ownEncoder e wi c pend ∗ W out ∗ encRecIn rp t d ∗
        G (out ++ pend ++ frame (walRecEnc ⟨t, hash.crc32.crc32c c d, d⟩)) }}
      (App (Val (e @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.encoder.ty @!!
        go!"encode")) (Val #rp))
    {{ (err : GoInterface), RET #err;
        ∃ ys pend' : List w8, W (out ++ ys) ∗ ownEncoder e wi (hash.crc32.crc32c c d) pend' ∗
          recRoC rp (recOf ⟨t, hash.crc32.crc32c c d, d⟩) ∗
          ⌜(err = GoInterface.nil →
              ys ++ pend' = pend ++ frame (walRecEnc ⟨t, hash.crc32.crc32c c d, d⟩)) ∧
            (err ≠ GoInterface.nil → pend' = [] ∧
              ys <+: pend ++ frame (walRecEnc ⟨t, hash.crc32.crc32c c d, d⟩))⌝ }}

/-- `w.saveCrc(prevCrc)` (S/wal.go:1164-1166), for `cut` and `Create` (whose encoders write files
they own, or the tail): `encode(&Record{Type: CrcType, Crc: &prevCrc})`, the record without data,
whose CRC the encoder sets to its own (`crc32c c [] = c`); over any guarded writer. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.saveCrc.spec : Prop :=
  ∀ (w e : Loc) (wi : GoInterfaceOk) (W G : List w8 → IProp GF) (out pend : List w8) (c prev : w32),
  ⊢ io.writerStreamG wi W G -∗ (□ ∀ xs ys, ⌜xs <+: ys⌝ -∗ G ys -∗ G xs) -∗
    {{ encEnv ∗ structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"encoder" w ↦ e ∗
        ownEncoder e wi c pend ∗ W out ∗
        G (out ++ pend ++ frame (walRecEnc ⟨crcType, hash.crc32.crc32c c [], []⟩)) }}
      (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!!
        go!"saveCrc")) (Val #prev))
    {{ (err : GoInterface), RET #err;
        ∃ ys pend' : List w8, structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"encoder" w ↦ e ∗
          W (out ++ ys) ∗ ownEncoder e wi (hash.crc32.crc32c c []) pend' ∗
          ⌜(err = GoInterface.nil →
              ys ++ pend' = pend ++ frame (walRecEnc ⟨crcType, hash.crc32.crc32c c [], []⟩)) ∧
            (err ≠ GoInterface.nil → pend' = [] ∧
              ys <+: pend ++ frame (walRecEnc ⟨crcType, hash.crc32.crc32c c [], []⟩))⌝ }}

end spec

end EtcdGrove
end Perennial
