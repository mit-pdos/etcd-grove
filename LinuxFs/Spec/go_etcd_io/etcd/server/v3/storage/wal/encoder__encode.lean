/-
`e.encode(rec)` (`server/storage/wal/encoder.go:66-98`), on a record the WAL built
(`encRecIn rp t d`: type `t`, data `d`): under `e.mu`, chains the CRC over `d` (`c' = crc32c c d`),
sets `rec.Crc = &c'` (freezing the record: afterwards `recRoC rp (recOf ⟨t, c', d⟩)`), marshals it
(`MarshalAppend` into the scratch buffer `e.buf[:0]` with the cached size, or `proto.Marshal` when it
is larger than the buffer) and writes its frame (`prepareDataWithPadding`, `write`) to the page
writer. On success the page writer has accepted `frame (walRecEnc ⟨t, c', d⟩)` (the length word,
the record bytes `recEnc (recOf …)`, the padding) after its pending bytes; on an error (only the
writer's: the marshalling cannot fail at `walpb.Record`) its buffer is dropped and the writer is
broken by one of its `Write`s, `B (out ++ a) b`, `a ++ b` a prefix of pending ++ the frame. The CRC is `c'` either way. Premise: the record's size below
`2^47` (`MarshalAppendCachedRecord`'s). The nil-type branch ("record is missing type") is excluded
by `encRecIn`. Proved in `LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/encoder__encode.lean`.
W6; Lean-first.
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.encoder.encode.spec : Prop :=
  ∀ (e : Loc) (wi : GoInterfaceOk) (W : List w8 → IProp GF) (B : List w8 → List w8 → IProp GF)
    (lim : Nat) (out pend : List w8) (c : w32) (rp : Loc) (t : w64) (d : List w8),
  recSize (recOf ⟨t, hash.crc32.crc32c c d, d⟩) < 2 ^ 47 →
  out.length + pend.length + (frame (walRecEnc ⟨t, hash.crc32.crc32c c d, d⟩)).length ≤ lim →
  ⊢ io.writerStream wi lim W B -∗
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

end spec

end EtcdGrove
end Perennial
