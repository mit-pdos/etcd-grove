/-
`encoder.encode` on the WAL's tail (W6 of `notes/wal-fsext-plan.md`), a hypothesis of `SaveSnapshot`'s,
`saveEntry`'s and `saveState`'s proofs until the tail's writer accepts writes past its preallocated size (the
window of writes past the size, I3b log): `encoder.encode.specG` over the tail's writer (`wal.tailWriter`)
without `tailOk`'s size clause, the size growing with the writes (and with them the tail's resize window open,
`TailMetaW`, until a `sync`). The stream bound (ledger 2026-11-14, "the batch's size"): the encoder's bytes and
the record's frame below ext4's maximum offset, the caller's (`Save`'s batch bound and the handle's stream end);
the post's size then below it too. Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.encoder__encodeG

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs WalEnc WalFs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- **`e.encode(rec)` on the WAL's tail** (see the file header): the encoder's bytes and the record's frame a
prefix of the tail's intended stream past `o0`, below ext4's maximum offset; on success, the tail written to some `out'` (the encoder holding
`pend'`, `out' ++ pend'` everything it was given), its size `sz'` grown as needed. *Error*: the tail's
resources lost (the invariant holds what was written). -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.encoder.encode.specTail (Mr : WalMarshal) : Prop :=
  ∀ (R : Roots) (jr : Ino) (r : GoString) (e f : Loc) (fd : w64) (name dir : GoString) (γ : GName)
    (i : Ino) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (o0 sz : Nat)
    (out pend : List w8) (c : w32) (rp : Loc) (t : w64) (d : List w8),
  recSize (recOf ⟨t, hash.crc32.crc32c c d, d⟩) < 2 ^ 47 →
  out ++ pend ++ frame (walRecEnc ⟨t, hash.crc32.crc32c c d, d⟩) <+: (tailStream Mr H md cuts).drop o0 →
  o0 + out.length ≤ sz → sz ≤ 0xffffffff000 →
  o0 + out.length + pend.length + (frame (walRecEnc ⟨t, hash.crc32.crc32c c d, d⟩)).length ≤ 0xffffffff000 →
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ encEnv ∗ ownEncoder e (wal.fileWi f) c pend ∗
      walTailW (W := W) f fd name dir γ i H md cuts o0 sz out TailMetaW ∗ encRecIn rp t d }}
    (App (Val (e @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.encoder.ty @!!
      go!"encode")) (Val #rp))
  {{ (err : GoInterface), RET #err;
      ∃ pend' : List w8, ownEncoder e (wal.fileWi f) (hash.crc32.crc32c c d) pend' ∗
        recRoC rp (recOf ⟨t, hash.crc32.crc32c c d, d⟩) ∗
        ((∃ (out' : List w8) (sz' : Nat), ⌜err = GoInterface.nil ∧
            out' ++ pend' = out ++ pend ++ frame (walRecEnc ⟨t, hash.crc32.crc32c c d, d⟩) ∧
            o0 + out'.length ≤ sz' ∧ sz' ≤ 0xffffffff000 ∧
            o0 + out'.length + pend'.length ≤ 0xffffffff000⌝ ∗
            walTailW (W := W) f fd name dir γ i H md cuts o0 sz' out' TailMetaW) ∨
         ⌜err ≠ GoInterface.nil⌝) }}

end spec

end EtcdGrove
end Perennial
