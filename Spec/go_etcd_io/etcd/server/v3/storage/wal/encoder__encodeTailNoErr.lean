/-
`encoder.encode` on the WAL's tail with no I/O error (unit `noioerr`, `notes/wal-units/noioerr.md`):
`encoder.encode.specTail` over a semantics whose steps satisfy **no I/O error on chosen files**
(`FsStepSat (NoIoErr Sio)`), coverage (a) for now (every file of the roots' trees, `∀ st i, Sio.ino st i`;
`notes/decisions.md`, "fsExt: no I/O errors on chosen files"), the encoder's bytes and the record's frame
ending at most at `maxBytes` (ext4's `s_maxbytes`, where a write fails with `EFBIG` whatever the premise).
Proved in `Proof/.../wal/encoder__encodeTailNoErr.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.encoder__encodeTail
public import GooseLang.Ext.Fs.Premises
public import GooseLang.Ext.Fs.FilteredSem

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
variable {Sio : IoSet} [FsStepSat (NoIoErr Sio)]

/-- **`e.encode(rec)` on the WAL's tail with no I/O error** (see the file header): `specTail`'s success
arm, always. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.encoder.encode.specTailNoErr (Mr : WalMarshal) : Prop :=
  (∀ st i, Sio.ino st i) →
  ∀ (R : Roots) (jr : Ino) (r : GoString) (e f : Loc) (fd : w64) (name dir : GoString) (γ : GName)
    (i : Ino) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (o0 sz : Nat)
    (out pend : List w8) (c : w32) (rp : Loc) (t : w64) (d : List w8),
  recSize (recOf ⟨t, hash.crc32.crc32c c d, d⟩) < 2 ^ 47 →
  out ++ pend ++ frame (walRecEnc ⟨t, hash.crc32.crc32c c d, d⟩) <+: (tailStream Mr H md cuts).drop o0 →
  o0 + out.length ≤ sz → sz ≤ 0xffffffff000 →
  o0 + (out ++ pend ++ frame (walRecEnc ⟨t, hash.crc32.crc32c c d, d⟩)).length ≤ maxBytes →
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ encEnv ∗ ownEncoder e (wal.fileWi f) c pend ∗
      walTailW (W := W) f fd name dir γ i H md cuts o0 sz out TailMetaW ∗ encRecIn rp t d }}
    (App (Val (e @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.encoder.ty @!!
      go!"encode")) (Val #rp))
  {{ (err : GoInterface), RET #err;
      ∃ pend' : List w8, ownEncoder e (wal.fileWi f) (hash.crc32.crc32c c d) pend' ∗
        recRoC rp (recOf ⟨t, hash.crc32.crc32c c d, d⟩) ∗
        ∃ (out' : List w8) (sz' : Nat), ⌜err = GoInterface.nil ∧
            out' ++ pend' = out ++ pend ++ frame (walRecEnc ⟨t, hash.crc32.crc32c c d, d⟩) ∧
            o0 + out'.length ≤ sz' ∧ sz' ≤ 0xffffffff000⌝ ∗
            walTailW (W := W) f fd name dir γ i H md cuts o0 sz' out' TailMetaW }}

end spec

end EtcdGrove
end Perennial
