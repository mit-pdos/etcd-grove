/- Lean-first (no Rocq counterpart).
# The WAL encoder's vocabulary (W6 of `notes/wal-fsext-plan.md`)

The specs of `encoder.go` (`LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/`) are stated over an
encoder writing through a `*ioutil.PageWriter` (`ioutil.ownPageWriter`) over a stream writer
(`io.writerStream wi W B`, the client's file): the bytes the encoder has accepted are the writer's
(`W out`) followed by the page writer's pending ones (`pend`).

* `ownEncoder e wi c pend`: the `*encoder` at `e`: its page writer over `wi` holding `pend`, its CRC
  digest at `c` (over the Castagnoli table, `ownDecCrc`), its 1 MiB scratch buffer `e.buf` (owned
  whole: `encode` lends `e.buf[:0]` to `MarshalAppend` and gets the array back, whether or not the
  result reused it) and its 8-byte `uint64buf`; the mutex `e.mu` guards nothing (the encoder is
  owned by its caller, the WAL, which holds it under its own lock).
* `encRecIn rp t d`: a fresh `*walpb.Record` at `rp` as the WAL builds one for `encode`
  (`&walpb.Record{Type: &t, Data: d}`): `Type` set (frozen), `Data` frozen, nil exactly when
  `recOf` says (a CRC record without data), no unknown fields; `Crc` anything (`encode` sets it).
  `encode` freezes it: afterwards it is `recRoC rp (recOf ⟨t, crc, d⟩)` (persistent).
* `encEnv`: the packages `encode` and `write` call initialized and the WAL's metrics
  (`wal.metricsInit`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.DecDefs
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Metrics
public import LinuxFs.Proof.go_etcd_io.etcd.pkg.v3.ioutil.Defs
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.walpb.PbRecord
public import LinuxFs.Proof.google_golang_org.protobuf.proto.PkgInit
public import Proof.go_etcd_io.etcd.server.v3.storage.WalPbWire

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI WalEnc

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- The size of the encoder's scratch buffer (`make([]byte, 1024*1024)`, encoder.go:52). -/
abbrev encBufBytes : Int := 1048576

/-- See the file header. -/
def ownEncoder (e : Loc) (wi : GoInterfaceOk) (c : w32) (pend : List w8) : IProp GF :=
  iprop(∃ (pw : Loc) (h : GoInterface) (b u : GoSlice) (bs us : List w8),
    sync.isMutex (structFieldRef go_etcd_io.etcd.server.v3.storage.wal.encoder go!"mu" e)
      (BI.pure True : IProp GF) ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.encoder go!"bw" e ↦ pw ∗
    ioutil.ownPageWriter pw wi pend ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.encoder go!"crc" e ↦ h ∗
    ownDecCrc h c ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.encoder go!"buf" e ↦ b ∗
    b ↦* bs ∗ ⌜sint.Z b.len = encBufBytes ∧ b.cap = b.len⌝ ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.encoder go!"uint64buf" e ↦ u ∗
    u ↦* us ∗ ⌜us.length = 8⌝)

/-- See the file header. -/
def encEnv : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗
    isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗
    isPkgInit (PROP := IProp GF) pkg_id.sync ∗
    isPkgInit (PROP := IProp GF) pkg_id.time ∗
    wal.metricsInit)

instance encEnv_persistent : Persistent (encEnv (GF := GF)) := by
  unfold encEnv; infer_instance

theorem sliceIndexRef_w8_zero (b : GoSlice) : sliceIndexRef w8 (sint.Z (W64 0)) b = b.ptr := by
  rw [show sint.Z (W64 0) = 0 by simp]
  exact go.arrayIndexRef_0 _ _

theorem slice_w8_zero_ptr (b : GoSlice) (h : w64) : (slice.slice b w8 (W64 0) h).ptr = b.ptr :=
  sliceIndexRef_w8_zero b

theorem w64_sub_W64_zero (x : w64) : x - W64 0 = x := by
  rw [show W64 0 = 0#64 by simp]; exact BitVec.sub_zero x

theorem slice_w8_zero_cap (b : GoSlice) (h : w64) : (slice.slice b w8 (W64 0) h).cap = b.cap :=
  w64_sub_W64_zero b.cap

/-- **The scratch buffer back**: a slice `s` in `b`'s array (same pointer, same capacity; `b` with
no slack), owned with its capacity, gives `b` back whole (`encode` after `MarshalAppend` and the
padding `append`). -/
theorem encBuf_back (s b : GoSlice) (xs : List w8) (hptr : s.ptr = b.ptr) (hcap : s.cap = b.cap)
    (hb : b.cap = b.len) (h : 0 ≤ sint.Z s.len ∧ sint.Z s.len ≤ sint.Z s.cap) :
    s ↦* xs ∗ ownSliceCap (GF := GF) w8 s (DFrac.own 1) ⊢ ∃ bs : List w8, b ↦* bs := by
  have hs : slice.slice s w8 (W64 0) s.cap = b := by
    rcases b with ⟨bp, bl, bc⟩
    rcases s with ⟨sp, sl, sc⟩
    simp only at hptr hcap hb
    subst hptr hcap hb
    simp only [slice.slice, sliceIndexRef_w8_zero, w64_sub_W64_zero]
  iintro ⟨Hs, Hc⟩
  icases ownSlice_slice_into_capacity (W64 0) s.cap s xs $$ [Hs Hc] with ⟨%vc, -, H, -⟩
  · iframe
    ipureintro
    have h0 : sint.Z (W64 0) = 0 := rfl
    rw [h0]
    exact ⟨Int.le_refl _, by have := h.1; have := h.2; omega, h.2, Int.le_refl _⟩
  rw [hs]
  iexists _
  iexact H

end defs

section recin
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
def encRecIn (rp : Loc) (t : w64) (d : List w8) : IProp GF :=
  iprop(∃ (v : go_etcd_io.etcd.server.v3.storage.wal.walpb.Record),
    rp ↦ v ∗ v.Type' ↦□ t ∗ recBytes v.Data' (recOf ⟨t, 0#32, d⟩).data ∗
    ⌜v.unknownFields' = slice.nil⌝)

/-- The data of a record built for `encode` holds `d` (a nil slice holds `[]`). -/
theorem recBytes_recOf (s : GoSlice) (t : w64) (k : w32) (d : List w8) :
    recBytes (GF := GF) s (recOf ⟨t, k, d⟩).data ⊢ s ↦*□ d := by
  unfold recOf
  by_cases hc : t = crcType ∧ d = []
  · simp only [hc, and_self, ite_true, recBytes]
    iintro %hs
    subst hs
    iapply ownSlice_nil
  · simp only [hc, ite_false, recBytes]
    iintro ⟨-, H⟩
    iexact H

end recin

end WalFs
end EtcdGrove
end Perennial
