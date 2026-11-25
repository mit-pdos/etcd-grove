/- Lean-first (no Rocq counterpart).

# The handle with room before `maxBytes` (unit `noioerr`, `notes/wal-units/noioerr.md`)

`walOpenWFR P Mr w dir k` (sealed): `walOpenWF` whose tail's stream, written and pending
(`o0 + |out| + |pend|`), ends at least `k` bytes before `maxBytes` (ext4's `s_maxbytes`, `fsExt`'s file size
bound). The no-error specs (`Close.spec`, `Save.spec`, `SaveSnapshot.spec`, through `walHdl`) take it: a write that reaches
`maxBytes` fails with `EFBIG` whether or not `NoIoErr` holds (no write can succeed there), so an error-free
flush needs the stream to end before it. How a client comes by it (a law from `Create`'s post, the fresh
tail's headers being far below `maxBytes`; from `Save`'s cut; or a public measure of the tail) is open:
`notes/wal-units/noioerr.md`, second session, "Decisions left for the user". `walOpenWFR_wf`: it is a
`walOpenWF`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleLaws
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.StreamBound
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateHdr

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- **The room of a fresh tail** (`Create`'s segment, a cut's): its header records (`crc`, metadata
below `2 ^ 41` bytes, the state or the empty snapshot) end below `2 ^ 43`, so at least
`maxBytes - 2 ^ 43` bytes (about 8 TB) are left before ext4's `s_maxbytes`. -/
def walFreshRoom : Nat := maxBytes - 2 ^ 43

/-- A cut's headers end below `2 ^ 43`. -/
theorem cutHdrs_room (Mr : WalMarshal) (md : List w8) (hs : HardStateM) (c : w32)
    (hsz : md.length + (Mr.encState hs).length < 2 ^ 42) :
    (recFrames walCodec (chainRecs walCodec c (cutHdrDs Mr md hs))).length ≤ 2 ^ 43 := by
  rw [cutHdrRecs_frames]
  have h1 := frame_walRecEnc_tight crcType (hash.crc32.crc32c c []) [] (by decide) (by simp)
  have h2 := frame_walRecEnc_tight metadataType (hash.crc32.crc32c (hash.crc32.crc32c c []) md) md
    (by decide) (by omega)
  have h3 := frame_walRecEnc_tight stateType (hash.crc32.crc32c (hash.crc32.crc32c
    (hash.crc32.crc32c c []) md) (Mr.encState hs)) (Mr.encState hs) (by decide) (by omega)
  simp only [List.length_nil] at h1
  split <;> simp only [List.length_append, List.length_nil] <;> omega

/-- `Create`'s headers end below `2 ^ 43`. -/
theorem createStream_room (Mr : WalMarshal) (md : List w8) (hMr : WalMarshalCreateOk Mr)
    (hmd : md.length < 2 ^ 41) : (createStream Mr md).length ≤ 2 ^ 43 := by
  rw [createStream_frames Mr md hMr]
  unfold snapFrame
  have h1 := frame_walRecEnc_tight crcType (hash.crc32.crc32c 0#32 []) [] (by decide) (by simp)
  have h2 := frame_walRecEnc_tight metadataType (hash.crc32.crc32c (hash.crc32.crc32c 0#32 []) md) md
    (by decide) (by omega)
  have h3 := frame_walRecEnc_tight snapshotType (hash.crc32.crc32c (hash.crc32.crc32c
    (hash.crc32.crc32c 0#32 []) md) (Mr.encSnap snapC0.model true)) (Mr.encSnap snapC0.model true) (by decide)
    (by
      have h4 : (Mr.encSnap snapC0.model true).length < 2 ^ 8 := by
        rw [hMr.2, hMr.1]; simp [snapC0, snapEnc, optVarintField, optBytesField, varintEnc]
      omega)
  have h4 : (Mr.encSnap snapC0.model true).length < 2 ^ 8 := by
    rw [hMr.2, hMr.1]; simp [snapC0, snapEnc, optVarintField, optBytesField, varintEnc]
  simp only [List.length_nil, List.length_append] at h1 ⊢
  omega

end pure

section handle
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- See the file header. -/
@[no_expose] def walOpenWFR (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) (k : Nat)
    (i : Nat) : IProp GF :=
  iprop(∃ h : WalHS, walHandleIn (W := W) P Mr w dir h TailMetaW ∗ ⌜h.Done⌝ ∗ ⌜h.md.length < 2 ^ 41⌝ ∗
    ⧗ h.pc ∗ ⌜h.o0 + h.out.length + h.pend.length + k ≤ maxBytes⌝ ∗ ⌜h.inc = i⌝)

/-- The room handle unfolded (for the package's proofs). -/
theorem walOpenWFR_iff (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) (k : Nat)
    (i : Nat) :
    walOpenWFR (W := W) P Mr w dir k i ⊣⊢
      ∃ h : WalHS, walHandleIn (W := W) P Mr w dir h TailMetaW ∗ ⌜h.Done⌝ ∗ ⌜h.md.length < 2 ^ 41⌝ ∗
        ⧗ h.pc ∗ ⌜h.o0 + h.out.length + h.pend.length + k ≤ maxBytes⌝ ∗ ⌜h.inc = i⌝ :=
  .rfl

/-- **A handle with room is a handle.** -/
theorem walOpenWFR_wf (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) (k : Nat)
    (i : Nat) :
    walOpenWFR (W := W) P Mr w dir k i ⊢ walOpenWFI P Mr w dir i := by
  refine (walOpenWFR_iff P Mr w dir k i).1.trans ?_
  refine BI.Entails.trans ?_ (walOpenWFI_iff P Mr w dir i).2
  iintro ⟨%h, Hh, %hD, %hmd, Hr, -, %hi⟩
  iexists h
  iframe Hh Hr
  ipureintro; exact ⟨hD, hmd, hi⟩

/-- **A handle whose tail's stream ends below `2 ^ 43` has the fresh room** (`Create`'s, a cut's). -/
theorem walOpenWFR_fresh (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) (h : WalHS)
    (hD : h.Done) (hmd : h.md.length < 2 ^ 41) (hb : h.o0 + h.out.length + h.pend.length ≤ 2 ^ 43) :
    walHandleIn (W := W) P Mr w dir h TailMetaW ∗ ⧗ h.pc ⊢ walOpenWFR P Mr w dir walFreshRoom h.inc := by
  refine BI.Entails.trans ?_ (walOpenWFR_iff P Mr w dir walFreshRoom h.inc).2
  iintro ⟨Hh, Hr⟩
  iexists h
  iframe Hh Hr
  ipureintro
  refine ⟨hD, hmd, ?_, rfl⟩
  unfold walFreshRoom
  have : (2 : Nat) ^ 43 ≤ maxBytes := by decide
  omega

/-- **Less room**: a handle with room `k` has room `k' ≤ k`. -/
theorem walOpenWFR_mono (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) (k k' : Nat)
    (i : Nat) (hk : k' ≤ k) : walOpenWFR (W := W) P Mr w dir k i ⊢ walOpenWFR P Mr w dir k' i := by
  refine (walOpenWFR_iff P Mr w dir k i).1.trans ?_
  refine BI.Entails.trans ?_ (walOpenWFR_iff P Mr w dir k' i).2
  iintro ⟨%h, Hh, %hD, %hmd, Hr, %hb, %hi⟩
  iexists h
  iframe Hh Hr
  ipureintro
  exact ⟨hD, hmd, by omega, hi⟩

end handle

end WalFs
end EtcdGrove
end Perennial

end
