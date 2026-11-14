/- Lean-first (no Rocq counterpart).

# Laws of the sealed handle (W6; the package's own proofs `import all` `Handle.lean`)

- `walOpenWF_iff`: the client handle is a quiescent internal handle with its cuts budget.
- `walHandleIn_lenLb`: a length lower bound of the open WAL is at most the handle's history
  (`walLenLb_tail_le` over the tail record the handle holds in `walTailW`); `Sync` needs it.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailLenLb
public import LinuxFs.Proof.go_etcd_io.etcd.pkg.v3.ioutil.Defs
import all LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section handle
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- **The client handle unsealed.** -/
theorem walOpenWF_iff (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) :
    walOpenWF (W := W) P Mr w dir ⊣⊢
      ∃ h : WalHS, walHandleIn (W := W) P Mr w dir h TailMetaW ∗ ⌜h.Done⌝ ∗ ⌜h.md.length < 2 ^ 41⌝ ∗
        ⧗ h.pc :=
  .rfl

/-- **A length lower bound is at most the handle's history** (at an update; see the file header). -/
theorem walHandleIn_lenLb (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (P : WalPbIn GF) (E : CoPset) (hE : ↑walN ⊆ E) (w : Loc) (dir : GoString) (h : WalHS) (n : Nat)
    (tm : OsMeta → List ByteG → Prop := TailMeta) :
    ⊢ walAreaOk C Mr R jr r -∗ notCrashed (hC := hG.goose_localGS.goose_crashGS) -∗
      walHandleIn (W := W) P Mr w dir h tm -∗ walLenLb (W := W) w dir n -∗
      |={E}=> notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗ walHandleIn (W := W) P Mr w dir h tm ∗
        ⌜n ≤ h.H.length⌝ := by
  letI := walAllG (W := W)
  iintro #Harea Hnc Hh #Hn
  unfold walAreaOk
  icases Harea with ⟨#Hinv, -⟩
  unfold walHandleIn
  icases Hh with ⟨%lg, %df, %sp, %e, %fp, %lt, %f, %mds, %locks, %lfs, %fd, %dfd, %name, %dnm, %j,
    %rc, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, H17, H18, Ht, Hrest⟩
  unfold walTailW
  icases Ht with ⟨Hf, Hfd, Hoff, Hk, %m, %bs, Hm, Hb, %hp, Hv⟩
  imod walLenLb_tail_le C Mr R jr r E hE w dir h.γ
    ((h.H, h.md, h.cuts, h.o0 + h.out.length, h.ino, none) : TailG) n $$ Hinv Hnc Hk [Hv] Hn
    with ⟨Hnc, Hk, Hv, %hn⟩
  · unfold tailVar; iexact Hv
  unfold tailVar
  imodintro
  iframe Hnc
  isplitl
  · iexists lg, df, sp, e, fp, lt, f, mds, locks, lfs, fd, dfd, name, dnm, j, rc
    iframe H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 Hrest
    iframe Hf Hfd Hoff Hk
    iexists m, bs
    iframe Hm Hb Hv
    ipureintro; exact hp
  · ipureintro; exact hn

/-- **The tail's state with a weaker meta form** (`TailMeta` gives `TailMetaW`, `TailMeta.win`). -/
theorem walTailW_mono (f : Loc) (fd : w64) (name dir : GoString) (γ : GName) (i : Ino)
    (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (o0 sz : Nat) (out : List w8)
    (tm tm' : OsMeta → List ByteG → Prop) (htm : ∀ m bs, tm m bs → tm' m bs) :
    walTailW (W := W) f fd name dir γ i H md cuts o0 sz out tm ⊢
      walTailW (W := W) f fd name dir γ i H md cuts o0 sz out tm' := by
  unfold walTailW
  iintro ⟨Hf, Hfd, Hoff, Hk, %m, %bs, Hm, Hb, %hp, Hv⟩
  iframe Hf Hfd Hoff Hk
  iexists m, bs
  iframe Hm Hb Hv
  ipureintro; exact ⟨hp.1, htm _ _ hp.2.1, hp.2.2⟩

/-- **The handle with a weaker meta form.** -/
theorem walHandleIn_mono (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) (h : WalHS)
    (tm tm' : OsMeta → List ByteG → Prop) (htm : ∀ m bs, tm m bs → tm' m bs) :
    walHandleIn (W := W) P Mr w dir h tm ⊢ walHandleIn (W := W) P Mr w dir h tm' := by
  unfold walHandleIn
  iintro ⟨%lg, %df, %sp, %e, %fp, %lt, %f, %mds, %locks, %lfs, %fd, %dfd, %name, %dnm, %j,
    %rc, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, H17, H18, Ht, Hrest⟩
  iexists lg, df, sp, e, fp, lt, f, mds, locks, lfs, fd, dfd, name, dnm, j, rc
  iframe H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 Hrest
  iapply (walTailW_mono f fd name dir h.γ h.ino h.H h.md h.cuts h.o0 h.sz h.out tm tm' htm)
  iexact Ht

/-- `TailMeta`'s handle is a `TailMetaW` one. -/
theorem walHandleIn_win (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) (h : WalHS) :
    walHandleIn (W := W) P Mr w dir h ⊢ walHandleIn (W := W) P Mr w dir h TailMetaW :=
  walHandleIn_mono P Mr w dir h TailMeta TailMetaW (fun _ _ hm => hm.win)

/-- **The page writer's pending bytes are at most its buffer** (`2 ^ 18`: `wmBytes + pageBytes`, the
page size at most the watermark). -/
theorem ioutil_ownPageWriter_pend (pw : Loc) (wi : GoInterfaceOk) (pend : List w8) :
    ioutil.ownPageWriter (GF := GF) pw wi pend ⊢ ioutil.ownPageWriter pw wi pend ∗ ⌜pend.length ≤ 2 ^ 18⌝ := by
  unfold ioutil.ownPageWriter
  iintro ⟨%v, %bs, Hp, Hb, %hv⟩
  isplitl
  · iexists v, bs; iframe Hp Hb; ipureintro; exact hv
  ipureintro
  obtain ⟨-, -, hok, hpe⟩ := hv
  obtain ⟨h1, h2, -, -, -, -, -, h8⟩ := hok
  rw [hpe, List.length_take]
  unfold ioutil.wmBytes at h2 h8
  omega

/-- **The handle's pure facts**: the stream split, the pending bytes at most the page writer's buffer. -/
theorem walHandleIn_pure (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) (h : WalHS)
    (tm : OsMeta → List ByteG → Prop) :
    walHandleIn (W := W) P Mr w dir h tm ⊢ walHandleIn (W := W) P Mr w dir h tm ∗
      ⌜h.Split Mr ∧ h.pend.length ≤ 2 ^ 18 ∧ h.o0 + h.out.length ≤ h.sz ∧ h.sz ≤ 0xffffffff000⌝ := by
  unfold walHandleIn
  iintro ⟨%lg, %df, %sp, %e, %fp, %lt, %f, %mds, %locks, %lfs, %fd, %dfd, %name, %dnm, %j,
    %rc, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, H17, H18, Ht, Hrest⟩
  unfold ownEncoder
  icases H18 with ⟨%pw, %hh, %b, %u, %bs, %us, E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11⟩
  icases ioutil_ownPageWriter_pend pw _ h.pend $$ E3 with ⟨E3, %hpe⟩
  icases Hrest with ⟨R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11, R12, Hw, %hp⟩
  isplitl
  · iexists lg, df, sp, e, fp, lt, f, mds, locks, lfs, fd, dfd, name, dnm, j, rc
    iframe H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 Ht
    isplitl [E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11]
    · iexists pw, hh, b, u, bs, us; iframe
    iframe R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 Hw; ipureintro; exact hp
  ipureintro
  exact ⟨hp.1, hpe, hp.2.2.1, hp.2.2.2.1⟩

end handle

end WalFs
end EtcdGrove
end Perennial
