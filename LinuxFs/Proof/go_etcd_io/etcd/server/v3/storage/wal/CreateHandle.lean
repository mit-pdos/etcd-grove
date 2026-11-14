/- Lean-first (no Rocq counterpart).

# `Create`'s handle before naming (W4, `notes/wal-fsext-plan.md`, "W4 implementation log", twenty-third
session)

`Create`'s arm 1 (`renameWAL` returned `w` with the pipeline and the directory open) builds the handle
before naming (`walOpenWFU`, `HandleUnnamed.lean`) from `renameWALPost`'s first arm:

* `createHS`: the handle's state, the fresh WAL (no history, no cuts, every header record encoded, the
  encoder at the stream's end, `w.state` nil read as the zero state, the indices 0).
* the pure facts: `createSeg_tailMeta` (the synced segment's `TailMeta`, over the preallocation's
  `ZeroPg`, `metaChain_zeroPg`), `createHS_split`, `createHS_crc` (the encoder's CRC the chain's after
  the header records).
* `walInv_mintAppend`: the ghost handle minted from the lock token, in append mode.
* `create_ghost`: the ghost steps at the arm's start (the name registered, `walInv_register`; the handle
  minted), from `createU (some x)` and `createSpR`, leaving `createUH x`.
* `create_handleIn`: the handle assembled (`walHandleIn` with `nmd := emp`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateRename
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleUnnamed
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleAlloc
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__renameWAL

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- **The fresh WAL's handle state**: tail inode `i`, record `γ`, size `sz`, the encoder at the stream's
end `L` with nothing out or pending. -/
def createHS (md : List w8) (i : Ino) (L : Nat) (γ : GName) (sz : Nat) : WalHS :=
  ⟨[], md, [], i, L, [], [], 0, hsZero, γ, sz, W64 0, W64 0, 0⟩

theorem createHS_done (md : List w8) (i : Ino) (L : Nat) (γ : GName) (sz : Nat) :
    (createHS md i L γ sz).Done := ⟨rfl, rfl⟩

/-- The handle's tail stream is the fresh WAL's. -/
theorem tailStream_fresh (Mr : WalMarshal) (md : List w8) :
    recFrames walCodec (tailRecs Mr [] md []) = createStream Mr md := rfl

theorem createHS_split (Mr : WalMarshal) (md : List w8) (i : Ino) (γ : GName) (sz : Nat) :
    (createHS md i (createStream Mr md).length γ sz).Split Mr := by
  unfold WalHS.Split WalHS.encRecs createHS
  simp only [Nat.sub_zero, List.take_length, List.append_nil, tailStream_fresh]
  exact ⟨trivial, Nat.le_refl _, Nat.zero_le _⟩

/-- The encoder's CRC after the header records. -/
theorem createHS_crc (Mr : WalMarshal) (md : List w8) (hMr : WalMarshalCreateOk Mr) (i : Ino) (L : Nat)
    (γ : GName) (sz : Nat) :
    (createHS md i L γ sz).crc Mr = hash.crc32.crc32c (hash.crc32.crc32c (hash.crc32.crc32c 0#32 []) md)
      (Mr.encSnap snapC0.model) := by
  unfold WalHS.crc createHS allRecs
  simp only [Nat.sub_zero, List.take_length]
  have e := create_recsOfSegs Mr md
  simp only [walDurFresh, histM, List.map_nil] at e
  simp only [List.map_nil]
  rw [e, chainEnd_chainRecs, hMr.2]
  rfl

/-- **The synced segment's `TailMeta`** (`walTailW`'s): all its bytes, no mappings, the zeros past its
size (the preallocation's `ZeroPg`, kept by the header writes, `metaChain_zeroPg`, then the sync), exact. -/
theorem createSeg_tailMeta (Mr : WalMarshal) (md : List w8) (hMr : WalMarshalCreateOk Mr) (i : Ino)
    (m2 mS : OsMeta) (zs2 : List Cands) (ysS : List ByteG)
    (hok : os.StreamOk m2 0 (zs2.map (fun c => ((0 : w8), c))) (createStream Mr md) mS ysS)
    (hm2s : m2.size = 64000000) (hm2c : m2.cut = none) (hmaps : m2.maps = ∅) (hzp : ZeroPg m2) :
    TailMeta (createSeg i mS ysS).om (createSeg i mS ysS).bs := by
  obtain ⟨-, hmeta, -⟩ := createSeg_facts Mr md hMr i m2 mS zs2 ysS hok hm2s hm2c
  have hzS : ZeroPg mS := metaChain_zeroPg hok.2.1 (Nat.zero_le _) hzp
  refine ⟨hmeta.1.symm, ?_, ?_, ?_, ?_, ?_⟩
  · show mS.synced.maps = ∅
    simp only [OsMeta.synced]; rw [hok.2.2.2.1, hmaps]
  · exact TailZ.synced_of hzS.pageEnd_size
  · rw [hmeta.2.2.1, hmeta.1]
  · rw [hmeta.2.2.2, hmeta.1]
  · exact PastZ.synced mS

/-- The synced segment's size: the preallocated 64 MB, or the stream if longer. -/
theorem createSeg_size (Mr : WalMarshal) (md : List w8) (hMr : WalMarshalCreateOk Mr) (hmd : md.length < 2 ^ 41)
    (i : Ino) (m2 mS : OsMeta) (zs2 : List Cands) (ysS : List ByteG)
    (hok : os.StreamOk m2 0 (zs2.map (fun c => ((0 : w8), c))) (createStream Mr md) mS ysS)
    (hm2s : m2.size = 64000000) :
    (createStream Mr md).length ≤ (createSeg i mS ysS).om.size ∧
      (createSeg i mS ysS).om.size ≤ 0xffffffff000 := by
  have hsz : mS.size = max 64000000 (createStream Mr md).length := by
    rw [metaChain_size hok.2.1 (by omega), hm2s]; simp
  have hfit := createStream_fit Mr md hMr hmd
  show (createStream Mr md).length ≤ mS.synced.size ∧ mS.synced.size ≤ 0xffffffff000
  simp only [OsMeta.synced, hsz]
  omega

end pure

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [W : WalGS GF]

/-- The ghost handle minted from the lock token, in append mode, on the invariant's contents. -/
theorem walInvBody_mintAppend (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (w : Loc) (dir : GoString) :
    ⊢ walInvBody (W := W) C Mr R jr r s -∗ walLockedTok (W := W) ==∗
      walInvBody (W := W) C Mr R jr r s ∗ walHandleP (W := W) w dir .append := by
  iintro Hb Hl
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, Hrest⟩
  icases (walGhost_handleAuth (W := W) s).1 $$ Hg with ⟨Ha, Hg⟩
  imod walHandleP_mint (W := W) w dir .append $$ Ha Hl with ⟨Ha, Ho⟩
  ihave Hg := Hg $$ Ha
  imodintro
  iframe Ho
  iexists Ls, cl, n, F
  iframe

/-- **The append-mode ghost handle minted** (`Create`'s). -/
theorem walInv_mintAppend (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (w : Loc) (dir : GoString) :
    ⊢ walInv (W := W) C Mr R jr r -∗ notCrashed (hC := hG.goose_localGS.goose_crashGS) -∗
      walLockedTok (W := W) ={⊤}=∗ notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗
        walHandleP (W := W) w dir .append := by
  iintro #Hinv Hnc Hl
  iapply walInv_step C Mr R jr r (walLockedTok (W := W)) (walHandleP (W := W) w dir .append) ⊤
    CoPset.subseteq_top (fun s => by
      iintro Hb Hl
      imod walInvBody_mintAppend C Mr R jr r s w dir $$ Hb Hl with ⟨Hb, Ho⟩
      imodintro
      iframe)
    $$ Hinv Hnc Hl

/-- **The ghost steps of `Create`'s arm 1** (see the file header): the new WAL's name registered with half
of `createSpR`'s claim fraction (`walInv_register`), the append-mode handle minted from the lock token;
`createUH x` the residue. -/
theorem create_ghost (Mr : WalMarshal) (R : Roots) (jr : Ino) (r nm : GoString) (hC : NamesH)
    (md : List w8) (Q : IProp GF) (J : Ino) (hJ : NamesH) (g : SegG) (Wn : List GoString) (c : Qp)
    (x : Nat × Nat) (w : Loc) (hin : InArea r (child r nm) nm) (hnmO : NameOk nm) :
    ⊢ osSharedInv (L := hG.goose_localGS) R -∗ notCrashed (hC := hG.goose_localGS.goose_crashGS) -∗
      createU (W := W) Mr R jr r nm hC md Q J hJ g (some x) -∗
      createSpR (hG := hG) jr J nm c x -∗ walSplitFrag (W := W) Wn ={⊤}=∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗ createUH (W := W) jr J r nm md Q Wn x ∗
      walInv (W := W) walCodec Mr R jr r ∗ walHandleP (W := W) w (child r nm) .append ∗
      osMeta g.ino (DFrac.own (1 : Qp).half) g.om ∗ osBytes g.ino 0 (DFrac.own (1 : Qp).half) g.bs ∗
      walOutFrag (W := W) (WalOut.empty.create g.ino J walTmps (child r nm)) ∗
      walTailReg (W := W) (child r nm) (createTailG Mr md jr nm J g) ∗ walNamesFrag (W := W) none ∗
      walDirKey (W := W) (child r nm) J walTmps := by
  iintro #Hsi Hnc HU HSpR Hsf
  unfold createU
  icases HU with ⟨#Hinv, -, HQ⟩
  simp only [walCreateQ]
  icases HQ with ⟨HQ, Hm, Hb, Hlt, Ho, Htr, Hnf, #Hk, %s', #Hpast, %hs'⟩
  unfold createSpR
  icases HSpR with ⟨%hn, %ht, Hnm, Htmp, %hnt, %hlw, #Hlog⟩
  icases (osNames_frac jr (.only [nm]) c.half c.half hn).1 $$ [Hnm] with ⟨Hn1, Hn2⟩
  · rw [Qp.half_add_half]; iexact Hnm
  imod walInv_register walCodec Mr R jr r s' (child r nm) nm Wn c.half hn hin hnmO
    (by rw [hs']; simp) $$ Hinv Hsi Hnc Hpast Hnf Hsf Hn1 with ⟨Hnc, Hnf, Hsf⟩
  imod walInv_mintAppend walCodec Mr R jr r w (child r nm) $$ Hinv Hnc Hlt with ⟨Hnc, Hh⟩
  imodintro
  iframe Hnc Hinv Hh Hm Hb Ho Htr Hnf Hk
  unfold createUH
  iframe HQ Hsf Hlog
  isplitl []
  · iexists s'; iframe Hpast; ipureintro; exact hs'
  isplitl [Hn2]
  · iexists c.half, hn; iframe Hn2; ipureintro; exact ⟨hnt.1, hlw⟩
  · iexists ht; iframe Htmp; ipureintro; exact hnt.2

end ghost

section handle
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- **The handle before naming assembled** (`Create`'s arm 1; see the file header): `w`'s fields
(`walPreIn` with the indices 0, the directory open in `w.dirFile`, `w.state`/`decoder` nil, the pipeline in
`w.fp`), the encoder at the header records' CRC, the tail file (fd `fd` of inode `i`, writable, its offset
at the stream's end `L`) with the registration's key and record and the program's halves of the synced
segment, the directory share (key, `J`'s half claim holding only the segment's name, a path, half the
permission, the record of what is out, the tails' and names' halves). -/
theorem create_handleIn (P : WalPbIn GF) (Mr : WalMarshal) (hMr : WalMarshalCreateOk Mr)
    (w lg : Loc) (r nm : GoString) (mds : GoSlice) (md : List w8) (e lt f : Loc) (fd : w64)
    (fname pd : GoString) (d : OsFd) (off : w64) (g : SegG)
    (jr J : Ino) (hj : NamesH) (R : Roots) (q : Qp) (dfd : w64) (df : Loc) (dnm : GoString)
    (sp : Loc) (rc : GoFunc) (fp : Loc) (γp : PipeNames) (Rp : Roots) (dqp : DFrac) (szp : w64)
    (hdi : d.ino = g.ino) (hdw : d.writable = true)
    (hoff : off = W64 (((createStream Mr md).length : Nat) : Int)) (hmds : mds ≠ slice.nil)
    (hname : fname = child pd (walFileName 0 0)) (htm : TailMeta g.om g.bs)
    (hL : (createStream Mr md).length ≤ g.om.size) (hsz : g.om.size ≤ 0xffffffff000)
    (hj0 : hj.cur !! walFileName 0 0 = some (.file g.ino))
    (hj1 : ∀ b n, hj.cur !! b = some n → b = walFileName 0 0) (hfp : fp ≠ null) (hfd0 : 0 ≤ fd.toInt) :
    walPreIn w lg (child r nm) mds md e lt f (W64 0) (W64 0) ∗
      ownEncoder e (wal.fileWi f) (hash.crc32.crc32c (hash.crc32.crc32c (hash.crc32.crc32c 0#32 []) md)
        (Mr.encSnap snapC0.model)) [] ∗
      os.ownFile f fd fname (DFrac.own 1) ∗ osFd fd (DFrac.own 1) d ∗ os.ownOff f off ∗
      walTailReg (W := W) (child r nm) (createTailG Mr md jr nm J g) ∗
      osMeta g.ino (DFrac.own (1 : Qp).half) g.om ∗ osBytes g.ino 0 (DFrac.own (1 : Qp).half) g.bs ∗
      walDirKey (W := W) (child r nm) J walTmps ∗
      osNames J (.except walTmps) (DFrac.own (1 : Qp).half) hj ∗
      osPathS R (child r nm) (DFrac.own q) J ∗ osSharedInv R ∗ osCallPerm (1 : Qp).half ∗
      osDirFdS dfd J .idle ∗
      walOutFrag (W := W) (WalOut.empty.create g.ino J walTmps (child r nm)) ∗ walNamesFrag (W := W) none ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dirFile" w ↦ df ∗
      os.ownFile df dfd dnm (DFrac.own 1) ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"state" w ↦ sp ∗ P.hsIn sp hsZero ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"decoder" w ↦ (null : Loc) ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"readClose" w ↦ rc ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"fp" w ↦ fp ∗
      isFilePipe fp γp Rp (child r nm) dqp J szp ∗ pipeMain γp 0 ∗ tmpClaim J (pipeTmp 1) ∗
      encEnv ∗ walCrcTable ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗
      walOpenW (W := W) w (child r nm) ⊢
    ∃ γ, walHandleIn (W := W) P Mr w (child r nm)
      (createHS md g.ino (createStream Mr md).length γ g.om.size) TailMetaW emp := by
  iintro ⟨Hpre, Henc, Hf, Hfd, Hoff, Htr, Hm, Hb, #Hk, Hn, Hp, #Hsi, Hperm, Hdfd, Ho, Hnf, Hdff, Hdf,
    Hst, #Hsp, Hdec, Hrc, Hfpf, #Hpipe, Hmain, Htc, #Henv, #Hcrc, #Hpkg, Hopen⟩
  iunfold walPreIn at Hpre
  icases Hpre with ⟨%locks, Hlg, #Hzap, Hdir, Hmd, #Hmds, Hns, #Hmu, Henti, Hsnapi, He, %hen, Hlocks, Hls,
    Hcap, #Hlt⟩
  unfold walTailReg
  icases Htr with ⟨%γ, Htf, Htk, Hv⟩
  subst hoff
  iexists γ
  unfold walHandleIn
  iexists lg, df, sp, e, fp, lt, f, mds, locks, [lt], fd, dfd, fname, dnm, J, rc
  rw [createHS_crc Mr md hMr g.ino (createStream Mr md).length γ g.om.size]
  dsimp only [createHS]
  iframe Hlg Hzap Hdir Hdff Hdf Hmd Hst Hsp Hdec Hrc Hns Hmu Henti Hsnapi He Henc Hlocks Hls Hcap Hlt Hfpf
    Henv Hcrc Hpkg Hopen
  isplitr
  · simp only [recBytes]; iframe Hmds; ipureintro; exact hmds
  isplitr
  · ipureintro; exact hen
  isplitl [Hf Hfd Hoff Htk Hm Hb Hv]
  · unfold walTailW
    iframe Hf Htk
    isplitl [Hfd]
    · iexists d.readable
      rw [show (⟨g.ino, d.readable, true⟩ : OsFd) = d by cases d; simp_all]
      iexact Hfd
    isplitl [Hoff]
    · rw [show (((createStream Mr md).length : Int) + (([] : List w8).length : Int)) =
          ((createStream Mr md).length : Int) by simp]
      iexact Hoff
    iexists g.om, g.bs
    iframe Hm Hb
    isplitr
    · ipureintro
      refine ⟨rfl, htm.win, by omega, hfd0, htm.loWr _⟩
    rw [show ((([] : List (WalOpG WalEnt)), md, ([] : List Nat),
        (createStream Mr md).length + ([] : List w8).length, g.ino, (none : Option SegFl)) : TailG) =
        createTailG Mr md jr nm J g from rfl]
    iexact Hv
  isplitl [Hn Hp Hperm Hdfd Ho Htf Hnf]
  · unfold walDirH
    iexists R, q, walTmps, hj, walFileName 0 0, .idle
    rw [show (⟨[g.ino], [(J, .except walTmps)], [child r nm]⟩ : WalOut) =
      WalOut.empty.create g.ino J walTmps (child r nm) from rfl]
    iframe Hk Hn Hp Hsi Hperm Hdfd Ho Hnf Htf
    ipureintro
    exact ⟨walNameP_walFileName 0 0, hj0, ⟨pd, hname⟩, fun _ h => h, walTmps_not_wal,
      ⟨0, 0, rfl, by decide⟩, fun b n hb _ => Or.inl (hj1 b n hb)⟩
  isplitr
  · ipureintro; rfl
  isplitr
  · simp only [List.dropLast_singleton]
    iapply BigSepL.bigSepL_nil.2
    iempintro
  isplitl [Hpipe Hmain Htc]
  · unfold walPipeH
    iexists γp, Rp, dqp, szp, 0
    iframe Hpipe Hmain Htc
    ipureintro; exact ⟨Nat.le_refl _, hfp⟩
  ipureintro
  refine ⟨createHS_split Mr md g.ino γ g.om.size, hfd0, by simpa using hL, hsz, ⟨fun _ => ?_, ?_⟩, ?_⟩
  · simp [walLastIdx]
  · simp [walMaxSnapIdx]
  · simp

end handle

end WalFs
end EtcdGrove
end Perennial

end
