/- Lean-first (no Rocq counterpart).

# `Create`'s update for the rename, over the fresh layout (W4, `notes/wal-fsext-plan.md`, "W4
implementation log", eighteenth session)

`walCreate_osAUnc` for the layout `Create` builds (`createLay`, the segment `createSeg`), its premises on
the layout and on `J`'s claim discharged by `createLay_abs`, `createSeg_facts` and `createJ_*`.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateAu
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateLay
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateJ
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreatePure

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Fs WalEnc

section au
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [W : WalGS GF]

/-- **`Create`'s update for the rename of `nm.tmp` onto `nm`**, over the fresh layout: the creating
claim `(jr, .only [nm, nm.tmp], hC)` holding `J` at `nm.tmp`; `J`'s claim off the pipeline's names
(`hJ'` merged after the segment's create, `createJ_claims`), coherent, its entries below the
program's commit bound `m`; the segment after its header
stream and fdatasync (`hok`, over the preallocated `m2`); the log bound `lb` past both claims. -/
theorem createFresh_osAUnc (Mr : WalMarshal) (R : Roots) (jr : Ino) (r nm : GoString)
    (md : List w8) (Q : IProp GF) (hC : NamesH) (J : Ino) (hJ' : NamesH) (i : Ino)
    (m2 mS : OsMeta) (zs2 : List Cands) (ysS : List ByteG) (lb : Nat)
    (hin : InArea r (child r nm) nm) (hnm : walNameOk nm) (hMr : WalMarshalCreateOk Mr)
    (hmd : md.length < 2 ^ 41)
    (hctmp : hC.cur !! tmpName nm = some (.dir J)) (hJjr : J ≠ jr)
    (hlb : hC.next ≤ lb) (hJlb : (hJ'.restrict J ((NameSet.except []).diff walTmps)).next ≤ lb)
    (hJcoh : ClaimCoh (hJ'.restrict J ((NameSet.except []).diff walTmps)) J (.except walTmps))
    (m : Nat) (hJm : ∀ xe ∈ (hJ'.restrict J ((NameSet.except []).diff walTmps)).ents, xe.1 < m)
    (hcur : ∀ b, hJ'.cur !! b = if b = walFileName 0 0 then some (.file i) else none)
    (hok : os.StreamOk m2 0 (zs2.map (fun c => ((0 : w8), c))) (createStream Mr md) mS ysS)
    (hm2s : m2.size = 64000000) (hm2c : m2.cut = none) :
    ⊢ walInv (W := W) walCodec Mr R jr r -∗ osCommitLb m -∗
      walCreateP (W := W) (child r nm) (.only [nm, tmpName nm]) hC md Q J walTmps
        (hJ'.restrict J ((NameSet.except []).diff walTmps)) (createSeg i mS ysS) -∗
      osAUnc (osNames jr (.only [nm, tmpName nm]) (DFrac.own (1 : Qp).half) hC)
        (renDirOut jr J (.only [nm, tmpName nm]) (tmpName nm) nm hC (DFrac.own (1 : Qp).half) lb)
        (walCreateQ (W := W) (child r nm) (.only [nm, tmpName nm]) hC md Q J walTmps
          (hJ'.restrict J ((NameSet.except []).diff walTmps)) (createSeg i mS ysS)
          (createTailG Mr md jr nm J (createSeg i mS ysS))) := by
  obtain ⟨⟨hbs1, hbs2⟩, hmeta, hzf, hne, hz, hdur⟩ :=
    createSeg_facts Mr md hMr i m2 mS zs2 ysS hok hm2s hm2c
  have hw : walNameP (createSeg i mS ysS).name = true := walNameP_walFileName 0 0
  have hcur' : ∀ b, hJ'.cur !! b =
      if b = (createSeg i mS ysS).name then some (.file (createSeg i mS ysS).ino) else none := hcur
  apply walCreate_osAUnc walCodec Mr R jr r (child r nm) nm (tmpName nm) md Q _ hC J walTmps _
    (createLay jr nm J (createSeg i mS ysS) (createStream Mr md).length) (createSeg i mS ysS) lb
    hin (tmpName_ne nm) (by simp [NameSet.Mem]) (by simp [NameSet.Mem]) hctmp
    (tmpName_not_walName nm) (tmpName_walNameP nm) (tmpName_areaSlot hnm) hJjr hlb hJlb
    ⟨rfl, rfl, rfl⟩ rfl hne hJcoh walTmps_not_wal rfl
    (createLay_abs Mr md hMr hmd jr nm J _ _ rfl ⟨hbs1, hbs2⟩ hmeta (createJ_walInos hw hcur'))
    hdur hzf rfl
  · intro b hb _
    simp only [createLay, List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl
  · intro b _ _
    simp only [createLay, List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl
  · simpa [createLay] using hz
  · exact createLay_tailBound Mr md jr nm J _
  · exact hmeta.2.1
  · exact ⟨hmeta.2.2.1, hmeta.2.2.2⟩
  · exact createJ_segsNamed rfl hcur'
  · exact createJ_segsNamedC hw hcur'
  · exact hJm
  · exact hmd

end au

end WalFs
end EtcdGrove
end Perennial
