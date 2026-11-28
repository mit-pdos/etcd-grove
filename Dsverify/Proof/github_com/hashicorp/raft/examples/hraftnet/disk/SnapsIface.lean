/-
(hraft_robust R3) `*Snaps` as raft's snapshot store (`isSnapStore`, `iface/Stores.lean`), from the methods' specs
(hypotheses), as `examples/snapstore`'s `New`: its view `snapsOwn g`, its close obligation `Qc` that of
`snapsInv`, which must show the configuration's servers (`Close` encodes them; raft's `snapWin` does, through
`latestOk`'s `cfgVal`).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Snaps__Create
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Snaps__List
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Snaps__Open
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Sink__Write
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Sink__Close
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Sink__Cancel
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Sink__ID

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section sec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]
variable [dur_sem : github_com.mit_pdos.etcd_grove.examples.lib.durable.Assumptions]

open github_com.hashicorp.raft proto github_com.hashicorp.raft.examples.hraftnet.disk EtcdGrove

set_option goose.wp.extras true

/-- An open sink's bytes are a Go slice's: shorter than `2^63`. -/
theorem dk_sinkSt_len (k : Loc) (bs : List w8) :
    sinkSt (GF := GF) k (some bs) ⊢ ⌜bs.length < 2 ^ 63⌝ ∗ sinkSt k (some bs) := by
  simp only [sinkSt]
  iintro ⟨%dsl, Hd, Hsl, Hcap, Hc, Hsz⟩
  ihave %Hl := ownSlice_len $$ Hsl
  isplitr
  · ipureintro
    obtain ⟨h1, h2⟩ := Hl
    rw [h1]; word
  · iexists dsl; iframe

/-- **The sink of `Create` meets `isSink`**, with the commit the client fixed (holding its `Qx`) and the close
obligation `Qc ∗ Qx`. -/
theorem snaps_sink_isSink
    (wp_Write : github_com.hashicorp.raft.examples.hraftnet.disk.Sink.Write.spec (GF := GF) (hG := hG))
    (wp_Close : github_com.hashicorp.raft.examples.hraftnet.disk.Sink.Close.spec (GF := GF) (hG := hG))
    (wp_Cancel : github_com.hashicorp.raft.examples.hraftnet.disk.Sink.Cancel.spec (GF := GF) (hG := hG))
    (wp_ID : github_com.hashicorp.raft.examples.hraftnet.disk.Sink.ID.spec (GF := GF) (hG := hG))
    (k s : Loc) (g : SnapGen) (Qc : SnapshotMeta → List w8 → IProp GF) (Wf : IProp GF) (id : GoString)
    (ver idx term cfgIdx : w64) (cfg : Configuration) (Qx R : List w8 → IProp GF)
    (hQc : ∀ m b, Qc m b ⊢ (∃ svs : List Server, m.Configuration'.Servers' ↦*□ svs) ∗ Qc m b) :
    sinkCore k s g Qc Wf id ver idx term cfgIdx cfg ⊢
      isSink ⟨go.GoType.PointerType Sink.ty, #k⟩ id
        (sinkOwn k iprop(∀ bs : List w8, ⌜bs.length < 2 ^ 63⌝ -∗
          Qc (sinkMeta ver idx term cfgIdx cfg id bs) bs -∗ Qx bs -∗
          snapCommitAU g (sinkMeta ver idx term cfgIdx cfg id bs) bs (R bs)))
        (fun bs => iprop(Qc (sinkMeta ver idx term cfgIdx cfg id bs) bs ∗ Qx bs)) R := by
  iintro #Hcore
  ihave #Hcore2 := Hcore
  iunfold sinkCore at Hcore2
  icases Hcore2 with ⟨#Hst, #Hsn, -⟩
  iunfold isSnaps at Hsn
  icases Hsn with ⟨%mu, #Hpkg, -⟩
  unfold isSink
  simp only [sinkOwn]
  isplitr
  · ipureintro; go_type_set
  isplitr
  · imodintro
    iintro %p %dq %bs %c %Φ ⟨Hst, Hcm⟩ Hp HΦ
    iapply wp_Write k p dq bs c $$ [$Hpkg $Hst $Hp]
    inext; iintro ⟨Hst, Hp⟩
    iapply HΦ $$ [Hst Hcm] Hp
    iframe
  isplitr
  · imodintro
    iintro %bs %Φ ⟨Hst, Hcm⟩ ⟨HQc, HQx⟩ HΦ
    icases dk_sinkSt_len k bs $$ Hst with ⟨%Hlen, Hst⟩
    iapply wp_Close k s g Qc Wf id ver idx term cfgIdx cfg (some bs) (R bs) hQc $$ [$Hcore $Hst Hcm HQc HQx]
    · dsimp only
      iframe HQc
      iintro HQc
      iapply Hcm $$ %bs %Hlen HQc HQx
    inext; iintro ⟨Hst, HR⟩
    iapply HΦ $$ Hst HR
  isplitr
  · imodintro
    iintro %Φ Hst HΦ
    iapply wp_Close k s g Qc Wf id ver idx term cfgIdx cfg none iprop(True) hQc $$ [$Hcore $Hst]
    inext; iintro ⟨Hst, -⟩
    iapply HΦ $$ Hst
  isplitr
  · imodintro
    iintro %o %Φ Hst HΦ
    ihave Hst' : sinkSt k o $$ [Hst]
    · cases o with
      | none => iexact Hst
      | some bs => icases Hst with ⟨Hst, -⟩; iexact Hst
    iapply wp_Cancel k o $$ [$Hpkg $Hst']
    inext; iintro Hst
    iapply HΦ $$ Hst
  · imodintro
    iintro %Φ HΦ
    iapply wp_ID k s g Qc Wf id ver idx term cfgIdx cfg $$ [$Hcore]
    inext; iintro -
    iexact HΦ

/-- **`*Snaps` is a snapshot store** (`isSnapStore`), its view `snapsOwn g`, its close obligation `Qc` (which shows
the configuration's servers). -/
theorem snaps_isSnapStore
    (wp_Create : github_com.hashicorp.raft.examples.hraftnet.disk.Snaps.Create.spec (GF := GF) (hG := hG))
    (wp_List : github_com.hashicorp.raft.examples.hraftnet.disk.Snaps.List.spec (GF := GF) (hG := hG))
    (wp_Open : github_com.hashicorp.raft.examples.hraftnet.disk.Snaps.Open.spec (GF := GF) (hG := hG))
    (wp_Write : github_com.hashicorp.raft.examples.hraftnet.disk.Sink.Write.spec (GF := GF) (hG := hG))
    (wp_Close : github_com.hashicorp.raft.examples.hraftnet.disk.Sink.Close.spec (GF := GF) (hG := hG))
    (wp_Cancel : github_com.hashicorp.raft.examples.hraftnet.disk.Sink.Cancel.spec (GF := GF) (hG := hG))
    (wp_ID : github_com.hashicorp.raft.examples.hraftnet.disk.Sink.ID.spec (GF := GF) (hG := hG))
    (g : SnapGen) (s : Loc) (Qc : SnapshotMeta → List w8 → IProp GF) (Wf : IProp GF) (eof : GoInterface)
    (hQc : ∀ m b, Qc m b ⊢ (∃ svs : List Server, m.Configuration'.Servers' ↦*□ svs) ∗ Qc m b) :
    isSnaps (GF := GF) g s Qc Wf ∗ globalAddr io.EOF ↦□ eof ⊢
      isSnapStore ⟨go.GoType.PointerType Snaps.ty, #s⟩ (snapsOwn g) eof Qc := by
  iintro ⟨#Hsn, #Heof⟩
  unfold isSnapStore
  isplitr
  · imodintro
    iintro %ver %idx %term %cfgIdx %cfg %trans %Φ HΦ
    iapply wp_Create g s Qc Wf ver idx term cfgIdx cfg trans $$ [$Hsn]
    inext
    iintro %k %id ⟨#Hcore, Hopen⟩
    iapply HΦ
    iintro %Qx %R Hcm
    imodintro
    iexists _
    isplitr
    · iapply snaps_sink_isSink wp_Write wp_Close wp_Cancel wp_ID k s g Qc Wf id ver idx term cfgIdx cfg Qx R hQc
      iexact Hcore
    simp only [sinkOwn]
    iframe
  isplitr
  · imodintro
    iintro %tid %Φ Htok HAU
    iapply wp_List g s Qc Wf Φ
    iframe #
    iintro Hnc
    imod HAU $$ Hnc with ⟨Hnc, HAU⟩
    imodintro
    iframe Hnc
    inext
    icases HAU with ⟨%old, Hown, Hcl⟩
    iexists old
    iframe Hown
    iintro Hown
    imod Hcl $$ Hown with Hk
    imodintro
    iintro %sl %ps Hsl Hm
    iapply Hk $$ Hsl Hm Htok
  · imodintro
    iintro %id %tid %Φ Htok HAU
    iapply wp_Open g s Qc Wf eof id Φ
    iframe #
    iintro Hnc
    imod HAU $$ Hnc with ⟨Hnc, HAU⟩
    imodintro
    iframe Hnc
    inext
    icases HAU with ⟨%old, Hown, Hcl⟩
    iexists old
    iframe Hown
    iintro Hown
    imod Hcl $$ Hown with Hk
    imodintro
    iintro %v Hv
    iapply Hk $$ Hv Htok

end sec

end Perennial
