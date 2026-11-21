/- Read the complete term history before handing the rebuilt MemoryStorage to Raft. -/
module
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReplayAppend
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftNode
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseRestartStor
public import Spec.go_etcd_io.raft.v3.MemoryStorage__FirstIndex
public import Spec.go_etcd_io.raft.v3.MemoryStorage__LastIndex
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Entries

@[expose] public section
noncomputable section
namespace Perennial
namespace EtcdGrove
open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

set_option maxHeartbeats 0 in
theorem replayTermsFromStorage.wp_proof
    (getFirst : MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (getLast : MemoryStorage.LastIndex.spec (GF := GF) (hG := hG))
    (getEntries : MemoryStorage.Entries.spec (GF := GF) (hG := hG))
    (getIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG))
    (getTerm : raftpb.Entry.GetTerm.spec (GF := GF) (hG := hG))
    (ms : Loc) (γs : MemStorNames) (σ : StorContents) (cs : ConfStateM)
    (ordered : (σ.ents.map EntryModel.ofM).Pairwise fun a b => uint.nat a.term ≤ uint.nat b.term) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
       memStorLock ms γs ∗ memStorRestarted ms γs σ cs }}
      (App (Val (@! replayTermsFromStorage)) (Val #ms))
    {{ (out : GoSlice), RET #out; memStorRestarted ms γs σ cs ∗
       out ↦*□ (σ.ents.map EntryModel.ofM).foldl replayAddEntry [] }} := by
  wp_start as ⟨#Hl, Hrest⟩
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  iunfold memStorRestarted at Hrest
  icases Hrest with ⟨Hfresh, Hmeta, #Hc, #Hdummy, Hsn, Hents, Hend⟩
  (try wp_auto)
  wp_apply getFirst ms γs σ.b $$ [$Hraft $Hl $Hc] as %fi ⟨%hfi, #Hc'⟩
  icases memStorFresh_compacted ms γs _ _ _ $$ [$Hfresh $Hc'] with ⟨%hcompact, Hfresh⟩
  have hfirst : uint.nat fi = σ.b + 1 := by omega
  (try wp_auto)
  wp_apply getLast ms γs (σ.last + 1) $$ [$Hraft $Hl $Hend] as %li ⟨Hend, %hli⟩
  have hlast : uint.nat li = σ.b + σ.ents.length := by simpa [StorContents.last] using hli
  ihave #Hnil := ownSlice_nil (GF := GF) (V := replayTermRun) DFrac.discard
  (try wp_auto)
  by_cases hempty : σ.ents = []
  · have hlt : uint.Z li < uint.Z fi := by simp [hempty] at hlast; word
    simp only [hlt, _root_.decide_true]
    (try wp_auto)
    iapply HΦ
    isplitl [Hfresh Hmeta Hsn Hents Hend]
    · iunfold memStorRestarted
      iframe Hfresh Hmeta Hc Hdummy Hsn Hents Hend
    simp only [hempty, List.map_nil, List.foldl_nil]
    iexact Hnil
  · have hpos : 0 < σ.ents.length := List.length_pos_iff.mpr hempty
    have hnlt : ¬ uint.Z li < uint.Z fi := by word
    simp only [hnlt, decide_false]
    iunfold memLog at Hents
    icases Hents with ⟨Hlog, %hbound⟩
    have hsize := hbound.resolve_left hempty
    ihave Hents : memLog γs (σ.b + 1) (DFrac.own 1) σ.ents $$ [Hlog]
    · iunfold memLog
      iframe Hlog
      ipureintro; exact hbound
    have hhi : uint.nat (li + W64 1) = uint.nat li + 1 := by word
    ihave #Hinit := isInitialized_access $$ Hraft
    iNamed Hinit
    (try wp_auto)
    wp_apply getEntries ms γs σ.b DFrac.discard (DFrac.own 1) [memDummy (walSnapCS σ cs)]
        σ.ents fi (li + W64 1) (W64 18446744073709551615) errCompacted $$ [$Hraft $Hl $Hdummy $Hents $ErrCompacted]
      as %sl %es %err ⟨#Hdummy', Hents, Hresult⟩
    · ipureintro; simp only [List.length_singleton]; omega
    icases Hresult with (⟨-, #Hbad⟩ | ⟨-, ⟨%contents, #Hcontents, %hcontents⟩, %hread⟩)
    · icases memStorFresh_compacted ms γs _ _ _ $$ [$Hfresh $Hbad] with ⟨%hbad, -⟩
      omega
    have heq := hread.2.2.2 rfl
    rw [hfirst, hhi, hlast] at heq
    have hd : σ.b + σ.ents.length + 1 - (σ.b + 1) = σ.ents.length := by omega
    simp [hd] at heq
    subst es
    ihave #Hrows := entsPtsC_entsPts γs.sz sl DFrac.discard contents σ.ents hcontents.1 $$ Hcontents
    iunfold entsPts at Hrows
    icases Hrows with ⟨%ls, #Hsl, #Hentries⟩
    ihave #Hmodels := entriesAt_of_entRO ls σ.ents $$ Hentries
    generalize hm : σ.ents.map EntryModel.ofM = models at *
    cases models with
    | nil => simp at hm; contradiction
    | cons first rest =>
      (try wp_auto)
      wp_apply replayTerms.appendEntries_nonempty slice.nil sl [] ls first rest ordered getIndex getTerm
          $$ [$Hpkg $Hnil $Hsl $Hmodels] as %out ⟨%k, %hcut, #Hout⟩
      (try wp_auto)
      iapply HΦ
      isplitl [Hfresh Hmeta Hsn Hents Hend]
      · iunfold memStorRestarted
        iframe Hfresh Hmeta Hc Hdummy Hsn Hents Hend
      isimp only [replayRetain, List.getElem?_nil, List.take_nil] at Hout
      iexact Hout
end EtcdGrove
end Perennial
