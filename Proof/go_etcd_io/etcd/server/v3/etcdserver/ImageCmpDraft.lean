/-
**#7-cmp, the image certificate by the cluster's mode (Draft)** (`notes/image-cmp-plan.md`; the
user's direction of 2026-11-02: in place, `imageAt`'s `keyImage` as `mvcc.keyImageM γk.cmp`, the
mode off today's). Imported by nothing; no `axiom`, no `sorry`; nothing switched. Each `…D` drafts
the unsuffixed statement it names, to replace it in place at the switch (`compaction-in-place.md`).

* **The image** (`imageAtD`): `D`'s key view by the KV names' mode at some compaction records `r`
  (`keyImageM γk.cmp (kvModel γk A) r D`), whose revision is the committed log's compaction revision
  (`r.crev = crevOf γk A`, M2's apply Draft: the scheduled record is the store's `compactMainRev`,
  which is the model's); the rest as today. Off, at a log with no compaction, today's
  (`imageAtD_off`).
* **The certificate** (`dbImageD`, `srvImageD`): today's, over `imageAtD`, with the image's KV log's
  persistent receipt `⧖ (logCh (kvModel γk A))` (B2's `dbImageR`), which the installer's
  `restoreRcptM` needs in compaction mode. `srvNet`'s text stays (`img := srvImage γ`).
* **No mode in the network's certificate** (`dbImageD_of_srvImageD`): the existential KV names of
  `srvImage` fix the start values only, so a receiver gets the image at some mode `b`; it moves it to
  its own (`keyImageM_mode`), the mode off needing `r.crev = -1`, which `crevOf` of its committed log
  gives (a plain log: `crevOf_plain`). So neither `SrvRaft` nor `srvNet` needs the cluster's mode.
* **The sender** (`merged_imageD`): `merged_image` in either mode, from the window's observation
  restated (`mergedObsD`: the image by the store's mode at records of revision `x.crev`), the sole
  writer's receipt, and `kvApplied`'s deferred clause `x.crev = crevOf γk A` (M2 apply item 4).
  Off, today's window gives `mergedObsD` (`mergedObsD_of_off`).
* **The receiver** (`snapRecv_imageMD`): from the certificate, for `applySnapshot.specSnap`: records
  `r` with `keyImageM d.cm L r D`, the receipt `restoreRcptM d L`, the permits `crevPermAt E.γ
  r.finRev`, `crevPermAt E.γ r.crev` (from the store's permit `crevPermIs E.γ (kvCmpPermit γr.kv)`
  and the cluster's permit of the committed log's compaction revision, `CrevPermitLaw`, a law to
  prove), and `hcc` (from the receiver's own `x.crev = crevOf γr.kv A`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapSendBranch
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapRecvFacts
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.M2ApplyDraft
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreImageOpen
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreCmp

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

/-! ## The image by the mode (pure) -/

section pure
variable [GooseExts]

/-- The finished record is at most the restored revision. -/
theorem CmpRecs.finRev_le_crev (r : mvcc.CmpRecs) : r.finRev ≤ r.crev := by
  unfold mvcc.CmpRecs.crev mvcc.CmpRecs.resumes
  split
  · rename_i h; simp only [decide_eq_true_eq] at h; omega
  · exact Int.le_refl _

/-- **No record at revision `-1`** (under `recsPos`, which `keyImageM` on gives). -/
theorem CmpRecs.empty_of_crev (r : mvcc.CmpRecs) (hp : mvcc.recsPos r) (hc : r.crev = -1) :
    r = mvcc.CmpRecs.empty := by
  have hf : ∀ x, r.fin = some x → 1 ≤ sint.Z x := hp.1
  have hs : ∀ x, r.sched = some x → 1 ≤ sint.Z x := hp.2
  unfold mvcc.CmpRecs.crev mvcc.CmpRecs.resumes mvcc.CmpRecs.schedRev mvcc.CmpRecs.finRev at hc
  rcases r with ⟨_ | x, _ | y⟩ <;>
    simp only [Option.map_none, Option.map_some, Option.getD_none, Option.getD_some] at hf hs hc
  · rfl
  · have := hs y rfl
    have h0 : sint.Z y ≠ 0 := by omega
    have h1 : (-1 : Int) < sint.Z y := by omega
    simp [h0, h1] at hc; omega
  · have := hf x rfl; simp at hc; omega
  · have := hf x rfl; have := hs y rfl
    have h0 : sint.Z y ≠ 0 := by omega
    by_cases h : sint.Z x < sint.Z y <;> simp [h0, h] at hc <;> omega

/-- **The mode off's image is the mode on's** (the whole bucket, no record: the cut at `-1`). -/
theorem keyImageM_on_of_off (L : mvcc.Log) (r : mvcc.CmpRecs) (D : backend.Data)
    (h : mvcc.keyImageM false L r D) : mvcc.keyImageM true L r D := by
  obtain ⟨⟨hk, hs, hf⟩, rfl⟩ := (mvcc.keyImageM_off L r D).1 h
  unfold mvcc.keyImageM
  simp only [↓reduceIte]
  refine ⟨mvcc.logEnts L 0 L.length, fun k => by rw [mvcc.bucketOfEnts_logEnts]; exact hk k,
    hf, hs, ⟨(fun x hx => by simp [mvcc.CmpRecs.empty] at hx),
      (fun x hx => by simp [mvcc.CmpRecs.empty] at hx)⟩,
    ⟨(fun x hx => by simp [mvcc.CmpRecs.empty] at hx),
      (fun x hx => by simp [mvcc.CmpRecs.empty] at hx)⟩, ?_, ?_⟩
  · exact mvcc.entsCutAt_full _ _
  · rw [mvcc.CmpRecs.crev_empty]; exact mvcc.NoDelPutAt_neg (by decide)

/-- **The mode on's image at no compaction is the mode off's**: records at `-1` are none
(`recsPos`), and the cut at `-1` deletes nothing (`KeyDel_neg`), so the bucket is the log's. -/
theorem keyImageM_off_of_on (L : mvcc.Log) (r : mvcc.CmpRecs) (D : backend.Data)
    (hb : mvcc.LogB L) (h : mvcc.keyImageM true L r D) (hc : r.crev = -1) :
    mvcc.keyImageM false L r D := by
  unfold mvcc.keyImageM at h
  simp only [↓reduceIte] at h
  obtain ⟨ents, hk, hfin, hsched, -, hpos, hcut, -⟩ := h
  have hr := CmpRecs.empty_of_crev r hpos hc
  subst hr
  rw [mvcc.keyImageM_off]
  refine ⟨⟨fun k => ?_, hsched, hfin⟩, rfl⟩
  rw [hk k, ← mvcc.bucketOfEnts_logEnts]
  -- every entry of the log is in the cut at `-1`
  have hall : ∀ e ∈ mvcc.logEnts L 0 L.length, e ∈ ents := by
    intro e he
    exact Classical.byContradiction fun hn => mvcc.KeyDel_neg (by decide) (hcut.2.1 e he hn)
  apply Option.ext
  intro v
  have h1 := mvcc.bucketOfEnts_lookup_iff L hb hcut.1 k v
  have h2 := mvcc.bucketOfEnts_lookup_iff L hb (List.Sublist.refl (mvcc.logEnts L 0 L.length)) k v
  change (mvcc.bucketOfEnts ents).lookup k = some v ↔ _ at h1
  change (mvcc.bucketOfEnts (mvcc.logEnts L 0 L.length)).lookup k = some v ↔ _ at h2
  rw [h1, h2]
  constructor
  · intro hm
    exact (hcut.1.map mvcc.KvEnt.pair).subset hm
  · intro hm
    obtain ⟨e, he, hpe⟩ := List.mem_map.1 hm
    exact List.mem_map.2 ⟨e, hall e he, hpe⟩

/-- **An image moves between the modes** when, for the mode off, the records' revision is `-1`. -/
theorem keyImageM_mode (b b' : Bool) (L : mvcc.Log) (r : mvcc.CmpRecs) (D : backend.Data)
    (hb : mvcc.LogB L) (h : mvcc.keyImageM b L r D) (hc : b = true → b' = false → r.crev = -1) :
    mvcc.keyImageM b' L r D := by
  cases b <;> cases b'
  · exact h
  · exact keyImageM_on_of_off L r D h
  · exact keyImageM_off_of_on L r D hb h (hc rfl rfl)
  · exact h

/-- **Draft of `imageAt`** (see the file header): the key view by the KV names' mode, at records of
the committed log's compaction revision; the rest today's. -/
def imageAtD (γk : KVNames) (bootLog : List EntryM) (i : w64) (L A : List EntryModel)
    (D : backend.Data) : Prop :=
  (∃ r : mvcc.CmpRecs, mvcc.keyImageM γk.cmp (kvModel γk A) r D ∧ r.crev = crevOf γk A) ∧
    backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName
      go_etcd_io.etcd.server.v3.storage.schema.ciKeyBytes = encMeta i ∧
    (∃ t : w64, backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName
      go_etcd_io.etcd.server.v3.storage.schema.termKeyBytes = encMeta t) ∧
    bkRestAt γk.c0 bootLog L D ∧ mvcc.IdxWf (kvModel γk A) []

/-- **Off, at a log with no compaction, today's image** (`keyImageM_off`). -/
theorem imageAtD_off (γk : KVNames) (bootLog : List EntryM) (i : w64) (L A : List EntryModel)
    (D : backend.Data) (hcm : γk.cmp = false) :
    imageAtD γk bootLog i L A D ↔ imageAt γk bootLog i L A D ∧ crevOf γk A = -1 := by
  unfold imageAtD imageAt
  rw [hcm]
  constructor
  · rintro ⟨⟨r, hk, hc⟩, h2, h3, h4, h5⟩
    obtain ⟨hk', hr⟩ := (mvcc.keyImageM_off _ r D).1 hk
    subst hr
    exact ⟨⟨hk', h2, h3, h4, h5⟩, by rw [← hc, mvcc.CmpRecs.crev_empty]⟩
  · rintro ⟨⟨hk, h2, h3, h4, h5⟩, hc⟩
    exact ⟨⟨mvcc.CmpRecs.empty, (mvcc.keyImageM_off _ _ D).2 ⟨hk, rfl⟩,
      by rw [mvcc.CmpRecs.crev_empty, hc]⟩, h2, h3, h4, h5⟩

/-- `imageAtD` reads the KV names through their start values and mode. -/
theorem imageAtD_kv_congr {γk γk' : KVNames} {bootLog : List EntryM} {i : w64}
    {L A : List EntryModel} {D : backend.Data}
    (h0 : γk.c0 = γk'.c0) (h1 : γk.ch0 = γk'.ch0) (h2 : γk.log0 = γk'.log0)
    (hc : γk.cmp = true → γk'.cmp = false → crevOf γk A = -1) :
    imageAtD γk bootLog i L A D → imageAtD γk' bootLog i L A D := by
  have hk : kvModel γk A = kvModel γk' A := by simp only [kvModel, h0, h1, h2]
  have hcr : crevOf γk A = crevOf γk' A := by simp only [crevOf, h0, h1]
  rintro ⟨⟨r, hkI, hr⟩, h2', h3, h4, h5⟩
  have hb : mvcc.LogB (kvModel γk A) := ⟨by have := h5.2.1; omega, h5.2.2.2⟩
  refine ⟨⟨r, ?_, by rw [← hcr]; exact hr⟩, h2', h3, by rw [← h0]; exact h4, by rw [← hk]; exact h5⟩
  rw [← hk]
  exact keyImageM_mode _ _ _ r D hb hkI (fun h h' => by rw [hr]; exact hc h h')

/-- **What the merged snapshot observes, by the store's mode** (draft of `mergedObs`): the image of
the apply thread's KV log `log` at the store's mode `cmp` and records of revision `crev` (the apply
thread's `x.crev`, the store's `compactMainRev`), in place of today's two clauses for the `Key`
bucket and `noCmpData` (gone: `keyImageM` gives both, either mode); the rest today's. -/
def mergedObsD (γr : ReadNames) (cmp : Bool) (ai : w64) (A : List EntryModel) (log : mvcc.Log)
    (crev : Int) (D : backend.Data) : Prop :=
  (∃ r : mvcc.CmpRecs, mvcc.keyImageM cmp log r D ∧ r.crev = crev) ∧
    backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName
      go_etcd_io.etcd.server.v3.storage.schema.ciKeyBytes = encMeta ai ∧
    (∃ t : w64, backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName
      go_etcd_io.etcd.server.v3.storage.schema.termKeyBytes = encMeta t) ∧
    bkRestAt γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A) D ∧ mvcc.IdxWf log []

/-- **Off, today's observation is the draft's** (at revision `-1`): the window's mode-off proof
stands. -/
theorem mergedObsD_of_off (γr : ReadNames) (ai : w64) (A : List EntryModel) (log : mvcc.Log)
    (D : backend.Data) (h : mergedObs γr false ai A log D) : mergedObsD γr false ai A log (-1) D := by
  obtain ⟨-, hk, hn, h3, h4, h5, h6⟩ := h
  exact ⟨⟨mvcc.CmpRecs.empty, (mvcc.keyImageM_off _ _ D).2 ⟨⟨hk rfl, (hn rfl).1, (hn rfl).2⟩, rfl⟩,
    mvcc.CmpRecs.crev_empty⟩, h3, h4, h5, h6⟩

end pure

/-! ## The certificate -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **Draft of `dbImage`**: today's over `imageAtD`, with the image's KV log's persistent receipt
(B2's `dbImageR`). -/
def dbImageD (γ : ServerRaftNames) (γk : KVNames) (i : w64) (D : backend.Data) : IProp GF :=
  iprop(∃ A : List EntryModel, srvRLogLb γ A ∗
    ⌜uint.Z i = uint.Z γ.ai0 + A.length ∧ imageAtD γk γ.raft.boot i (γ.pre ++ A) A D⌝ ∗
    ⧖ (mvcc.logCh (kvModel γk A)))

instance dbImageD_persistent (γ : ServerRaftNames) (γk : KVNames) (i : w64) (D : backend.Data) :
    Persistent (dbImageD (GF := GF) γ γk i D) := by
  unfold dbImageD; infer_instance

/-- **Draft of `srvImage`** (`srvNet`'s `img`, the snapshot directory's): its text, over
`dbImageD`. -/
def srvImageD (γ : SrvRaft) (i : w64) (D : backend.Data) : IProp GF :=
  iprop(∃ γk : KVNames, ⌜γk.c0 = W64 0 ∧ γk.ch0 = apply.alarmChain false false false ∧
    γk.log0 = [[], []]⌝ ∗ dbImageD ⟨γ, [], W64 0⟩ γk i D)

instance srvImageD_persistent (γ : SrvRaft) (i : w64) (D : backend.Data) :
    Persistent (srvImageD (GF := GF) γ i D) := by
  unfold srvImageD; infer_instance

/-- A member's certificate is the network's (`srvImage_of_dbImage`). -/
theorem srvImageD_of_dbImageD {γ : SrvRaft} {γk : KVNames} {i : w64} {D : backend.Data}
    (h0 : γk.c0 = W64 0) (h1 : γk.ch0 = apply.alarmChain false false false)
    (h2 : γk.log0 = [[], []]) :
    dbImageD (GF := GF) ⟨γ, [], W64 0⟩ γk i D ⊢ srvImageD γ i D := by
  iintro #H
  iunfold srvImageD
  iexists γk
  iframe H
  ipureintro; exact ⟨h0, h1, h2⟩

/-- **The network's certificate at a member's names** (`dbImage_of_srvImage`), at the sender's
mode `b` (the network's certificate names none): a receiver moves the image to its own mode with
`imageAtD_kv_congr`, the mode off needing its committed log's `crevOf` at `-1` (`crevOf_off`). -/
theorem dbImageD_of_srvImageD {γ : SrvRaft} {γk : KVNames} {i : w64} {D : backend.Data}
    (h0 : γk.c0 = W64 0) (h1 : γk.ch0 = apply.alarmChain false false false)
    (h2 : γk.log0 = [[], []]) :
    srvImageD (GF := GF) γ i D ⊢ ∃ b : Bool, dbImageD ⟨γ, [], W64 0⟩ { γk with cmp := b } i D := by
  iintro H
  iunfold srvImageD at H
  icases H with ⟨%γk', %h, #H⟩
  obtain ⟨h0', h1', h2'⟩ := h
  iexists γk'.cmp
  iunfold dbImageD at H
  icases H with ⟨%A, #HA, %hA, #Hp⟩
  have hk : kvModel γk' A = kvModel { γk with cmp := γk'.cmp } A := by
    simp only [kvModel, h0', h1', h2', h0, h1, h2]
  iunfold dbImageD
  iexists A
  iframe HA
  rw [← hk]
  iframe Hp
  ipureintro
  exact ⟨hA.1, imageAtD_kv_congr (h0'.trans h0.symm) (h1'.trans h1.symm) (h2'.trans h2.symm)
    (fun h h' => by simp only at h'; rw [h] at h'; cases h') hA.2⟩

end defs

/-! ## The sender: `merged_image` in either mode -/

section sender
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **Draft of `merged_image`, both modes** (in place of `merged_image` and `merged_image_cmp`,
SNAPSHOT-SORRY #7-cmp): the window's observation `mergedObsD` at the store's mode and the apply
thread's compaction revision `x.crev`, the sole writer's receipt of the KV log (`idxCert`'s, which
the window's restated post hands out: `mergedCreate_window`), and `kvApplied`'s deferred clause
`x.crev = crevOf γr.kv A` (`hcrev`; M2 apply item 4) give the network's certificate. -/
theorem merged_imageD (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (ai : w64) (A : List EntryModel)
    (x : apply.ApplyKV) (D : backend.Data) (hlen : uint.Z ai = A.length)
    (h0 : γr.kv.c0 = W64 0 ∧ γr.kv.log0 = [[], []]) (hcrev : x.crev = crevOf γr.kv A) :
    ⌜mergedObsD γr E.cmp ai A x.log x.crev D⌝ ∗ ⧖ (mvcc.logCh x.log) ∗
      isServer s γ ci TM E ρ γr ∗ kvApplied γr.raft γr.kv A x ⊢
      |={⊤}=> kvApplied γr.raft γr.kv A x ∗ □ srvImageD (GF := GF) γr.raft.raft ai D := by
  iintro ⟨%hobs, #Hrc, #Hsrv, Hka⟩
  obtain ⟨⟨r, hkI, hr⟩, hci, hterm, hrest, hwf⟩ := hobs
  iunfold isServer at Hsrv
  icases Hsrv with ⟨-, -, -, Hat, -, -⟩
  iunfold srvAtomics at Hat
  icases Hat with ⟨-, -, Hki⟩
  iunfold srvKVInvs at Hki
  icases Hki with ⟨#Hki, -, #Hrl, -, %Hcm, -⟩
  ihave %hraft := srvRaftLogInv_fresh γr.raft $$ Hrl
  imod (kvInv_ch0_off γr.raft γr.kv) $$ Hki with %hch
  iunfold kvApplied at Hka
  icases Hka with ⟨Hka, %hx⟩
  iunfold kvAppliedL at Hka
  icases Hka with ⟨#HA, Hhi, Hcert, %hlog⟩
  imodintro
  isplitl [Hhi Hcert]
  · iunfold kvApplied
    iunfold kvAppliedL
    iframe HA Hhi Hcert
    ipureintro; exact ⟨hlog, hx⟩
  ihave #HA' : srvRLogLb (GF := GF) ⟨γr.raft.raft, [], W64 0⟩ A $$ []
  · rw [← hraft]; iexact HA
  iintro !>
  iapply (srvImageD_of_dbImageD (γk := γr.kv) h0.1 hch h0.2)
  iunfold dbImageD
  iexists A
  iframe HA'
  rw [← hlog]
  iframe Hrc
  ipureintro
  have hpre : γr.raft.pre = [] := by rw [hraft]
  have hz : uint.Z (W64 0) = 0 := rfl
  rw [hlog] at hkI hwf
  refine ⟨by simp only []; omega, ⟨⟨r, ?_, by rw [hr, hcrev]⟩, hci, hterm, ?_, hwf⟩⟩
  · rw [Hcm.1]; exact hkI
  · simpa [hpre] using hrest

end sender

/-! ## The receiver: `applySnapshot.specSnap`'s image premises -/

section receiver
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **A law to prove (the Prove phase): the committed log's compaction revision is the cluster's
permit** (`crevOf` is `-1` or the revision of a committed compaction, whose claim, `cmpLogOk`, puts
it at a positive revision at least the retention below a revision the model reached:
`cmpPermRq_of_entry`'s argument, at `crevOf`). -/
def CrevPermitLaw (γ : ServerRaftNames) (γk : KVNames) : Prop :=
  ∀ A : List EntryModel, ⊢ kvInv (GF := GF) γ γk -∗ srvRaftLogInv γ -∗ srvRLogLb γ A ={⊤}=∗
    ⌜crevOf γk A = -1⌝ ∨ kvCmpPermit γk (crevOf γk A)

/-- **Off, a committed log has no compaction** (`kv_log_plain`, `crevOf_plain`). -/
theorem crevOf_off (γ : ServerRaftNames) (γk : KVNames) (A : List EntryModel) (hcm : γk.cmp = false) :
    ⊢ kvInv (GF := GF) γ γk -∗ srvRaftLogInv γ -∗ srvRLogLb γ A ={⊤}=∗ ⌜crevOf γk A = -1⌝ := by
  iintro #Hinv #Hr #HA
  imod kv_log_plain γ γk A $$ Hinv Hr HA with %Hp
  imodintro
  ipureintro
  rw [hcm, plainLogM_false] at Hp
  exact crevOf_plain γk A Hp.1

/-- The mode-off fact for a committed log, in either mode. -/
theorem crevOf_offM (γ : ServerRaftNames) (γk : KVNames) (A : List EntryModel) :
    ⊢ kvInv (GF := GF) γ γk -∗ srvRaftLogInv γ -∗ srvRLogLb γ A ={⊤}=∗
      ⌜γk.cmp = false → crevOf γk A = -1⌝ := by
  iintro #Hinv #Hr #HA
  cases hm : γk.cmp
  · imod crevOf_off γ γk A hm $$ Hinv Hr HA with %h
    imodintro; ipureintro; exact fun _ => h
  · imodintro; ipureintro; intro h; cases h

/-- A permit at a positive revision below a permitted one. -/
theorem kvCmpPermit_le (γk : KVNames) (c c' : Int) (h0 : 0 < c) (h : c ≤ c') :
    kvCmpPermit (GF := GF) γk c' ⊢ kvCmpPermit γk c := by
  iintro H
  iunfold kvCmpPermit at H
  icases H with ⟨-, #H⟩
  iunfold kvCmpPermit
  isplitr
  · ipureintro; exact h0
  iapply kvRevLbZ_mono γk (c + γk.cret) (c' + γk.cret) (by omega)
  iexact H

/-- **The glue at `specSnap`'s call** (in compaction mode `run_job_snap_cmp`'s, either mode): from
the network's certificate of the received file `D` at the snapshot's index `i` and the image's
committed log `A'` (`snapRecv_image`'s, of length `i`), the receiver's KV invariants (its store's
permit `crevPermIs E.γ (kvCmpPermit γr.kv)`, the mode tie `γr.kv.cmp = E.cmp`) and the new backend's
mode `d.cm = E.cmp`: the records `r` with `keyImageM d.cm (kvModel γr.kv A') r D`, the restored
log's receipt, the two permits, and `hcc` from the receiver's `x.crev = crevOf γr.kv A` at an
applied `A` below `A'`. -/
theorem snapRecv_imageMD (γ : SrvRaft) (γr : ReadNames) (E : apply.AEnv GF) (d : mvcc.KBReal)
    (i : w64) (D : backend.Data) (A A' : List EntryModel) (x : apply.ApplyKV)
    (hraft : γr.raft = ⟨γ, [], W64 0⟩) (hc0 : γr.kv.c0 = W64 0)
    (hch : γr.kv.ch0 = apply.alarmChain false false false) (hlog0 : γr.kv.log0 = [[], []])
    (hlA : uint.Z i = A'.length) (hAA : A <+: A') (hdcm : d.cm = E.cmp)
    (hcrev : x.crev = crevOf γr.kv A) (hperm : CrevPermitLaw (GF := GF) γr.raft γr.kv) :
    ⊢ srvKVInvs E γr -∗ srvImageD γ i D -∗ srvRLogLb γr.raft A' ={⊤}=∗
      ∃ r : mvcc.CmpRecs, ⌜mvcc.keyImageM d.cm (kvModel γr.kv A') r D ∧
          (d.cm = true → x.crev ≤ r.crev)⌝ ∗
        mvcc.restoreRcptM d (kvModel γr.kv A') ∗ mvcc.crevPermAt E.γ r.finRev ∗
        mvcc.crevPermAt E.γ r.crev := by
  iintro #Hinvs #Himg #HA'
  iunfold srvKVInvs at Hinvs
  icases Hinvs with ⟨#HkI, -, #HrI, -, %Hcm, -, #Hcp⟩
  -- the certificate at the sender's mode, its committed log `A'` (one length, one log)
  ihave ⟨%b, #Hdb⟩ := (dbImageD_of_srvImageD (γ := γ) (γk := γr.kv) (i := i) (D := D) hc0 hch hlog0)
    $$ Himg
  iunfold dbImageD at Hdb
  icases Hdb with ⟨%B, #HB, %hB, #Hrc⟩
  ihave #HB' : srvRLogLb (GF := GF) γr.raft B $$ []
  · rw [hraft]; iexact HB
  ihave %Hpf := srvRLogLb_prefix _ A' B $$ [HA' HB']
  · iframe HA' HB'
  have hz : uint.Z (W64 0) = 0 := rfl
  have hlB : uint.Z i = B.length := by have := hB.1; simp only at this; omega
  have heq : A' = B := by
    rcases Hpf with h | h
    · exact h.eq_of_length (by omega)
    · exact (h.eq_of_length (by omega)).symm
  subst heq
  have hk : kvModel { γr.kv with cmp := b } A' = kvModel γr.kv A' := rfl
  have hcr : crevOf { γr.kv with cmp := b } A' = crevOf γr.kv A' := rfl
  -- the receiver's mode: off, its committed log has no compaction
  imod crevOf_offM γr.raft γr.kv A' $$ HkI HrI HA' with %Hoff
  have himg : imageAtD γr.kv γ.boot i ([] ++ A') A' D :=
    imageAtD_kv_congr (γk := { γr.kv with cmp := b }) rfl rfl rfl
      (fun _ h => by rw [hcr]; exact Hoff h) hB.2
  obtain ⟨⟨r, hkI, hr⟩, -, -, -, -⟩ := himg
  rw [Hcm.1, ← hdcm] at hkI
  have hcc : d.cm = true → x.crev ≤ r.crev := fun _ => by
    rw [hcrev, hr]; exact crevOf_mono γr.kv A A' hAA
  -- the receipt
  ihave #Hrcpt : mvcc.restoreRcptM (GF := GF) d (kvModel γr.kv A') $$ []
  · unfold mvcc.restoreRcptM
    split
    · rw [← hk]; iexact Hrc
    · itrivial
  -- the permits: none off; on, the committed log's compaction revision's
  cases hdm : d.cm with
  | false =>
    rw [hdm] at hkI
    obtain ⟨-, rfl⟩ := (mvcc.keyImageM_off _ _ D).1 hkI
    imodintro
    iexists mvcc.CmpRecs.empty
    iframe Hrcpt
    isplitr
    · ipureintro; rw [hdm] at hcc; exact ⟨(mvcc.keyImageM_off _ _ D).2 ⟨by
        obtain ⟨h, -⟩ := (mvcc.keyImageM_off _ _ D).1 (by rw [← hdm] at hkI ⊢; exact hkI); exact h,
        rfl⟩, hcc⟩
    rw [mvcc.CmpRecs.finRev_empty, mvcc.CmpRecs.crev_empty]
    isplitr <;> iapply mvcc.crevPermAt_none
  | true =>
    rw [hdm] at hkI
    have hpos : mvcc.recsPos r := by
      unfold mvcc.keyImageM at hkI; simp only [↓reduceIte] at hkI
      obtain ⟨-, -, -, -, -, h, -⟩ := hkI; exact h
    imod hperm A' $$ HkI HrI HA' with (%Hn | #Hp)
    · have he := CmpRecs.empty_of_crev r hpos (by rw [hr]; exact Hn)
      subst he
      imodintro
      iexists mvcc.CmpRecs.empty
      iframe Hrcpt
      isplitr
      · ipureintro; rw [hdm] at hcc; exact ⟨hkI, hcc⟩
      rw [mvcc.CmpRecs.finRev_empty, mvcc.CmpRecs.crev_empty]
      isplitr <;> iapply mvcc.crevPermAt_none
    · imodintro
      iexists r
      iframe Hrcpt
      isplitr
      · ipureintro; rw [hdm] at hcc; exact ⟨hkI, hcc⟩
      ihave #Hpc : mvcc.crevPermAt (GF := GF) E.γ r.crev $$ []
      · rw [hr]
        iapply mvcc.crevPermAt_of E.γ (kvCmpPermit γr.kv) (crevOf γr.kv A')
        iframe Hcp
        imodintro; iexact Hp
      iframe Hpc
      -- the finished record: none, or a positive revision below the restored one
      have hf : r.finRev = -1 ∨ 1 ≤ r.finRev := by
        have hp1 : ∀ x, r.fin = some x → 1 ≤ sint.Z x := hpos.1
        unfold mvcc.CmpRecs.finRev
        cases hfx : r.fin with
        | none => left; rfl
        | some y => right; have := hp1 y hfx; simpa using this
      rcases hf with hf | hf
      · rw [hf]; iapply mvcc.crevPermAt_none
      · iapply mvcc.crevPermAt_of E.γ (kvCmpPermit γr.kv) r.finRev
        iframe Hcp
        imodintro
        iapply (kvCmpPermit_le γr.kv r.finRev (crevOf γr.kv A') (by omega)
          (by rw [← hr]; exact CmpRecs.finRev_le_crev r))
        iexact Hp

end receiver

end EtcdGrove
end Perennial
