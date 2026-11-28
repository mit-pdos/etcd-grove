/-
(hraft_robust R3) The snapshot store's crash invariant and lock invariant (`dir/snap`, `*Snaps`), the
disk's design (`Inv.lean`) with `SnapLatest` for the abstract state:

* `SnapGen`: a generation's names (durable's, the client view's half `γl`, the window record `γw`, the crash
  token `γk`).
* The record holds the client's latest `lat`, the image's latest `lt` (what the file keeps of it: `latRep lat lt`,
  the metadata up to its servers slice, whose servers the image holds) and the window.
* `snapsInv g Qc Wf` (namespace `snapsN`, inside `storeN` and `durAuMask`): `durable`'s client state and the
  record's half, and, until the crash lemma takes them with `γk`, the view's other half and the window's facts:
  idle (the file holds the latest, with some next ID), open (a `Close`'s rename done and not yet committed to the
  client: the file holds the new latest `(m, b)` (newer than `lat`), the old file may survive a crash, and the
  close obligation `Qc m b` is held; the sink's own `Qx` stays with the closing thread), fresh (`FreshSnaps`
  before its write is synced: the caller's `Wf`).
* `snapsLockInv g s` (`s.mu`): `s`'s memory at the record's latest, idle, durable's handle and a call permission.
* `isSnaps g s Qc Wf`: the persistent handle.

The next ID (`nextID`, `Create`'s counter) is not part of the abstract state: `Create` increments it in memory
only, and the file keeps whatever the last persisting `Close` wrote.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.Inv

@[expose] public section

noncomputable section

namespace Perennial

namespace github_com.hashicorp.raft.examples.hraftnet.disk

open Iris Iris.BI Iris.ProofMode github_com.hashicorp.raft proto EtcdGrove

/-- The image's latest snapshot (`SnapImg.latest`). -/
abbrev SLat : Type := Option (SMeta × List w8)

/-- The image's latest is well formed (whatever the next ID). -/
def ltOk (lt : SLat) : Prop := SnapImg.Ok ⟨W64 0, lt⟩

theorem ltOk_iff (n : w64) (lt : SLat) : SnapImg.Ok ⟨n, lt⟩ ↔ ltOk lt := Iff.rfl

section types
variable [GooseExts]

/-- The window: idle; a `Close` of `(m, b)` between its rename and its commit, the file holding the latest
`(sm, b)` with next ID `nid` (`sy`: its directory synced); `FreshSnaps` before its write is synced (`r`: its rename
done). -/
inductive SnapWin
  | idle
  | open (m : SnapshotMeta) (b : List w8) (sm : SMeta) (nid : w64) (sy : Bool)
  | fresh (r : Bool)

instance sserver_countable : Pos.Countable SServer :=
  Pos.Countable.ofInjective (fun s => Pos.Countable.encode (s.suffrage, s.id, s.addr))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h; subst h1 h2 h3; rfl)

instance smeta_countable : Pos.Countable SMeta :=
  Pos.Countable.ofInjective
    (fun m => Pos.Countable.encode (m.version, m.id, m.index, m.term, m.servers, m.cfgIndex))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h; subst h1 h2 h3 h4 h5 h6; rfl)

def snapWinEnc : SnapWin → Option (Bool ⊕ (SnapshotMeta × List w8 × SMeta × w64 × Bool))
  | .idle => none
  | .fresh r => some (.inl r)
  | .open m b sm nid sy => some (.inr (m, b, sm, nid, sy))

instance snapWin_countable : Pos.Countable SnapWin :=
  Pos.Countable.ofInjective (fun w => Pos.Countable.encode (snapWinEnc w))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a <;> cases b <;> simp only [snapWinEnc, Option.some.injEq, Prod.mk.injEq, reduceCtorEq,
        Sum.inl.injEq, Sum.inr.injEq] at h
      all_goals first | rfl | (subst h; rfl) | (obtain ⟨h1, h2, h3, h4, h5⟩ := h; subst h1 h2 h3 h4 h5; rfl))

/-- The record's value: the client's latest, the image's, the window. -/
abbrev SnapRec : Type := SnapLatest × SLat × SnapWin

/-- **A generation's names** (see the file header). -/
structure SnapGen where
  γd : DurFs.DurGS
  f : DurFs.DFile
  R : Fs.Roots
  γl : GName
  γw : GName
  γk : GName

/-- **The snapshot store's invariant's namespace.** -/
def snapsN : Namespace := storeN .@ "snap"

theorem snapsN_sub_storeN : (↑snapsN : CoPset) ⊆ ↑storeN := nclose_subseteq _ _

set_option maxRecDepth 100000 in
/-- The invariant is open inside `durable`'s atomic updates. -/
theorem snapsN_sub_durAu : (↑snapsN : CoPset) ⊆ DurFs.durAuMask := by
  intro x hx
  have h1 := nclose_subseteq' _ (mask_ndot_ne' nroot "hraftstore" "osfs" (by decide)) x hx
  have h2 := nclose_subseteq' _ (mask_ndot_ne' nroot "hraftstore" "osfsShared" (by decide)) x hx
  have h3 := nclose_subseteq' _ (mask_ndot_ne' nroot "hraftstore" "durable" (by decide)) x hx
  rw [Std.LawfulSet.mem_diff] at h1 h2 h3
  unfold DurFs.durAuMask Fs.osAuMask
  rw [Std.LawfulSet.mem_diff, Std.LawfulSet.mem_diff, Std.LawfulSet.mem_diff]
  exact ⟨⟨⟨CoPset.mem_full, h1.2⟩, h2.2⟩, h3.2⟩

/-- `snapsN` is outside `durable`'s namespace. -/
theorem snapsN_not_durN (x : Pos) (hx : x ∈ (↑snapsN : CoPset)) : x ∉ (↑DurFs.durN : CoPset) := by
  have := snapsN_sub_durAu x hx
  unfold DurFs.durAuMask at this
  rw [Std.LawfulSet.mem_diff] at this
  exact this.2

theorem diff_storeN_sub_snapsN : (⊤ : CoPset) \ ↑storeN ⊆ ⊤ \ ↑snapsN := by
  intro x hx
  rw [Std.LawfulSet.mem_diff] at hx ⊢
  exact ⟨hx.1, fun h => hx.2 (snapsN_sub_storeN x h)⟩

/-- The pure part of `metaRep`. -/
def metaPure (mv : SnapshotMeta) (m : SMeta) (n : Nat) : Prop :=
  mv.Version' = m.version ∧ mv.ID' = m.id ∧ mv.Index' = m.index ∧ mv.Term' = m.term ∧
    mv.Peers' = slice.nil ∧ mv.ConfigurationIndex' = m.cfgIndex ∧ mv.Size' = W64 (n : Int)

/-- **The image's latest `lt` matches the latest `lat`, its servers being `svs`'s** (pure: what a crash carries
to the next generation). -/
def latMatch (lat : SnapLatest) (lt : SLat) (svs : List Server) : Prop :=
  match lat, lt with
  | none, none => True
  | some (m, b), some (sm, b') => b' = b ∧ metaPure m sm b.length ∧ sm.servers = svs.map srvOf
  | _, _ => False

/-- **`v` (what `durable.Read` returns) decodes to the latest `lat`, whose servers are `svs`** (up to its
servers slice). -/
def snapHolds (v : Option GoString) (lat : SnapLatest) (svs : List Server) : Prop :=
  ∃ S : SnapImg, S.Ok ∧ v = some (encSnap S) ∧ latMatch lat S.latest svs

end types

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]

/-- **The snapshot store's view** (`isSnapStore`'s `own`). -/
def snapsOwn (g : SnapGen) (lat : SnapLatest) : IProp GF := ghostVar g.γl (1 : Qp).half lat

/-- **The image's latest `lt` represents the latest `lat`** (`metaRep`; persistent). -/
def latRep (lat : SnapLatest) (lt : SLat) : IProp GF :=
  match lat, lt with
  | none, none => iprop(True)
  | some (m, b), some (sm, b') => iprop(⌜b' = b⌝ ∗ metaRep m sm b.length)
  | _, _ => iprop(False)

instance latRep_persistent lat lt : Persistent (latRep (GF := GF) lat lt) := by
  unfold latRep; split <;> infer_instance

/-- The latest's servers slice holds `svs` (nothing without a latest). -/
def latSrvs (lat : SnapLatest) (svs : List Server) : IProp GF :=
  match lat with
  | none => iprop(True)
  | some (m, _) => iprop(m.Configuration'.Servers' ↦*□ svs)

instance latSrvs_persistent lat svs : Persistent (latSrvs (GF := GF) lat svs) := by
  unfold latSrvs; split <;> infer_instance

/-- **The latest `lat'` is `lat` up to its servers slice** (`metaEquiv`), which holds the old servers `svs`. -/
def latEquiv (lat lat' : SnapLatest) (svs : List Server) : IProp GF :=
  match lat, lat' with
  | none, none => iprop(True)
  | some (m, b), some (m', b') => iprop(⌜b' = b ∧ metaEquiv m m'⌝ ∗ m'.Configuration'.Servers' ↦*□ svs)
  | _, _ => iprop(False)

/-- **The window's facts and resources** (see the file header). -/
def snapWinRes (Qc : SnapshotMeta → List w8 → IProp GF) (Wf : IProp GF) (lat : SnapLatest) (lt : SLat)
    (s : DurFs.DurSt) : SnapWin → IProp GF
  | .idle => iprop(⌜∃ nid, s = ⟨some (encSnap ⟨nid, lt⟩), none⟩⌝)
  | .open m b sm nid sy => iprop(⌜newerSnap lat m b = some (m, b) ∧ b.length < 2 ^ 63 ∧ ltOk (some (sm, b)) ∧
      s.cur = some (encSnap ⟨nid, some (sm, b)⟩) ∧
      (s.alt = none ∨ (sy = false ∧ ∃ nid0, s.alt = some (some (encSnap ⟨nid0, lt⟩))))⌝ ∗
      metaRep m sm b.length ∗ Qc m b)
  | .fresh r => iprop(Wf ∗ ⌜r = true → ∃ nid, s.cur = some (encSnap ⟨nid, lt⟩)⌝)

/-- **The invariant's contents** (see the file header). -/
def snapsBody (g : SnapGen) (Qc : SnapshotMeta → List w8 → IProp GF) (Wf : IProp GF) : IProp GF :=
  iprop(∃ (lat : SnapLatest) (lt : SLat) (w : SnapWin) (s : DurFs.DurSt),
    DurFs.durSt g.γd s ∗ ghostVar g.γw (1 : Qp).half ((lat, lt, w) : SnapRec) ∗
    ((ghostVar g.γl (1 : Qp).half lat ∗ latRep lat lt ∗ ⌜ltOk lt⌝ ∗ snapWinRes Qc Wf lat lt s w) ∨
      crashed ∗ token g.γk))

/-- **The snapshot store's crash invariant.** -/
def snapsInv (g : SnapGen) (Qc : SnapshotMeta → List w8 → IProp GF) (Wf : IProp GF) : IProp GF :=
  inv snapsN (snapsBody g Qc Wf)

instance snapsInv_persistent g Qc Wf : Persistent (snapsInv (GF := GF) g Qc Wf) := by
  unfold snapsInv; infer_instance

/-- The metadata field's value is the latest's metadata (`List`/`Open` return it). -/
def latMv (lat : SnapLatest) (mv : SnapshotMeta) : Prop :=
  match lat with
  | none => True
  | some (m, _) => mv = m

/-- **The lock invariant** of `s.mu`. -/
def snapsLockInv (g : SnapGen) (s : Loc) : IProp GF :=
  iprop(∃ (lat : SnapLatest) (lt : SLat) (nid : w64) (has : Bool) (mv : SnapshotMeta) (dt : GoSlice) (qc : Qp),
    snapsMemAt s ⟨nid, lt⟩ has mv dt ∗ ⌜latMv lat mv⌝ ∗ latRep lat lt ∗ ghostVar g.γw (1 : Qp).half ((lat, lt, SnapWin.idle) : SnapRec) ∗
    DurFs.durHandle g.γd g.f g.R ∗ Fs.osCallPerm (Fs.callKey g.R g.f.d) qc)

/-- **The handle on `*Snaps` `s`** of the generation `g`, with the client's close obligation `Qc` and `FreshSnaps`'s
`Wf`. -/
def isSnaps (g : SnapGen) (s : Loc) (Qc : SnapshotMeta → List w8 → IProp GF) (Wf : IProp GF) : IProp GF :=
  iprop(∃ mu : Loc,
    isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.disk ∗
    s.[Snaps, go!"mu"] ↦□ mu ∗ sync.isMutex mu (snapsLockInv g s) ∗ s.[Snaps, go!"file"] ↦□ g.f.name ∗
    snapsInv g Qc Wf ∗ DurFs.durInv g.γd g.f ∗ Fs.osInv ∗ Fs.osSharedInv g.R ∗ ⌜g.f.Ok⌝)

instance isSnaps_persistent g s Qc Wf : Persistent (isSnaps (GF := GF) g s Qc Wf) := by
  unfold isSnaps; infer_instance

end res

end github_com.hashicorp.raft.examples.hraftnet.disk

end Perennial
