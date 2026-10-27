/-
The certificate registry of a `MemoryStorage` tied to raft's names (D22 S-b′2, 2026-10-20; a
module of its own since D22 S-b′3, so that an application's storage instance -- the key-value
store's, `KVStorageInstance.lean` -- uses it without `MemstorageInstance.lean`'s links): the
invariant `memCertInv γ γs` whose entries carry raft's certificates (`certElemOk`), its
allocation from `NewMemoryStorage`'s `memCertAuth`, and reading (`memCert_read`) and registering
(`memCert_register`, at any term `memCert_registerAny`) through it. `memStorCertOk_intro`
(`MemstorageInstance.lean`) builds `storCertOk` from it for a bare `MemoryStorage`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvMemstorage
public import Proof.go_etcd_io.raft.v3.StepGhostMode

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section certLink
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-! ### The certificate registry's link to raft's names (D22 S-b′2, 2026-10-20)

The application, knowing raft's names `γ`, puts the registry's authority (`memCertAuth`,
`NewMemoryStorage`'s) in an invariant whose entries carry raft's certificates (`memCertInv`):
then a registered snapshot is certified for raft (`memCert_read`) and a certified one can be
registered (`memCert_register`; at any term, `memCert_registerAny`, for `CreateSnapshot`), and
the storage meets `storCertOk γ` (`memStorCertOk_intro`). -/

/-- What a registry entry carries: raft's certificates of its snapshot (D22 S-r, 2026-10-21: the
configuration's and the data's, `raftSnapCertD`), at every term for an any-term entry. -/
def certElemOk (γ : RaftNames) (e : CertKey) : IProp GF :=
  if e.2 then iprop(∀ t : w64, raftSnapCertD γ ⟨⟨t, e.1.sid.index'⟩, e.1.cl, e.1.al, e.1.dat⟩)
  else raftSnapCertD γ e.1

theorem certElemOk_covers (γ : RaftNames) (e : CertKey) (k : SnapTrip) (h : certCovers e k) :
    certElemOk (GF := GF) γ e ⊢ raftSnapCertD γ k := by
  unfold certElemOk
  unfold certCovers at h
  split
  · rename_i he
    rw [if_pos he] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    iintro H
    ihave H := H $$ %k.sid.term'
    have : (⟨⟨k.sid.term', e.1.sid.index'⟩, e.1.cl, e.1.al, e.1.dat⟩ : SnapTrip) = k := by
      cases k with | mk sid cl al dat => cases sid; simp only at h1 h2 h3 h4; subst h1 h2 h3 h4; rfl
    rw [this]; iexact H
  · rename_i he
    rw [if_neg he] at h
    subst h
    exact .rfl

instance certElemOk_persistent (γ : RaftNames) (e : CertKey) :
    Persistent (certElemOk (GF := GF) γ e) := by
  unfold certElemOk; split <;> infer_instance

instance certElemOk_timeless (γ : RaftNames) (e : CertKey) :
    Timeless (certElemOk (GF := GF) γ e) := by
  unfold certElemOk; split <;> infer_instance

/-- The registry's invariant, at raft's names `γ`. -/
def memCertInv (γ : RaftNames) (γs : MemStorNames) : IProp GF :=
  inv raftCertN iprop(∃ L : List CertKey, monoListAuthOwn γs.cert 1 L ∗ [∗list] e ∈ L, certElemOk γ e)

instance memCertInv_persistent (γ : RaftNames) (γs : MemStorNames) :
    Persistent (memCertInv (GF := GF) γ γs) := by
  unfold memCertInv; infer_instance

/-- The application allocates it from the empty registry's authority. -/
theorem memCertInv_alloc (γ : RaftNames) (γs : MemStorNames) (E : CoPset) :
    ⊢ memCertAuth (GF := GF) γs ={E}=∗ memCertInv γ γs := by
  iintro Ha
  unfold memCertInv
  iapply inv_alloc
  inext
  iexists ([] : List CertKey)
  iunfold memCertAuth at Ha
  isplitl [Ha]
  · iexact Ha
  iapply (BigSepL.bigSepL_nil (Φ := fun _ e => certElemOk (GF := GF) γ e)).2
  iempintro

/-- A registered snapshot is certified for raft. -/
theorem memCert_read (γ : RaftNames) (γs : MemStorNames) (k : SnapTrip) (E : CoPset)
    (hE : ↑raftCertN ⊆ E) :
    ⊢ memCertInv (GF := GF) γ γs -∗ memStorCert γs k ={E}=∗ raftSnapCertD γ k := by
  iintro #Hinv #Hc
  iunfold memStorCert at Hc
  icases Hc with ⟨%L0, #Hlb, %Hin⟩
  obtain ⟨e, he, hc⟩ := Hin
  unfold memCertInv
  iinv Hinv with ⟨%L, >Ha, >#Hall⟩ Hclose
  icases mono_list_auth_lb_valid _ _ _ _ $$ Ha Hlb with %Hv
  obtain ⟨-, Hpre⟩ := Hv
  have he' : e ∈ L := Hpre.subset he
  ihave ⟨#He, -⟩ := BigSepL.bigSepL_mem_acc he' $$ Hall
  ihave #Hk := certElemOk_covers γ e k hc $$ He
  imod Hclose $$ [Ha] with -
  · inext
    iexists L
    iframe Ha Hall
  imodintro
  iexact Hk

/-- A certified snapshot can be registered (by anyone holding raft's certificate). -/
theorem memCert_register (γ : RaftNames) (γs : MemStorNames) (k : SnapTrip) (E : CoPset)
    (hE : ↑raftCertN ⊆ E) :
    ⊢ memCertInv (GF := GF) γ γs -∗ raftSnapCertD γ k ={E}=∗ memStorCert γs k := by
  iintro #Hinv #Hk
  unfold memCertInv
  iinv Hinv with ⟨%L, >Ha, >#Hall⟩ Hclose
  imod monoListAuthOwn_update_app [((k, false) : CertKey)] $$ Ha with ⟨Ha, #Hlb⟩
  ihave #He : certElemOk (GF := GF) γ ((k, false) : CertKey) $$ []
  · simp only [certElemOk, Bool.false_eq_true, ↓reduceIte]
    iexact Hk
  imod Hclose $$ [Ha] with -
  · inext
    iexists L ++ [((k, false) : CertKey)]
    iframe Ha
    iapply BigSepL.bigSepL_snoc.2
    iframe Hall He
  imodintro
  iapply memStorCert_of_lb γs (L ++ [((k, false) : CertKey)]) (k, false) k (by simp)
    (by simp [certCovers]) $$ Hlb

/-- ... at any term (an any-term entry): what `CreateSnapshot`'s premise asks. -/
theorem memCert_registerAny (γ : RaftNames) (γs : MemStorNames) (i : w64) (cl : CSLists)
    (al : Bool) (d : List w8) (E : CoPset) (hE : ↑raftCertN ⊆ E) :
    ⊢ memCertInv (GF := GF) γ γs -∗ (□ ∀ t : w64, raftSnapCertD γ ⟨⟨t, i⟩, cl, al, d⟩) ={E}=∗
      □ ∀ t : w64, memStorCert γs ⟨⟨t, i⟩, cl, al, d⟩ := by
  iintro #Hinv #Hk
  unfold memCertInv
  iinv Hinv with ⟨%L, >Ha, >#Hall⟩ Hclose
  imod monoListAuthOwn_update_app [((⟨⟨W64 0, i⟩, cl, al, d⟩, true) : CertKey)] $$ Ha with ⟨Ha, #Hlb⟩
  ihave #He : certElemOk (GF := GF) γ ((⟨⟨W64 0, i⟩, cl, al, d⟩, true) : CertKey) $$ []
  · simp only [certElemOk, ↓reduceIte]
    iexact Hk
  imod Hclose $$ [Ha] with -
  · inext
    iexists L ++ [((⟨⟨W64 0, i⟩, cl, al, d⟩, true) : CertKey)]
    iframe Ha
    iapply BigSepL.bigSepL_snoc.2
    iframe Hall He
  imodintro
  imodintro
  iintro %t
  iapply memStorCert_of_lb γs (L ++ [((⟨⟨W64 0, i⟩, cl, al, d⟩, true) : CertKey)])
    (⟨⟨W64 0, i⟩, cl, al, d⟩, true) ⟨⟨t, i⟩, cl, al, d⟩ (by simp) (by simp [certCovers]) $$ Hlb

end certLink

end EtcdGrove
end Perennial
