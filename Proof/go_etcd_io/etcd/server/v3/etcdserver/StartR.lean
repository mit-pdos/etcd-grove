/-
**The apply thread's resources at a restart's start** (R2d' probe, step 4, 2026-11-06; DRAFT:
nothing here is frozen, `notes/restart-plan.md`, "R2d' Scope (approved 2026-11-06)", its probe).
Lean-first (no Rocq counterpart).

At the etcd pin `673da07c8`, `run` (`server.go:757`) reads the raft storage's snapshot
(`sn, err := s.r.raftStorage.Snapshot()`, `server.go:760`) and starts `ep` at its metadata (`server.go:808-814`): `confState`
its conf state, `appliedi`, `snapi` (disk and memory) its index, `appliedt` its term. At a first start
that snapshot is empty (`memSnapNone`, `rnSnapOnce` at `ai₀ = 0`); at a restart it is the WAL
snapshot `recoverSnapshot` restored into the `MemoryStorage` (`bootstrap.go:449-478`), at Go's start
index `σ.b` with `σ`'s term and conf state, while the backend's ghost log `A₀` runs through its
consistent index (`bootstrap.go:255-273`).

* `rnSnapOnceR`: `Hsnap`'s restart form (DRAFT, not the hub's text): the snapshot at a given index and
  term, with the conf state reporting the voters after the ghost log `A₀` (`epCsAt`) and a lower
  bound of the storage's snapshot (`memSnapLb γs 0`, under an update: a first start's opens
  `memSnapNone`); today's `rnSnapOnce` gives it at `A₀ = []` (`rnSnapOnceR_first`);
* `srvRestartAtR`: `applyStartC`'s restart form (DRAFT): the ghost rows at `A₀` (the applied index
  `ai₀ + |A₀|`, the KV, the rest buckets, `srvApRes`, the consistent index equal to the ghost index),
  Go's rows at Go's start index `ai`; a first start's `applyStartC` gives it (`srvRestartAtR_first`);
* `applyResR_start`: from them and `ep`'s fields, `applyResR` at Go's handed log `P` (`rp = ⟨|P|, A₀⟩`,
  `P <+: A₀`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RunR

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`Hsnap`'s restart form** (DRAFT; `rnSnapOnce`'s, `InvRunRes.lean:334`): `run`'s one call of
the raft storage's `Snapshot()` (`server.go:760` at `673da07c8`) answers a snapshot at index `i` and
term `t` whose conf state is read-only and reports the voters after the ghost log `A₀` (`epCsAt γ A₀`:
at a restart the WAL snapshot's `ConfState`, `bootstrap.go:449-478`; nothing at `A₀ = []`), with a
lower bound of the storage's snapshot (`memSnapLb γs 0`, the writers' handle; a first start's from
`memSnapNone`) and the storage's invariant. -/
def rnSnapOnceR (rg : GName) (cl : Cluster) (nk : GName) (ms : Loc) (γs : MemStorNames) (i t : w64)
    (γ : ServerRaftNames) (A₀ : List EntryModel) : IProp GF :=
  iprop(∀ Φ : val → IProp GF,
    ▷ (∀ (sn pm cs : Loc) (sv : SnapshotM),
      ⌜sv.Metadata'.Index' = i ∧ sv.Metadata'.Term' = t ∧ pm ≠ null ∧ cs ≠ null⌝ -∗
      ownSnapM sn DFrac.discard sv -∗
      sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦□ pm -∗
      pm.[go_etcd_io.raft.v3.raftpb.SnapshotMetadata, go!"ConfState"] ↦□ cs -∗
      epCsOk cs -∗ epCsAt γ A₀ cs -∗ (|==> memSnapLb γs 0) -∗
      (letI : MemStorReg GF := ⟨rg⟩; memStorInv ms γs cl nk) -∗
      Φ (PairV #sn #(GoInterface.nil))) -∗
    WP (App (Val (ms @!! go.GoType.PointerType go_etcd_io.raft.v3.MemoryStorage.ty @!! go!"Snapshot"))
      (Val #())) {{ Φ }})

/-- **A first start's `Hsnap` gives the restart form at `A₀ = []`**. -/
theorem rnSnapOnceR_first (rg : GName) (cl : Cluster) (nk : GName) (ms : Loc) (γs : MemStorNames)
    (i t : w64) (γ : ServerRaftNames) :
    rnSnapOnce (GF := GF) rg cl nk ms γs i t ⊢ rnSnapOnceR rg cl nk ms γs i t γ [] := by
  iintro H
  iunfold rnSnapOnceR
  iintro %Φ HΦ
  iunfold rnSnapOnce at H
  iapply H
  inext
  iintro %sn %pm %cs %sv %h Hsn Hpm Hcs #Hok Hnone Hinv
  ihave #Hca : epCsAt γ [] cs $$ []
  · iunfold epCsAt; ileft; ipureintro; rfl
  ihave Hlb : iprop(|==> memSnapLb γs 0) $$ [Hnone]
  · iapply (memSnapNone_open (GF := GF) γs) $$ Hnone
  iapply HΦ $$ %sn %pm %cs %sv %h Hsn Hpm Hcs Hok Hca Hlb Hinv

/-- **`applyStartC`'s restart form** (DRAFT): the apply thread's resources when `run` starts at Go's
index `ai` (`ep.appliedi`'s first value, the WAL snapshot's index), with the backend's ghost log
`A₀`: the ghost rows at `A₀` (the applied index `g₀ = ai₀ + |A₀|`, `kvRunM`, `srvRest`, `srvApRes`,
the consistent index `ciEff` at `g₀`, `bootstrap.go:255-273`), Go's at `ai` (`loopOk`, the snapshot
resources). The auth state `sa₀` is the one after `A₀` (`kvRunM`'s, with auth on the state
`A₀`'s admin entries leave, which Go's auth store recovers from the backend at the consistent
index), existential so that an auth-on restart whose log changed auth meets it; a first start's is
`srvAuthSt0` (`srvRestartAtR_first`). -/
def srvRestartAtR (C : AuthC) (s : Loc) (γ : ApplyNames) (ci : Loc) (b : GoInterface)
    (E : apply.AEnv GF) (γr : ReadNames) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV) (γw : GName)
    (A₀ : List EntryModel) (ai : w64) : IProp GF :=
  iprop(∃ (st₀ : ApplyState) (a t : w64) (f : Bool) (g₀ : w64) (sa₀ : auth.AuthState),
    applyThread γ st₀ ∗
    ⌜loopOk γ st₀ ai ∧ g₀ = ciEff γ st₀.k ∧ uint.Z g₀ = uint.Z ai₀ + A₀.length⌝ ∗
    applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvBemuReaderAt s E.γbe ∗
    srvWgReader s ∗ srvApplyKVC C s E γw x₀ sa₀ ∗
    srvAppliedOwn γr g₀ ∗ appliedLogAt γr g₀ x₀.log ∗ kvRunM C.isOn γr ai₀ c₀ A₀ x₀ sa₀ ∗
    srvRest E γr A₀ ∗ srvApRes s γr A₀ ∗ srvForceSnapAddr s ↦ f ∗ acTok C (ciEff γ st₀.k) ∗
    srvSnapOwn s ci E γr γ ai)

/-- **A first start's `applyStartC` is the restart form at `A₀ = []`** (Go's index `ai₀`). -/
theorem srvRestartAtR_first (C : AuthC) (s : Loc) (γ : ApplyNames) (ci : Loc) (b : GoInterface)
    (E : apply.AEnv GF) (γr : ReadNames) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV) (γw : GName) :
    applyStartC (GF := GF) C s γ ci b E γr ai₀ c₀ x₀ γw ∗ ⌜c₀ = ai₀⌝ ⊢
      srvRestartAtR C s γ ci b E γr ai₀ c₀ x₀ γw [] ai₀ := by
  iintro ⟨H, %hc⟩
  iunfold applyStartC at H
  icases H with ⟨%st₀, %a, %t, %f, Hth, %Hok, Hbe, Hca, Hlg, Hbm, Hwg, Hkv, Hao, Hal, Hkr, Hrest,
    Hap, Hfs, Htok, Hso⟩
  iunfold srvRestartAtR
  iexists st₀, a, t, f, ai₀, srvAuthSt0
  iframe Hth Hbe Hca Hlg Hbm Hwg Hkv Hao Hal Hkr Hrest Hap Hfs Htok Hso
  ipureintro
  exact ⟨Hok.1, by rw [← hc]; exact Hok.2, by simp⟩


/-- **A9's texts for `isServerRunC`** (R2d'a A9, Q24 (c); DRAFT, not yet in the hub: under Q20 the
hub edit lands with A10's proof of `run`'s restart branch). Three of `isServerRunC`'s conjuncts at a
restart, **`σ.b = 0` only**: a restart before the member's first WAL snapshot, so that nothing was
handed before the start (`γn.pre = []`, `ai₀ = 0`: `rnEnvOk` unchanged), Go's log restarts at index 0
and the backend's ghost log `A₀` (`γn.a0`, A6's field) is replayed through the window `(0, |A₀|]`.
`σ.b > 0` is R2d'b's, with the raft side's restart data (Q24 (a)).
- `%HEr`: today's conjuncts with `γn.a0 = A₀` for some `A₀` (was `γn.a0 = []`), `A₀`'s entries
  normal or conf changes, and room past it (`ai₀ + |A₀| + 1 < 2^64`);
- `Hsnap`: `rnSnapOnceR` at index `ai₀` (`= 0`), the conf state at `A₀`;
- `Hstart`: `srvRestartAtR` at `A₀`, Go's index `ai₀`.
At `A₀ = []` they are today's (`srvRunRestartR_first`). -/
def srvRunRestartR (C : AuthC) (s : Loc) (γ : ApplyNames) (ci : Loc) (b : GoInterface)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames)
    (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (γw : GName) : IProp GF :=
  iprop(∃ A₀ : List EntryModel,
    ⌜Er.C = srvCM C.isOn ρ E ai₀ c₀ x₀ ∧ Er.γr = γr ∧
      (uint.Z c₀ ≤ uint.Z ai₀ ∧ γn.pre = [] ∧ ai₀ = W64 0) ∧
      γn.a0 = A₀ ∧ (∀ m ∈ A₀, m.typ = W32 0 ∨ m.typ = W32 1) ∧
      uint.Z ai₀ + A₀.length + 1 < 2 ^ 64⌝ ∗
    (∃ ms : Loc, rnRaftStorageAddr (srvRAddr s) ↦□ ms ∗
      rnSnapOnceR γn.node.reg γn.node.cl γn.key ms γn.γs ai₀ at₀ γr.raft A₀) ∗
    srvRestartAtR C s γ ci b E γr ai₀ c₀ x₀ γw A₀ ai₀)

/-- **A first start's conjuncts give A9's** (`A₀ = []`): today's `%HEr` (with A6's `γn.a0 = []`),
`Hsnap` and `Hstart`. -/
theorem srvRunRestartR_first (C : AuthC) (s : Loc) (γ : ApplyNames) (ci : Loc) (b : GoInterface)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames)
    (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (γw : GName)
    (hEr : Er.C = srvCM C.isOn ρ E ai₀ c₀ x₀ ∧ Er.γr = γr ∧
      (uint.Z c₀ ≤ uint.Z ai₀ ∧ γn.pre = [] ∧ ai₀ = W64 0) ∧ γn.a0 = []) :
    (∃ ms : Loc, rnRaftStorageAddr (srvRAddr s) ↦□ ms ∗
        rnSnapOnce (GF := GF) γn.node.reg γn.node.cl γn.key ms γn.γs ai₀ at₀) ∗
      applyStartC C s γ ci b E γr ai₀ c₀ x₀ γw ⊢
    srvRunRestartR C s γ ci b E ρ γr Er γn ai₀ at₀ c₀ x₀ γw := by
  obtain ⟨h1, h2, ⟨hc, hp, ha⟩, h4⟩ := hEr
  have hc0 : c₀ = ai₀ := by subst ha; word
  iintro ⟨⟨%ms, #Hms, Hsnap⟩, Hst⟩
  iunfold srvRunRestartR
  iexists []
  isplitr
  · ipureintro
    refine ⟨h1, h2, ⟨hc, hp, ha⟩, h4, by simp, ?_⟩
    subst ha; simp <;> word
  isplitl [Hsnap]
  · iexists ms
    iframe Hms
    iapply rnSnapOnceR_first $$ Hsnap
  iapply srvRestartAtR_first $$ [Hst]
  iframe Hst
  ipureintro; exact hc0

end defs

section start
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The rest buckets at the restart's start**: `srvRest` at the backend's log is `srvRestR` at
Go's handed log `P` (`rp = ⟨|P|, A₀⟩`; inside the window, the replay arm at the model's image). -/
theorem srvRestR_start (E : apply.AEnv GF) (γr : ReadNames) (P A₀ : List EntryModel)
    (hP : P <+: A₀) : srvRest (GF := GF) E γr A₀ = srvRestR E γr ⟨P.length, A₀⟩ P := by
  by_cases h : P.length < A₀.length
  · rw [srvRestR_in _ _ _ _ h]
    unfold restReplay
    simp only [List.drop_length, List.foldl_nil]
    rw [srvRestRp_model]
  · have hl := hP.length_le
    have he : P = A₀ := hP.eq_of_length (by omega)
    subst he
    rw [srvRestR_past _ _ _ _ (Nat.le_refl _)]

/-- **`run`'s loop resources at a restart's start** (R2d' probe, step 4; DRAFT): from the restart
form of `applyStartC` (`srvRestartAtR`, at Go's start index `ai = ai₀ + |P|`), `ep`'s fields as `run`
sets them from the storage's snapshot (`server.go:808-814` at `673da07c8`: `appliedi`, `snapi` and
`diskSnapshotIndex` at `ai`, `appliedt` the handed log's last term, `confState` with what
`rnSnapOnceR` gives: `epCsOk`, `epCsAt` at `A₀`, `memSnapLb γs 0`), and the restart point's facts
(`P <+: A₀`; `A₀`'s entries normal or conf changes; room past `A₀`; `c₀ ≤ ai₀`): `applyResR` at `P`. -/
theorem applyResR_start (K : AuthC) (C : ApplyCtx GF) (TM : MetaCI → IProp GF) (P A₀ : List EntryModel)
    (ai at' : w64) (cs : Loc)
    (hP : P <+: A₀) (hai : uint.Z ai = uint.Z C.ai₀ + P.length) (hlt : lastTermIs P at')
    (hc₀ : uint.Z C.c₀ ≤ uint.Z C.ai₀) (hty : ∀ m ∈ A₀, m.typ = W32 0 ∨ m.typ = W32 1)
    (hbnd : uint.Z C.ai₀ + A₀.length + 1 < 2 ^ 64) (hρ : C.ρ.raft = C.γr.raft) :
    isServerC (GF := GF) K C.s C.γ C.ci TM C.E C.ρ C.γr ∗
      epAppliedIAddr C.ep ↦ ai ∗ epAppliedTAddr C.ep ↦ at' ∗
      epConfStateAddr C.ep ↦ cs ∗ epCsOk cs ∗ epCsAt C.ρ.raft A₀ cs ∗
      epDiskSnapAddr C.ep ↦ ai ∗ epMemSnapAddr C.ep ↦ ai ∗
      rnRaftStorageAddr (srvRAddr C.s) ↦□ C.ms ∗ memSnapLb C.γs 0 ∗
      (∃ kv : GoInterface, srvKVAddr C.s ↦□ kv ∗ txn.isKV kv C.E.s C.E.γ) ∗
      rnWalTokA C.rn (srvRAddr C.s) (1 : Qp).half ∗ (∃ w : Nat, srvWTTaken C.wt.cnt w) ∗
      srvRestartAtR K C.s C.γ C.ci C.b C.E C.γr C.ai₀ C.c₀ C.x₀ C.γw A₀ ai ⊢
    applyResR K C ⟨P.length, A₀⟩ P := by
  iintro ⟨#Hsrv, Hai, Hat, Hcsa, #Hcsok, #Hcsat, Hdsi, Hmsi, #Hms, #Hslb, Hkvf, Hwt, Hwtt, Hrs⟩
  iunfold srvRestartAtR at Hrs
  icases Hrs with ⟨%st₀, %a, %t, %f, %g₀, %sa₀, Hth, %Hok, Hbe, Hca, Hlg, Hbm, Hwg, Hkv, Hao, Hal, Hkr,
    Hrest, Hap, Hfs, Htok, Hso⟩
  obtain ⟨Hloop, Hce, Hg⟩ := Hok
  icases kvRunM_lbR _ _ _ _ _ _ _ $$ Hkr with ⟨#HlbA, Hkr⟩
  have hgh : ghostOf ⟨P.length, A₀⟩ P = A₀ := ghostOf_in ⟨P.length, A₀⟩ P hP
  iunfold applyResR
  iexists ⟨C.γ, TM, C.E, C.b⟩, st₀, ai, at', a, t, cs, C.x₀, sa₀, g₀
  simp only [hgh]
  rw [← srvRestR_start _ _ P A₀ hP]
  isplitr
  · ipureintro; exact beSucc_refl C.γ C.E
  ihave Hcs : epConfState C.ep cs $$ [Hcsa]
  · iunfold epConfState; iframe Hcsa Hcsok
  ihave Hss : srvSnapState C.s C.ep C.ms C.γs ai (W64 0) $$ [Hdsi Hmsi Hfs]
  · iunfold srvSnapState
    iexists ai, ai, f
    iframe Hdsi Hmsi Hfs Hms
    isplitr
    · ipureintro; exact ⟨Int.le_refl _, Int.le_refl _⟩
    iExactEq Hslb; rfl
  ihave #HlbA' : srvRLogLb C.ρ.raft A₀ $$ []
  · rw [hρ]; iexact HlbA
  iframe Hsrv Hai Hat Hcs Hcsat Hss Hth Hbe Hca Hlg Hbm Hwg Hkv Hao Hal Hkr Hrest Hap HlbA' Hkvf Hwt
  iframe Hwtt Htok Hso
  ipureintro
  have hl := hP.length_le
  refine ⟨Hloop, hai, Or.inr ⟨?_, ?_⟩, ?_, hlt, Hg, Nat.le_refl _, hty, ?_, hbnd⟩
  · omega
  · rw [← Hce]; omega
  · rw [← Hce]; omega
  · rw [← Hce]; omega

end start

end EtcdGrove
end Perennial
