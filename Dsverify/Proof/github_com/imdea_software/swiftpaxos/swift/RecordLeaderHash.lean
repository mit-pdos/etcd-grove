/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/RecordLeaderHash.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`r.recordLeaderHash(x, s, hs)` (swift.go; the `ackHash` arm's callee, `leaderAckHash`), total
(round 18, sv-swc; notes/prove-swift.md §22):

* `x` has a proposal in `proposes`: `r.updateLogs(p.Command, x, s, hs)` (one `HashLog.Update` per
  key of the command). Its premise `swift.leadUpdOk` (the command is a put or a get, and
  `Update`'s effect keeps `hlogOk` of its key) follows from the leader's numbering (change log
  C22, M3, round 19: `swift.leadUpdOk_of`, from `sp.num_paths`); it is stated per command through
  `cmdIs` (the proposal's `propIs` carries `cmdIs γ x c`).
* `x` has no proposal: `pendingHashUpds[x] = &UpdateEntry{hs, s}` (`swift.pendOwnH`, Local.lean:
  each entry read-only with its hash's path and the leader's number and path of the command, for
  the later `recordLeaderHash` of `handleProposal`).

`swift.Replica.updateLogs.specT` is a hypothesis (its proof: `keysOf` of a put/get is its key,
the `hlog` map's lookup/insert of a fresh `HL.init`, `HashLog.Update.spec`; not done).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DepHashPure

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-- What the leader's numbering gives (change log C22, see the file header): `c` is a put or a
get, and `Update(x, s, h)` (of path `P`) keeps `hlogOk` of `c`'s key. -/
def swift.leadUpdOk (ld : Bool) (hd : sp.Seq) (K : sp.CmdId → Prop)
    (Λ : w64 → w64 → List sp.CmdId → Prop) (x : sp.CmdId) (s : w64) (h : sp.Hash)
    (P : List sp.CmdId) (c : sp.Cmd) : Prop :=
  (c.isPut ∨ c.isGet) ∧
    ∀ σ, swift.hlogOk ld hd K Λ c.key σ → swift.hlogOk ld hd K Λ c.key (σ.updateTo x s h P true)

/-- **`leadUpdOk` from the leader's numbering** (change log C22, M3; the facts `sp.num_paths`
gives): at a follower, an acknowledgement of `x` (in `K`: proposed here) with the leader's number
`s ≥ 0` and path `P` (ending with `x`, recorded in `Λ`), the paths of `Λ` following the
numbers. -/
theorem swift.leadUpdOk_of (hd : sp.Seq) (K : sp.CmdId → Prop)
    (Λ : w64 → w64 → List sp.CmdId → Prop) (x : sp.CmdId) (s : w64) (h : sp.Hash)
    (P : List sp.CmdId) (c : sp.Cmd) (hpg : c.isPut ∨ c.isGet) (hK : K x) (hx : x ∈ P)
    (h0 : 0 ≤ sint.Z s) (hΛ : Λ c.key s P)
    (hord : ∀ s' P', Λ c.key s' P' → (sint.Z s ≤ sint.Z s' → x ∈ P') ∧
      (sint.Z s' < sint.Z s → ∀ z ∈ P', z ∈ P)) :
    swift.leadUpdOk false hd K Λ x s h P c := by
  refine ⟨hpg, fun σ hσ => ?_⟩
  obtain ⟨h1, h2, h3, -, h5⟩ := hσ
  unfold swift.hlog.HL.updateTo
  by_cases hp : x ∈ σ.pending
  · rw [if_pos hp]
    by_cases hlt : sint.Z σ.synced < sint.Z s
    · rw [if_pos hlt]
      refine ⟨fun z hz => h1 z (List.mem_of_mem_erase hz), fun z hz => ?_, h3,
        fun e => absurd e Bool.false_ne_true, Or.inr hΛ⟩
      rcases h2 z hz with hz' | hz'
      · by_cases e : z = x
        · subst e; right; exact hx
        · left; exact (List.mem_erase_of_ne e).mpr hz'
      · right
        rcases h5 with ⟨-, hb⟩ | hb
        · rw [hb] at hz'; cases hz'
        · exact (hord _ _ hb).2 hlt z hz'
    · rw [if_neg hlt]
      refine ⟨fun z hz => h1 z (List.mem_of_mem_erase hz), fun z hz => ?_, h3,
        fun e => absurd e Bool.false_ne_true, h5⟩
      rcases h2 z hz with hz' | hz'
      · by_cases e : z = x
        · subst e
          right
          rcases h5 with ⟨hneg, -⟩ | hb
          · omega
          · exact (hord _ _ hb).1 (by omega)
        · left; exact (List.mem_erase_of_ne e).mpr hz'
      · right; exact hz'
  · rw [if_neg hp, if_pos rfl]
    refine ⟨h1, h2, fun y hy => ?_, fun e => absurd e Bool.false_ne_true, h5⟩
    by_cases e : y = x
    · right; rw [e]; exact hK
    · simp only [e, if_false] at hy
      exact h3 y hy


section mono
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS]
variable [swift.Assumptions]

/-- `hlogOwn` is monotone in `K` and `Λ` (change log C22). -/
theorem swift.hlogOwn_mono (hm : Loc) (hM : GMap w64 Loc) (ld : Bool) (hd : sp.Seq)
    {K K' : sp.CmdId → Prop} {Λ Λ' : w64 → w64 → List sp.CmdId → Prop}
    (hK : ∀ y, K y → K' y) (hΛ : ∀ k s P, Λ k s P → Λ' k s P) :
    swift.hlogOwn hm hM ld hd K Λ ⊢ swift.hlogOwn hm hM ld hd K' Λ' := by
  unfold swift.hlogOwn
  iintro ⟨Hm, Hents, %Hc⟩
  iframe Hm
  isplitl [Hents]
  · iapply (BigSepM.bigSepM_mono_of_forall (Φ := fun k l => swift.hlogEnt ld hd K Λ k l)
      (Ψ := fun k l => swift.hlogEnt ld hd K' Λ' k l) (fun {k l} => ?_)) $$ Hents
    unfold swift.hlogEnt
    iintro ⟨%σ, Ho, %Hok⟩
    iexists σ; iframe Ho; ipureintro
    exact swift.hlog.hlogOk_mono hK hΛ Hok
  · ipureintro; exact Hc

end mono

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions]

/-- `r.updateLogs(cmd, x, s, hs)` for a put or a get whose `Update` keeps its key's `hlogOk`
(`leadUpdOk`). -/
abbrev swift.Replica.updateLogs.specT : Prop :=
  ∀ (rp hm : Loc) (hM : GMap w64 Loc) (ld : Bool) (hd : sp.Seq) (K : sp.CmdId → Prop)
    (Λ : w64 → w64 → List sp.CmdId → Prop) (c : sp.Cmd) (vs : GoSlice)
    (dq : DFrac) (x : swift.CommandId) (sq : w64) (hs : GoSlice) (H : swift.SHash)
    (P : List sp.CmdId),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      swift.fld rp go!"hlog" ↦ hm ∗ swift.hlogOwn hm hM ld hd K Λ ∗ vs ↦*{dq} c.val ∗
      hs ↦*□ [H] ∗ sp.startHash P H.H'.arr ∗
      ⌜swift.leadUpdOk ld hd K Λ (toCmdId x) sq H.H'.arr P c⌝ }}
    (App (App (App (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"updateLogs"))
      (Val #(state.Command.mk c.op c.key vs))) (Val #x)) (Val #sq)) (Val #hs))
  {{ (hM' : GMap w64 Loc), RET #();
      swift.fld rp go!"hlog" ↦ hm ∗ swift.hlogOwn hm hM' ld hd K Λ ∗ vs ↦*{dq} c.val }}

/-- **`r.recordLeaderHash(x, s, hs)`, total** (see the file header; change log C22, at a follower:
the hash logs over `K = propsK pM` and the leader's synced paths `Λ` (`ldSound`), the
acknowledgement's number and path of ballot `b`'s leader; with a proposal, `Λ` grows by it
(`leadUpd_ghost`); the pending entries with the leader's number and path). -/
abbrev swift.Replica.recordLeaderHash.specT : Prop :=
  ∀ (γ : sp.Names) (γc γm γl : GName) (N : Nat) (fr : Bool) (l : List GoString)
    (rp hm pm pd : Loc) (hM : GMap w64 Loc) (pM pdM : GMap swift.CommandId Loc)
    (hd : sp.Seq) (Λ : w64 → w64 → List sp.CmdId → Prop) (b : Nat)
    (x : swift.CommandId) (sq : w64) (hs : GoSlice) (H : swift.SHash) (P : List sp.CmdId),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      sp.inv γ γc γm γl ∗ sp.cfg γc γm N fr l ∗
      swift.fld rp go!"hlog" ↦ hm ∗ swift.hlogOwn hm hM false hd (swift.propsK pM) Λ ∗
      swift.ldSound γ (sp.leaderOf N b) b Λ ∗
      swift.fld rp go!"proposes" ↦ pm ∗ swift.propsOwn γ pm pM ∗
      swift.fld rp go!"pendingHashUpds" ↦ pd ∗ swift.pendOwnH γ (sp.leaderOf N b) b pd pdM ∗
      hs ↦*□ [H] ∗ sp.startHash P H.H'.arr ∗
      sp.numIs γ (sp.leaderOf N b) b (toCmdId x) sq ∗
      sp.pathIs γ (sp.leaderOf N b) b (toCmdId x) P }}
    (App (App (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"recordLeaderHash"))
      (Val #x)) (Val #sq)) (Val #hs))
  {{ (hM' : GMap w64 Loc) (pdM' : GMap swift.CommandId Loc)
      (Λ' : w64 → w64 → List sp.CmdId → Prop), RET #();
      swift.fld rp go!"hlog" ↦ hm ∗ swift.hlogOwn hm hM' false hd (swift.propsK pM) Λ' ∗
      swift.ldSound γ (sp.leaderOf N b) b Λ' ∗
      swift.fld rp go!"proposes" ↦ pm ∗ swift.propsOwn γ pm pM ∗
      swift.fld rp go!"pendingHashUpds" ↦ pd ∗ swift.pendOwnH γ (sp.leaderOf N b) b pd pdM' ∗
      ⌜(pM !! x).isSome → pdM' = pdM⌝ }}

end specs

section ghost
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS]
variable [swift.Assumptions]

instance swift.ldSound_persistent (γ : sp.Names) (L b : Nat)
    (Λ : w64 → w64 → List sp.CmdId → Prop) : Persistent (swift.ldSound γ L b Λ) := by
  unfold swift.ldSound; infer_instance

/-- `Λ` with one more entry. -/
def swift.ΛAdd (Λ : w64 → w64 → List sp.CmdId → Prop) (k s : w64) (P : List sp.CmdId) :
    w64 → w64 → List sp.CmdId → Prop :=
  fun k' s' P' => Λ k' s' P' ∨ (k' = k ∧ s' = s ∧ P' = P)

/-- **The leader's acknowledgement at a follower** (change log C22, M3): ballot `b`'s leader
numbered `x` (command `c`, of `K`) with `s`, its path `P`: `Λ` extended with it stays sound, and
`Update(x, s, h)` keeps the hash logs (`leadUpdOk`). -/
theorem swift.leadUpd_ghost (E : CoPset) (hE : ↑sp.spN ⊆ E) (γ : sp.Names) (γc γm γl : GName)
    (N : Nat) (fr : Bool) (l : List GoString) (b : Nat) (Λ : w64 → w64 → List sp.CmdId → Prop)
    (x : sp.CmdId) (c : sp.Cmd) (s : w64) (h : sp.Hash) (P : List sp.CmdId) (hd : sp.Seq)
    (K : sp.CmdId → Prop) (hK : K x) (hpg : c.isPut ∨ c.isGet) :
    sp.inv γ γc γm γl ∗ sp.cfg γc γm N fr l ∗ swift.ldSound γ (sp.leaderOf N b) b Λ ∗
      sp.numIs γ (sp.leaderOf N b) b x s ∗ sp.pathIs γ (sp.leaderOf N b) b x P ∗
      sp.cmdIs γ x c ⊢
    |={E}=> swift.ldSound γ (sp.leaderOf N b) b (swift.ΛAdd Λ c.key s P) ∗
      ⌜swift.leadUpdOk false hd K (swift.ΛAdd Λ c.key s P) x s h P c⌝ := by
  iintro ⟨#Hinv, #Hcfg, #Hs, #Hn, #Hp, #Hc⟩
  iunfold swift.ldSound at Hs
  imod sp.num_paths_all E hE N fr l b x s P c Λ $$ [Hinv Hcfg Hn Hp Hc Hs] with %Hr
  · iframe Hinv Hcfg Hn Hp Hc Hs
  obtain ⟨h0, hlast, hall⟩ := Hr
  imodintro
  isplitl
  · iunfold swift.ldSound
    imodintro
    iintro %k' %s' %P' %H
    rcases H with H | ⟨rfl, rfl, rfl⟩
    · iapply Hs $$ %k' %s' %P' %H
    · iexists x, c
      iframe Hn Hp Hc
      ipureintro; rfl
  · ipureintro
    refine swift.leadUpdOk_of hd K _ x s h P c hpg hK (List.mem_of_getLast? hlast) h0
      (Or.inr ⟨rfl, rfl, rfl⟩) (fun s' P' hΛ => ?_)
    rcases hΛ with hΛ | ⟨-, rfl, rfl⟩
    · obtain ⟨h1, h2⟩ := hall s' P' hΛ
      refine ⟨fun hle => (h1 hle).subset (List.mem_of_getLast? hlast), fun hlt z hz => ?_⟩
      exact (h2 (by omega)).subset hz
    · exact ⟨fun _ => List.mem_of_getLast? hlast, fun hlt => by omega⟩

end ghost

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions]

theorem swift.Replica.recordLeaderHash.wp_proofT
    (wp_upd : swift.Replica.updateLogs.specT (hG := hG)) :
    swift.Replica.recordLeaderHash.specT (hG := hG) := by
  intro γ γc γm γl N fr l rp hm pm pd hM pM pdM hd Λ b x sq hs H P
  haveI := swift.hlog.cmdId_intoValInj (sem := sem)
  wp_start as ⟨#Hinv, #Hcfg, Hhf, Hhlog, #HΛ, Hpf, Hprops, Hpdf, Hpend, #Hhs, #HP, #Hnum, #Hpath⟩
  iunfold swift.propsOwn at Hprops
  icases Hprops with ⟨Hpm, Hpents⟩
  wp_auto
  wp_apply wp_map_lookup2 $$ [$Hpm] as Hpm
  cases hx : pM !! x with
  | none =>
    try simp only [hx]
    wp_if_destruct
    · simp_all
    · -- no proposal: the update waits in `pendingHashUpds`
      iunfold swift.pendOwnH at Hpend
      icases Hpend with ⟨Hpdm, Hpdents⟩
      irename «$r0» => Hu
      ipersist Hu
      wp_apply wp_mapInsert $$ [$Hpdm] as Hpdm
      iapply HΦ

      iframe Hhf Hhlog HΛ Hpf Hpdf
      isplitl [Hpm Hpents]
      · iunfold swift.propsOwn; iframe
      isplitl
      · iunfold swift.pendOwnH
        iframe
        iapply (BigSepM.bigSepM_insert_elim (Φ := fun (x : swift.CommandId) (u : Loc) =>
          iprop(∃ (sl : GoSlice) (sq : w64) (H : swift.SHash) (P : List sp.CmdId),
            u ↦□ swift.UpdateEntry.mk sl sq ∗ sl ↦*□ [H] ∗ sp.startHash P H.H'.arr ∗
            sp.numIs γ (sp.leaderOf N b) b (toCmdId x) sq ∗
            sp.pathIs γ (sp.leaderOf N b) b (toCmdId x) P)))
        · iexists hs, sq, H, P; iframe #
        · iexact Hpdents
      ipureintro; simp
  | some gp =>
    try simp only [hx]
    wp_if_destruct
    rotate_left
    · simp_all
    ihave ⟨Hgp, Hclose⟩ := BigSepM.bigSepM_lookup_acc
      (show Iris.Std.PartialMap.get? pM x = some gp from hx) $$ Hpents
    icases Hgp with ⟨%c, #Hpi⟩
    ihave #Hpi2 := Hpi
    iunfold swift.propIs at Hpi2
    icases Hpi2 with ⟨%p, %w, %mu, %addr, %ts, %vs, #Hgp, #Hp, #Hvs, #Hc, %Hwf⟩
    iStructNamed Hgp
    iStructNamed Hp
    -- the leader's numbering (change log C22): `Λ` grows by the acknowledgement
    iapply fupd_wp
    ihave Hcok := sp.cmdIs_ok (γ := γ) (γc := γc) (γm := γm) (γl := γl) (toCmdId x) c $$ [Hinv Hc]
    · iframe Hinv Hc
    imod (fupd_mask_mono (E1 := ↑sp.spN) (E2 := ⊤) (by simp)) $$ Hcok with %Hcok
    have hK : swift.propsK pM (toCmdId x) := by
      unfold swift.propsK
      rw [show ofCmdId (toCmdId x) = x from rfl, hx]; rfl
    imod swift.leadUpd_ghost ⊤ (by simp) γ γc γm γl N fr l b Λ (toCmdId x) c sq H.H'.arr P hd
        (swift.propsK pM) hK Hcok.1 $$ [Hinv Hcfg HΛ Hnum Hpath Hc] with ⟨#HΛ', %Hlu⟩
    · iframe Hinv Hcfg HΛ Hnum Hpath Hc
    imodintro
    ihave Hhlog := swift.hlogOwn_mono hm hM false hd (K' := swift.propsK pM)
      (Λ' := swift.ΛAdd Λ c.key sq P) (fun _ h => h) (fun _ _ _ h => Or.inl h) $$ Hhlog
    simp only [Option.getD_some]
    wp_auto
    wp_apply wp_upd rp hm hM false hd (swift.propsK pM) (swift.ΛAdd Λ c.key sq P) c vs
        DFrac.discard x sq hs H P $$ [$Hhf $Hhlog]
      as %hM' ⟨Hhf, Hhlog, -⟩
    · iframe #; ipureintro; exact Hlu
    iapply HΦ
    iframe
    iframe HΛ'
    isplitl [Hpm Hclose]
    · iunfold swift.propsOwn
      iframe
      iapply Hclose
      iexists c; iexact Hpi
    ipureintro; intro; rfl

end proof

end Perennial.github_com.imdea_software.swiftpaxos
