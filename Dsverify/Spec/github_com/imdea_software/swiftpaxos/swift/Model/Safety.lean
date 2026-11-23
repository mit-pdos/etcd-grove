/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/swift/Model/Safety.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The safety of one recovery: the recovery's context (Ctx), the potential that orders the kept graph, the three facts of a kept command (Safe) for a class-0 command (safe_K0) and for one kept for the fast path (safe_fast), and the MSync's order (safe_sync).
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Model.Graph

@[expose] public section

noncomputable section

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace Perennial.github_com.imdea_software.swiftpaxos

namespace sp

theorem recPos_inj (r0 : Nat × Report) (a b : CmdId) (i : Nat) (ha : recPos r0 a = some i)
    (hb : recPos r0 b = some i) : a = b := by
  unfold recPos at ha hb
  obtain ⟨h1, h1', -⟩ := List.findIdx?_eq_some_iff_getElem.mp ha
  obtain ⟨h2, h2', -⟩ := List.findIdx?_eq_some_iff_getElem.mp hb
  simp at h1' h2'; rw [← h1', ← h2']

theorem precedes_lt_idx (O : List CmdId) (a b : CmdId) (h : precedes O a b) : O.idxOf a < O.idxOf b :=
  ((precedes_iff O a b).mp h).2

theorem idxOf_lt_length {O : List CmdId} {a : CmdId} (h : a ∈ O) : O.idxOf a < O.length :=
  List.idxOf_lt_length_of_mem h

theorem takeWhile_split (A B : List CmdId) (z : CmdId) (hz : z ∉ A) :
    (A ++ z :: B).takeWhile (· != z) = A := by
  rw [List.takeWhile_append_of_pos]
  · simp
  · intro a ha; simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]; intro h; subst h; exact hz ha

/-- A command in a sequence of registered commands, before another. -/
theorem seqOf_split (S : PState) (O : List CmdId) (hnd : O.Nodup)
    (y z : CmdId) (cy cz : Cmd) (hy : S.cmds y = some cy) (hz : S.cmds z = some cz)
    (hzO : z ∈ O) (h : precedes O y z) :
    ∃ a b c, S.seqOf O = a ++ (y, cy) :: b ++ (z, cz) :: c := by
  obtain ⟨A, B, hO⟩ := List.append_of_mem hzO
  have hzA : z ∉ A := by
    intro hm; rw [hO, List.nodup_append] at hnd; exact hnd.2.2 z hm z (by simp) rfl
  have hyA : y ∈ A := by
    have : precedes (A ++ z :: B) y z := hO ▸ h
    unfold precedes at this; rwa [takeWhile_split A B z hzA] at this
  obtain ⟨T1, T2, hA⟩ := List.append_of_mem hyA
  rw [hO, hA, PState.seqOf_append, PState.seqOf_cons S z _ cz hz, PState.seqOf_append,
    PState.seqOf_cons S y _ cy hy]
  exact ⟨S.seqOf T1, S.seqOf T2, S.seqOf B, by simp⟩

/-- A recovery and the facts its proof uses: the pieces of `recoverSync N reps`, and what the
reports say of ballot `c = recMaxC acks`'s leader order `ord` (derived from `PInv`). -/
structure Ctx (S : PState) (N : Nat) (reps : List (Nat × Report)) where
  acks : List (Nat × Report)
  U : List (Nat × Report)
  R : List (Nat × Report)
  oldL : Nat
  leaderInU : Bool
  k1 : Kept
  k2 : Kept
  k3 : Kept
  k3b : Kept
  k4 : Kept
  ids : List CmdId
  ord : List CmdId
  hacks : acks = recAcks reps
  hU : U = recU acks
  hL : oldL = leaderOf N (recMaxC acks)
  hlU : leaderInU = U.any (·.1 == oldL)
  hR : R = U.filter (fun a => a.1 ∈ AQ N (recMaxC acks))
  h1 : k1 = rule1 oldL U
  h2 : k2 = rule2 k1 leaderInU R
  h3 : k3 = closure (recBest leaderInU R U acks) ((reps.flatMap (·.2.entries)).length + k2.length + 1) k2
  h3b : k3b = rule3b leaderInU R k3
  hids : ids = sortIds (k3b.map Prod.fst)
  h4 : k4 = rule4 ids k3b
  H : RecHyp oldL U leaderInU R
  reg : ∀ a ∈ U, ∀ e ∈ a.2.entries, S.cmds e.id = some e.cmd
  ordNd : ord.Nodup
  ordReg : ∀ y ∈ ord, S.cmds y ≠ none
  k0 : ∀ a ∈ U, ∀ e ∈ a.2.entries, okPhase oldL a e = true →
    e.id ∈ ord ∧ e.dep.Perm (depsIn (S.seqOf ord) e.id)
  pos : leaderInU = false → ∀ r0 rs, R = r0 :: rs → (r0.2.entries.map (·.id)).Nodup ∧
    ∀ e ∈ r0.2.entries, ¬ K0ok oldL U e.id → ∀ d ∈ e.dep,
      (∃ pd pe, recPos r0 d = some pd ∧ recPos r0 e.id = some pe ∧ pd < pe) ∧
      (∃ cd, S.cmds d = some cd ∧ cd.key = e.cmd.key)
  /-- every report's entries are registered (the closure's other entries, D33) -/
  regA : ∀ a ∈ acks, ∀ e ∈ a.2.entries, S.cmds e.id = some e.cmd
  /-- D33: the class-0 commands whose kept closure is acyclic: when the old leader reported,
  those it executed (`PState.lexec`); otherwise every class-0 command -/
  Gd : CmdId → Prop
  gK0 : ∀ y, Gd y → K0ok oldL U y
  gdeps : ∀ a ∈ U, ∀ e ∈ a.2.entries, okPhase oldL a e = true → Gd e.id → ∀ d ∈ e.dep, Gd d
  gall : leaderInU = false → ∀ y, K0ok oldL U y → Gd y

namespace Ctx
variable {S : PState} {N : Nat} {reps : List (Nat × Report)} (C : Ctx S N reps)

theorem sync_eq : recoverSync N reps =
    lkAlong ((recOrder C.k4 C.ids).filterMap (fun c => (C.k4.get c).map (fun e => (c, e.cmd)))) := by
  rw [C.h4, C.hids, C.h3b, C.h3, C.h2, C.h1, C.hR, C.hlU, C.hL, C.hU, C.hacks]; rfl

theorem graph : Graph C.oldL C.U C.leaderInU C.R C.acks C.k3 C.k3b C.k4 ∧ C.ids.Nodup ∧
    (∀ y, y ∈ C.ids ↔ (C.k4.get y).isSome) ∧ (∀ y, (C.k2.get y).isSome → (C.k3.get y).isSome) :=
  recover_graph N reps C.acks C.U C.R C.oldL C.leaderInU C.k1 C.k2 C.k3 C.k3b C.k4 C.ids
    C.hacks C.hU C.hL C.hlU C.hR C.h1 C.h2 C.h3 C.h3b C.hids C.h4 C.H

/-- The potential: class-0 commands by the leader's order, the others after, by `R[0]`'s. -/
noncomputable def phi (y : CmdId) : Nat :=
  open Classical in
  if K0ok C.oldL C.U y then C.ord.idxOf y else C.ord.length + (match C.R with
    | r0 :: _ => (recPos r0 y).getD 0
    | [] => 0)

theorem K0ok_ord {y : CmdId} (h : K0ok C.oldL C.U y) : y ∈ C.ord := by
  obtain ⟨a, ha, e, he, rfl, hok⟩ := h
  exact (C.k0 a ha e he hok).1

/-- A class-0 command's dependencies in the kept graph are the leader's. -/
theorem k0_deps {y : CmdId} {re : RecEntry} (hy : C.k4.get y = some re) (hK : K0ok C.oldL C.U y) :
    ∀ d, d ∈ re.dep ↔ d ∈ depsIn (S.seqOf C.ord) y := by
  obtain ⟨-, -, a, ha, e, he, hid, hok, -, hdep⟩ := C.graph.1.k0 y re hy hK
  intro d; rw [hdep]; subst hid; exact (C.k0 a ha e he hok).2.mem_iff

theorem k0_deps_ne {y : CmdId} {re : RecEntry} (hy : C.k4.get y = some re) (hK : K0ok C.oldL C.U y)
    {d : CmdId} (hd : d ∈ re.dep) : d ≠ y := by
  obtain ⟨-, -, a, ha, e, he, hid, hok, -, hdep⟩ := C.graph.1.k0 y re hy hK
  rw [hdep] at hd; subst hid; exact (C.H.k0 a ha e he hok d hd).1

/-- A `Gd` command's dependencies are `Gd` (D33). -/
theorem k0_deps_gd {y : CmdId} {re : RecEntry} (hy : C.k4.get y = some re) (hG : C.Gd y)
    {d : CmdId} (hd : d ∈ re.dep) : C.Gd d ∧ d ≠ y := by
  obtain ⟨-, -, a, ha, e, he, hid, hok, -, hdep⟩ := C.graph.1.k0 y re hy (C.gK0 y hG)
  rw [hdep] at hd; subst hid
  exact ⟨C.gdeps a ha e he hok hG d hd, (C.H.k0 a ha e he hok d hd).1⟩

/-- D33: the commands whose dependencies the potential orders: `Gd` ones, or every one when
the old leader did not report. -/
def Ac (y : CmdId) : Prop := C.Gd y ∨ C.leaderInU = false

theorem gd_of_ac {y : CmdId} (h : C.Ac y) (hK : K0ok C.oldL C.U y) : C.Gd y := by
  rcases h with h | h
  · exact h
  · exact C.gall h y hK

theorem seqOf_fst (O : List CmdId) (hreg : ∀ y ∈ O, S.cmds y ≠ none) : (S.seqOf O).map Prod.fst = O := by
  induction O with
  | nil => rfl
  | cons y O ih =>
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp (hreg y (by simp))
    rw [PState.seqOf_cons S y O c hc]; simp [ih (fun z hz => hreg z (by simp [hz]))]

theorem mem_seqOf {O : List CmdId} {y : CmdId} {c : Cmd} (h : (y, c) ∈ S.seqOf O) :
    S.cmds y = some c ∧ y ∈ O := by
  simp only [PState.seqOf, List.mem_filterMap, Option.map_eq_some_iff] at h
  obtain ⟨y', hy', c', hc', he⟩ := h
  simp at he; obtain ⟨rfl, rfl⟩ := he; exact ⟨hc', hy'⟩

/-- A dependency in the leader's order: before, of the same key. -/
theorem depsIn_ord {y d : CmdId} (hd : d ∈ depsIn (S.seqOf C.ord) y) :
    precedes C.ord d y ∧ ∃ cd cy, S.cmds d = some cd ∧ S.cmds y = some cy ∧ cd.key = cy.key := by
  obtain ⟨t, q, u, hs, hqy, hdt⟩ := depsIn_mem _ y d hd
  have hfst := seqOf_fst (S := S) C.ord C.ordReg
  rw [hs] at hfst
  have hnd := C.ordNd; rw [← hfst] at hnd
  have hq : q.1 ∉ t.map Prod.fst := by
    simp only [List.map_append, List.map_cons, List.nodup_append] at hnd
    intro h; exact hnd.2.2 q.1 h q.1 (by simp) rfl
  refine ⟨?_, ?_⟩
  · rw [← hfst, ← hqy]; simp only [List.map_append, List.map_cons]
    exact precedes_split _ _ _ _ hq hdt
  · -- the key, from `lkDeps`
    unfold depsIn at hd
    rw [hs, ← hqy, cmdIn_split t u q hq, before_split t u q hq] at hd
    simp only at hd
    obtain ⟨t1, q', t2, ht, hq'd, hk, -⟩ := (mem_lkDeps t q.2 d).mp hd
    have hq'mem : q' ∈ S.seqOf C.ord := by rw [hs, ht]; simp
    have hqmem : q ∈ S.seqOf C.ord := by rw [hs]; simp
    exact ⟨q'.2, q.2, hq'd ▸ (mem_seqOf hq'mem).1, hqy ▸ (mem_seqOf hqmem).1, hk⟩

theorem phi_edge {c d : CmdId} {re : RecEntry} (hc : C.k4.get c = some re) (hd : d ∈ re.dep)
    (hac : C.Ac c) : C.phi d < C.phi c ∧ C.Ac d := by
  have G := C.graph.1
  by_cases hK : K0ok C.oldL C.U c
  · have hG := C.gd_of_ac hac hK
    have hd' := (C.k0_deps hc hK d).mp hd
    have hdG := (C.k0_deps_gd hc hG hd).1
    have hdK := C.gK0 d hdG
    refine ⟨?_, Or.inl hdG⟩
    unfold phi; rw [if_pos hK, if_pos hdK]
    exact precedes_lt_idx _ _ _ (C.depsIn_ord hd').1
  · have hl : C.leaderInU = false := by
      rcases hac with h | h
      · exact absurd (C.gK0 c h) hK
      · exact h
    refine ⟨?_, Or.inr hl⟩
    obtain ⟨-, hnk⟩ := G.nk0 c re hc hK
    obtain ⟨r0, rs, hR0, e, he, hid, -, ex3, ex4, hdep, hex3, hex4⟩ := hnk hl
    obtain ⟨hnd0, hpos⟩ := C.pos hl r0 rs hR0
    have hphic : C.phi c = C.ord.length + (recPos r0 c).getD 0 := by
      unfold phi; rw [if_neg hK, hR0]
    have small : ∀ pd pc, recPos r0 d = some pd → recPos r0 c = some pc → pd < pc →
        C.phi d < C.phi c := by
      intro pd pc hpd hpc hlt
      rw [hphic, hpc]; unfold phi
      by_cases hdK : K0ok C.oldL C.U d
      · rw [if_pos hdK]; have := idxOf_lt_length (C.K0ok_ord hdK); simp; omega
      · rw [if_neg hdK, hR0]; simp only [hpd]; simp; omega
    rw [hdep] at hd
    rcases List.mem_append.mp hd with hd | hd
    · rcases List.mem_append.mp hd with hd | hd
      · subst hid
        obtain ⟨⟨pd, pe, hpd, hpe, hlt⟩, -⟩ := hpos e he hK d hd
        exact small pd pe hpd hpe hlt
      · obtain ⟨-, -, hne, ⟨pw, pc, hpw, hpc, hle⟩, -⟩ := hex3 d hd
        have : pw ≠ pc := fun h => hne (recPos_inj r0 d c pw hpw (h ▸ hpc))
        exact small pw pc hpw hpc (by omega)
    · obtain ⟨-, ⟨ea, hea, hea0⟩, -⟩ := hex4 d hd
      obtain ⟨ea3, hea3, hc3, -, -⟩ := G.m3b.back hea
      have hdK : K0ok C.oldL C.U d := (G.s3.cls hea3).mp (by rw [← hc3]; exact hea0)
      rw [hphic]; unfold phi; rw [if_pos hdK]
      have := idxOf_lt_length (C.K0ok_ord hdK); omega

theorem reach_phi {a b : CmdId} (h : Reach C.k4 a b) (ha : C.Ac a) : C.phi b < C.phi a ∧ C.Ac b := by
  induction h with
  | single hd =>
    unfold kdeps at hd
    cases hc : C.k4.get _ with
    | none => rw [hc] at hd; simp at hd
    | some re => rw [hc] at hd; exact C.phi_edge hc hd ha
  | tail _ hd ih =>
    unfold kdeps at hd
    obtain ⟨h1, h2⟩ := ih
    cases hm : C.k4.get _ with
    | none => rw [hm] at hd; simp at hd
    | some re => rw [hm] at hd; have := C.phi_edge hm hd h2; exact ⟨by omega, this.2⟩

theorem conflict_iff (a b : Cmd) : Cmd.conflict a b = true ↔ a.key = b.key ∧ (a.isPut = true ∨ b.isPut = true) := by
  unfold Cmd.conflict; simp

theorem kept_of_K0 {y : CmdId} (h : K0ok C.oldL C.U y) : (C.k4.get y).isSome :=
  (C.graph.1.keys y).mpr (C.graph.1.s3.2.2 y h)

/-- `recOrder` places every kept command once. -/
theorem order_mem : (∀ c, c ∈ recOrder C.k4 C.ids ↔ (C.k4.get c).isSome) ∧ (recOrder C.k4 C.ids).Nodup := by
  obtain ⟨-, hnd, hids, -⟩ := C.graph
  obtain ⟨hmem, hnd'⟩ := recOrder_mem C.k4 C.ids hnd
  exact ⟨fun c => (hmem c).trans (hids c), hnd'⟩

/-- From a `Gd` command, only earlier `Gd` commands are reached. -/
theorem reach_gd {a b : CmdId} (h : Reach C.k4 a b) (ha : C.Gd a) :
    C.Gd b ∧ precedes C.ord b a := by
  have edge : ∀ y d, C.Gd y → d ∈ kdeps C.k4 y → C.Gd d ∧ precedes C.ord d y := by
    intro y d hy hd
    unfold kdeps at hd
    cases hc : C.k4.get y with
    | none => rw [hc] at hd; simp at hd
    | some re =>
      rw [hc] at hd
      exact ⟨(C.k0_deps_gd hc hy hd).1, (C.depsIn_ord ((C.k0_deps hc (C.gK0 y hy) d).mp hd)).1⟩
  induction h with
  | single hd => exact edge _ _ ha hd
  | tail _ hd ih =>
    obtain ⟨h1, h2⟩ := ih
    obtain ⟨h3, h4⟩ := edge _ _ h1 hd
    exact ⟨h3, precedes_trans _ _ _ _ h4 h2⟩

/-- A `Gd` command reaches every earlier conflicting command of the leader's order. -/
theorem chain_gd {y z : CmdId} {cy cz : Cmd} (hz : C.Gd z) (hcy : S.cmds y = some cy)
    (hcz : S.cmds z = some cz) (hconf : Cmd.conflict cy cz = true) (hp : precedes C.ord y z) :
    Reach C.k4 z y := by
  obtain ⟨a, b, c', hs⟩ := seqOf_split S C.ord C.ordNd y z cy cz hcy hcz (C.K0ok_ord (C.gK0 z hz)) hp
  have hnd : ((S.seqOf C.ord).map Prod.fst).Nodup := by rw [seqOf_fst C.ord C.ordReg]; exact C.ordNd
  obtain ⟨hk, hput⟩ := (conflict_iff cy cz).mp hconf
  have hch := chain (S.seqOf C.ord) hnd b.length a b c' (y, cy) (z, cz) rfl hs hk hput
  -- every step is an edge of the kept graph, from a class-0 command
  have key : ∀ w, Relation.TransGen (fun a d => d ∈ depsIn (S.seqOf C.ord) a) z w →
      Reach C.k4 z w := by
    intro w hw
    induction hw with
    | single hd =>
      obtain ⟨re, hre⟩ := Option.isSome_iff_exists.mp (C.kept_of_K0 (C.gK0 z hz))
      apply Relation.TransGen.single
      unfold kdeps; rw [hre]; exact (C.k0_deps hre (C.gK0 z hz) _).mpr hd
    | tail _ hd ih =>
      rename_i m _
      have hm := C.gK0 _ (C.reach_gd ih hz).1
      obtain ⟨re, hre⟩ := Option.isSome_iff_exists.mp (C.kept_of_K0 hm)
      apply Relation.TransGen.tail ih
      unfold kdeps; rw [hre]; exact (C.k0_deps hre hm _).mpr hd
  exact key y hch

theorem cmd_k3 {y : CmdId} {re : RecEntry} (h : C.k3.get y = some re) : S.cmds y = some re.cmd := by
  rcases C.graph.1.s3.2.1 y re h with h' | h' | h'
  · obtain ⟨-, a, ha, e, he, rfl, -, hcmd, -⟩ := h'; rw [hcmd]; exact C.reg a ha e he
  · obtain ⟨-, hl, r0, rs, hR0, e, he, rfl, hcmd, -⟩ := h'
    rw [hcmd]
    have : r0 ∈ C.U := by
      have : r0 ∈ C.R := by rw [hR0]; simp
      rw [C.hR] at this; exact (List.mem_filter.mp this).1
    exact C.reg r0 this e he
  · obtain ⟨-, -, -, a, ha, e, he, rfl, hcmd⟩ := h'
    rw [hcmd]; exact C.regA a ha e he

theorem cmd_k3b {y : CmdId} {re : RecEntry} (h : C.k3b.get y = some re) : S.cmds y = some re.cmd := by
  obtain ⟨re3, h3, -, hm, -⟩ := C.graph.1.m3b.back h; rw [hm]; exact C.cmd_k3 h3

theorem cmd_k4 {y : CmdId} {re : RecEntry} (h : C.k4.get y = some re) : S.cmds y = some re.cmd := by
  obtain ⟨re3, h3, -, hm, -⟩ := C.graph.1.m4.back h; rw [hm]; exact C.cmd_k3b h3

theorem cls_k4 {y : CmdId} {re : RecEntry} (h : C.k4.get y = some re) : re.cls = 0 ↔ K0ok C.oldL C.U y := by
  obtain ⟨re3b, h3b, hc, -, -⟩ := C.graph.1.m4.back h
  obtain ⟨re3, h3, hc', -, -⟩ := C.graph.1.m3b.back h3b
  rw [hc, hc']; exact C.graph.1.s3.cls h3

theorem cls_k3b {y : CmdId} {re : RecEntry} (h : C.k3b.get y = some re) : re.cls = 0 ↔ K0ok C.oldL C.U y := by
  obtain ⟨re3, h3, hc', -, -⟩ := C.graph.1.m3b.back h
  rw [hc']; exact C.graph.1.s3.cls h3

theorem reach_kept {a b : CmdId} (h : Reach C.k4 a b) : (C.k4.get b).isSome := by
  have last : ∀ m d, d ∈ kdeps C.k4 m → (C.k4.get d).isSome := by
    intro m d hd; unfold kdeps at hd
    cases hm : C.k4.get m with
    | none => rw [hm] at hd; simp at hd
    | some re => rw [hm] at hd; exact C.graph.1.complete m re hm d hd
  cases h with
  | single hd => exact last _ _ hd
  | tail _ hd => exact last _ _ hd

/-- D33: a kept command after a `Gd` command `x` in the leader's order, of its key and
conflicting with it, reaches `x`: along the leader's dependency chain while it is class 0, by
rule 4 at the first other command (which `x`, reaching only `Gd` commands, does not reach). -/
theorem chain_in {x : CmdId} (hx : C.Gd x) : ∀ (n : Nat) (a b c' : Seq) (px pz : CmdId × Cmd),
    b.length = n → S.seqOf C.ord = a ++ px :: b ++ pz :: c' → px.1 = x → px.2.key = pz.2.key →
    (px.2.isPut ∨ pz.2.isPut) → (C.k4.get pz.1).isSome → Reach C.k4 pz.1 x := by
  have G := C.graph.1
  have hnd : ((S.seqOf C.ord).map Prod.fst).Nodup := by rw [seqOf_fst C.ord C.ordReg]; exact C.ordNd
  have hxK := C.gK0 x hx
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro a b c' px pz hn hs hpx hk hp hkz
    by_cases hzK : K0ok C.oldL C.U pz.1
    · obtain ⟨re, hre⟩ := Option.isSome_iff_exists.mp hkz
      have hnot : pz.1 ∉ (a ++ px :: b).map Prod.fst := by
        have hnd' := hnd; rw [hs] at hnd'
        have : (a ++ px :: b ++ pz :: c') = (a ++ px :: b) ++ pz :: c' := by simp
        rw [this, List.map_append, List.nodup_append] at hnd'
        intro hm; exact hnd'.2.2 pz.1 hm pz.1 (by simp) rfl
      have hdeps : depsIn (S.seqOf C.ord) pz.1 = lkDeps (a ++ px :: b) pz.2 := by
        rw [hs]
        have : (a ++ px :: b ++ pz :: c') = (a ++ px :: b) ++ pz :: c' := by simp
        rw [this]; exact depsIn_split _ _ _ hnot
      have edge : ∀ d, d ∈ depsIn (S.seqOf C.ord) pz.1 → Reach C.k4 pz.1 d := by
        intro d hd; apply Relation.TransGen.single; unfold kdeps; rw [hre]
        exact (C.k0_deps hre hzK d).mpr hd
      by_cases hb : ∃ q ∈ b, q.2.key = pz.2.key ∧ q.2.isPut = true
      · obtain ⟨b1, pm, b2, rfl, h1, h2, h3⟩ := last_put_split b pz.2.key hb
        have hedge : pm.1 ∈ depsIn (S.seqOf C.ord) pz.1 := by
          rw [hdeps, mem_lkDeps]
          exact ⟨a ++ px :: b1, pm, b2, by simp, rfl, h1, h3, Or.inl h2⟩
        have hpmk : (C.k4.get pm.1).isSome :=
          G.complete pz.1 re hre pm.1 ((C.k0_deps hre hzK _).mpr hedge)
        have hrec := ih b1.length (by rw [← hn]; simp) a b1 (b2 ++ pz :: c') px pm rfl
          (by rw [hs]; simp) hpx (by rw [hk, h1]) (Or.inr h2) hpmk
        exact Relation.TransGen.trans (edge _ hedge) hrec
      · have hb' : ∀ q ∈ b, q.2.key = pz.2.key → q.2.isPut = false := by
          intro q hq hk'; cases hc : q.2.isPut with
          | false => rfl
          | true => exact absurd ⟨q, hq, hk', hc⟩ hb
        rw [← hpx]; apply edge
        rw [hdeps, mem_lkDeps]
        exact ⟨a, px, b, rfl, rfl, hk, hb', hp⟩
    · have hcx : S.cmds px.1 = some px.2 :=
        (mem_seqOf (S := S) (O := C.ord) (y := px.1) (c := px.2) (by rw [hs]; simp)).1
      have hcz : S.cmds pz.1 = some pz.2 :=
        (mem_seqOf (S := S) (O := C.ord) (y := pz.1) (c := pz.2) (by rw [hs]; simp)).1
      obtain ⟨rez, hrez⟩ := Option.isSome_iff_exists.mp hkz
      obtain ⟨rex, hrex⟩ := Option.isSome_iff_exists.mp (C.kept_of_K0 hxK)
      obtain ⟨rez3, hz3, -, -, -⟩ := G.m4.back hrez
      obtain ⟨rex3, hx3, -, -, -⟩ := G.m4.back hrex
      have hconf : Cmd.conflict rex3.cmd rez3.cmd = true := by
        have e1 := C.cmd_k3b hx3; rw [← hpx, hcx] at e1
        have e2 := C.cmd_k3b hz3; rw [hcz] at e2
        rw [← Option.some.inj e1, ← Option.some.inj e2, conflict_iff]; exact ⟨hk, hp⟩
      rcases G.d4 pz.1 x (by rw [hz3]; rfl) (by rw [hx3]; rfl) rex3 rez3 hx3 hz3
          (fun h => hzK ((C.cls_k3b hz3).mp h)) ((C.cls_k3b hx3).mpr hxK) hconf with h | h
      · exact h
      · exact absurd (C.gK0 _ (C.reach_gd h hx).1) hzK

/-- What the recovery keeps of a command `x` (the three facts of the safety argument). -/
structure Safe (x : CmdId) : Prop where
  kept : (C.k4.get x).isSome
  inord : x ∈ C.ord
  s2 : ∀ y cy cx, (C.k4.get y).isSome → y ≠ x → S.cmds y = some cy → S.cmds x = some cx →
    Cmd.conflict cy cx = true → Reach C.k4 x y ∨ Reach C.k4 y x
  s3 : ∀ y, Reach C.k4 x y → precedes C.ord y x
  s4 : ∀ cx p, S.cmds x = some cx → cx.isGet = true → S.LastPut C.ord x cx.key (some p) →
    Reach C.k4 x p ∧ ∀ y, S.isPutOf cx.key y → Reach C.k4 x y → y ≠ p → Reach C.k4 p y
  /-- D33: what `x` reaches is acyclic (so `recOrder` places it after what it reaches) -/
  ac : C.Ac x

/-- The last put before a get is its dependency. -/
theorem lastPut_dep {x p : CmdId} {cx : Cmd} (hx : x ∈ C.ord) (hcx : S.cmds x = some cx)
    (hg : cx.isGet = true) (hp : S.LastPut C.ord x cx.key (some p)) :
    p ∈ depsIn (S.seqOf C.ord) x := by
  obtain ⟨hpx, ⟨cp, hcp, hkp, hpp⟩, hlast⟩ := hp
  have hnd := C.ordNd
  obtain ⟨A, B, hO⟩ := List.append_of_mem hx
  have hxA : x ∉ A := by
    intro hm; have := hnd; rw [hO, List.nodup_append] at this; exact this.2.2 x hm x (by simp) rfl
  have hpA : p ∈ A := by
    have : precedes (A ++ x :: B) p x := hO ▸ hpx
    unfold precedes at this; rwa [takeWhile_split A B x hxA] at this
  obtain ⟨A1, A2, hA⟩ := List.append_of_mem hpA
  have hregA : ∀ y ∈ A, S.cmds y ≠ none := fun y hy => C.ordReg y (by rw [hO]; simp [hy])
  have hseq : S.seqOf C.ord = S.seqOf A ++ (x, cx) :: S.seqOf B := by
    rw [hO, PState.seqOf_append, PState.seqOf_cons S x B cx hcx]
  have hxA' : x ∉ (S.seqOf A).map Prod.fst := by rw [seqOf_fst A hregA]; exact hxA
  rw [hseq]
  have := depsIn_split (S.seqOf A) (S.seqOf B) (x, cx) hxA'
  simp only at this; rw [this, mem_lkDeps]
  refine ⟨S.seqOf A1, (p, cp), S.seqOf A2, by rw [hA, PState.seqOf_append, PState.seqOf_cons S p A2 cp hcp], rfl,
    hkp, ?_, Or.inl hpp⟩
  intro q hq hk
  obtain ⟨hqc, hqA2⟩ := mem_seqOf hq
  cases hput : q.2.isPut with
  | false => rfl
  | true =>
    exfalso
    have hqx : precedes C.ord q.1 x := by
      rw [hO]; exact precedes_split A B x q.1 hxA (by rw [hA]; simp [hqA2])
    rcases hlast q.1 hqx ⟨q.2, hqc, hk, hput⟩ with h | h
    · have := hnd; rw [hO, hA] at this
      simp only [List.append_assoc, List.cons_append, List.nodup_append, List.nodup_cons] at this
      rw [h] at hqA2; exact this.2.1.1 (List.mem_append_left _ hqA2)
    · obtain ⟨A21, A22, hA2⟩ := List.append_of_mem hqA2
      have hO' : C.ord = (A1 ++ p :: A21) ++ q.1 :: (A22 ++ x :: B) := by rw [hO, hA, hA2]; simp
      have hqnot : q.1 ∉ A1 ++ p :: A21 := by
        intro hm; have := hnd; rw [hO', List.nodup_append] at this; exact this.2.2 q.1 hm q.1 (by simp) rfl
      have := precedes_split (A1 ++ p :: A21) (A22 ++ x :: B) q.1 p hqnot (by simp)
      rw [← hO'] at this
      exact precedes_antisymm _ _ _ h this

theorem conflict_symm (a b : Cmd) : Cmd.conflict a b = Cmd.conflict b a := by
  unfold Cmd.conflict; rw [Bool.or_comm]; congr 1; exact Bool.beq_comm

theorem safe_gd {x : CmdId} (hG : C.Gd x) : C.Safe x := by
  have G := C.graph.1
  have hK := C.gK0 x hG
  have hx := C.K0ok_ord hK
  refine ⟨C.kept_of_K0 hK, hx, ?_, fun y h => (C.reach_gd h hG).2, ?_, Or.inl hG⟩
  · intro y cy cx hy hne hcy hcx hconf
    by_cases hyK : K0ok C.oldL C.U y
    · rcases precedes_total C.ord y x (C.K0ok_ord hyK) hx hne with h | h
      · exact Or.inl (C.chain_gd hG hcy hcx hconf h)
      · right
        obtain ⟨a, b, c', hs⟩ := seqOf_split S C.ord C.ordNd x y cx cy hcx hcy (C.K0ok_ord hyK) h
        obtain ⟨hk, hput⟩ := (conflict_iff cx cy).mp (by rw [conflict_symm]; exact hconf)
        exact C.chain_in hG b.length a b c' (x, cx) (y, cy) rfl hs rfl hk hput hy
    · obtain ⟨rey, hrey⟩ := Option.isSome_iff_exists.mp hy
      obtain ⟨rex, hrex⟩ := Option.isSome_iff_exists.mp (C.kept_of_K0 hK)
      obtain ⟨rey3, hy3, -, -, -⟩ := G.m4.back hrey
      obtain ⟨rex3, hx3, -, -, -⟩ := G.m4.back hrex
      have h4 := G.d4 y x (by rw [hy3]; rfl) (by rw [hx3]; rfl) rex3 rey3 hx3 hy3
        (fun h => hyK ((C.cls_k3b hy3).mp h)) ((C.cls_k3b hx3).mpr hK)
        (by rw [C.cmd_k3b hx3] at hcx; rw [C.cmd_k3b hy3] at hcy; cases hcx; cases hcy
            rw [conflict_symm]; exact hconf)
      rcases h4 with h | h
      · exact Or.inr h
      · exact Or.inl h
  · intro cx p hcx hg hp
    have hpd := C.lastPut_dep hx hcx hg hp
    obtain ⟨re, hre⟩ := Option.isSome_iff_exists.mp (C.kept_of_K0 hK)
    have hxp : Reach C.k4 x p := by
      apply Relation.TransGen.single; unfold kdeps; rw [hre]; exact (C.k0_deps hre hK p).mpr hpd
    refine ⟨hxp, ?_⟩
    intro y hy hxy hne
    obtain ⟨-, hyx⟩ := C.reach_gd hxy hG
    obtain ⟨hpG, -⟩ := C.reach_gd hxp hG
    obtain ⟨-, hpput, hlast⟩ := hp
    rcases hlast y hyx hy with h | h
    · exact absurd h hne
    · obtain ⟨cy, hcy, hky, hpy⟩ := hy
      obtain ⟨cp, hcp, hkp, hpp⟩ := hpput
      exact C.chain_gd hpG hcy hcp (by rw [conflict_iff]; exact ⟨hky.trans hkp.symm, Or.inl hpy⟩) h

theorem recPos_of_mem {r0 : Nat × Report} {e : RepEntry} (he : e ∈ r0.2.entries) :
    ∃ p, recPos r0 e.id = some p := by
  apply Option.isSome_iff_exists.mp
  unfold recPos; rw [List.findIdx?_isSome, List.any_eq_true]; exact ⟨e, he, by simp⟩

/-- A kept command of class ≠ 0: `R[0]`'s entry, its dependencies with the appended ones. -/
theorem nk0_entry (hl : C.leaderInU = false) {r0 : Nat × Report} {rs : List (Nat × Report)}
    (hR0 : C.R = r0 :: rs) {y : CmdId}
    {re : RecEntry} (hy : C.k4.get y = some re) (hK : ¬ K0ok C.oldL C.U y) :
    ∃ e ∈ r0.2.entries, e.id = y ∧ re.cmd = e.cmd ∧ ∃ ex3 ex4, re.dep = e.dep ++ ex3 ++ ex4 ∧
      (∀ w ∈ ex3, P3b C.k3 r0 y w) ∧ (∀ a ∈ ex4, P4 C.k3b y a) := by
  obtain ⟨-, hnk⟩ := C.graph.1.nk0 y re hy hK
  obtain ⟨r0', rs', hR', e, he, hid, hcmd, ex3, ex4, hdep, hex3, hex4⟩ := hnk hl
  rw [hR0] at hR'; simp at hR'; obtain ⟨rfl, rfl⟩ := hR'
  exact ⟨e, he, hid, hcmd, ex3, ex4, hdep, hex3, hex4⟩

theorem entries3 {y : CmdId} {re : RecEntry} (h : C.k4.get y = some re) :
    ∃ re3b re3, C.k3b.get y = some re3b ∧ C.k3.get y = some re3 ∧ re3b.cls = re.cls ∧
      re3.cls = re.cls ∧ re3b.cmd = re.cmd ∧ re3.cmd = re.cmd := by
  obtain ⟨re3b, h3b, c1, m1, -⟩ := C.graph.1.m4.back h
  obtain ⟨re3, h3, c2, m2, -⟩ := C.graph.1.m3b.back h3b
  exact ⟨re3b, re3, h3b, h3, c1.symm, (c1.trans c2).symm, m1.symm, (m1.trans m2).symm⟩

/-- The precedence invariant along the paths from a command kept for the fast path. -/
def QF (r0 : Nat × Report) (x : CmdId) (cx : Cmd) (z : CmdId) : Prop :=
  precedes C.ord z x ∧ (∃ cz, S.cmds z = some cz ∧ cz.key = cx.key) ∧
  (¬ K0ok C.oldL C.U z → ∃ pz px, recPos r0 z = some pz ∧ recPos r0 x = some px ∧ pz < px)

theorem safe_fast {x : CmdId} {r0 : Nat × Report} {rs : List (Nat × Report)}
    (hl : C.leaderInU = false) (hR0 : C.R = r0 :: rs) (hK : ¬ K0ok C.oldL C.U x)
    (hkept : (C.k4.get x).isSome) (hx : x ∈ C.ord)
    (hdeps : ∀ e ∈ r0.2.entries, e.id = x → e.dep.Perm (depsIn (S.seqOf C.ord) x))
    (F2 : ∀ z pz px, recPos r0 z = some pz → recPos r0 x = some px → pz < px →
      (∃ cz cx, S.cmds z = some cz ∧ S.cmds x = some cx ∧ cz.key = cx.key) → precedes C.ord z x)
    (F3 : ∀ cx p, S.cmds x = some cx → cx.isGet = true → S.LastPut C.ord x cx.key (some p) →
      ∀ z pz px, ¬ K0ok C.oldL C.U z → recPos r0 z = some pz → recPos r0 x = some px → pz < px →
      S.isPutOf cx.key z → z ≠ p → ∃ pp, recPos r0 p = some pp ∧ pz < pp) :
    C.Safe x := by
  have G := C.graph.1
  obtain ⟨rex, hrex⟩ := Option.isSome_iff_exists.mp hkept
  have hcx := C.cmd_k4 hrex
  obtain ⟨ex, hex, hexid, hexcmd, ex3x, ex4x, hdepx, hex3x, hex4x⟩ := C.nk0_entry hl hR0 hrex hK
  obtain ⟨px, hpx⟩ := recPos_of_mem hex
  rw [hexid] at hpx
  obtain ⟨hnd0, hpos⟩ := C.pos hl r0 rs hR0
  -- a class-0 command conflicting with an earlier command than x is before x
  have k0_before : ∀ a z (ca cz : Cmd), K0ok C.oldL C.U a → ¬ K0ok C.oldL C.U z → S.cmds a = some ca →
      S.cmds z = some cz → Cmd.conflict ca cz = true → (z = x ∨ precedes C.ord z x) → precedes C.ord a x := by
    intro a z ca cz ha hz hca hcz hconf hzx
    have hane : a ≠ x := fun h => hK (h ▸ ha)
    rcases precedes_total C.ord a x (C.K0ok_ord ha) hx hane with h | h
    · exact h
    · exfalso
      have hza : precedes C.ord z a := by
        rcases hzx with rfl | hzx
        · exact h
        · exact precedes_trans _ _ _ _ hzx h
      exact hz (C.gK0 _ (C.reach_gd (C.chain_gd (C.gall hl a ha) hcz hca
        (by rw [conflict_symm]; exact hconf) hza) (C.gall hl a ha)).1)
  -- the invariant along every edge
  have step : ∀ z d, (z = x ∨ QF C r0 x rex.cmd z) → d ∈ kdeps C.k4 z → QF C r0 x rex.cmd d := by
    intro z d hz hd
    unfold kdeps at hd
    cases hre : C.k4.get z with
    | none => rw [hre] at hd; simp at hd
    | some re =>
      rw [hre] at hd; simp only [Option.map_some, Option.getD_some] at hd
      have hcz := C.cmd_k4 hre
      by_cases hzK : K0ok C.oldL C.U z
      · -- only on the invariant's side: x is not of class 0
        have hzQ : QF C r0 x rex.cmd z := by
          rcases hz with rfl | hz
          · exact absurd hzK hK
          · exact hz
        obtain ⟨hzx, ⟨cz, hcz', hkz⟩, -⟩ := hzQ
        obtain ⟨hdz, cd, cz', hcd, hcz'', hk⟩ := C.depsIn_ord ((C.k0_deps hre hzK d).mp hd)
        rw [hcz'] at hcz''; cases hcz''
        exact ⟨precedes_trans _ _ _ _ hdz hzx, ⟨cd, hcd, hk.trans hkz⟩,
          fun h => absurd (C.gK0 _ (C.k0_deps_gd hre (C.gall hl z hzK) hd).1) h⟩
      · obtain ⟨e, he, hid, hcmd, ex3, ex4, hdep, hex3, hex4⟩ := C.nk0_entry hl hR0 hre hzK
        -- z's position and key
        have hzinfo : ∃ pz, recPos r0 z = some pz ∧ pz ≤ px ∧ (z = x ∨ precedes C.ord z x) ∧
            re.cmd.key = rex.cmd.key := by
          rcases hz with rfl | ⟨hzx, ⟨cz, hcz', hkz⟩, hpz⟩
          · rw [hre] at hrex; cases hrex; exact ⟨px, hpx, Nat.le_refl _, Or.inl rfl, rfl⟩
          · obtain ⟨pz, px', hpz, hpx', hlt⟩ := hpz hzK
            rw [hpx] at hpx'; cases hpx'
            rw [hcz] at hcz'; cases hcz'
            exact ⟨pz, hpz, Nat.le_of_lt hlt, Or.inr hzx, hkz⟩
        obtain ⟨pz, hpz, hpzx, hzx, hkz⟩ := hzinfo
        -- an earlier command of `R[0]`'s report, of x's key
        have early : ∀ pd cd, recPos r0 d = some pd → pd < pz → S.cmds d = some cd →
            cd.key = rex.cmd.key → QF C r0 x rex.cmd d := by
          intro pd cd hpd hlt hcd hk
          refine ⟨F2 d pd px hpd hpx (by omega) ⟨cd, rex.cmd, hcd, hcx, hk⟩, ⟨cd, hcd, hk⟩, ?_⟩
          intro _; exact ⟨pd, px, hpd, hpx, by omega⟩
        rw [hdep] at hd
        rcases List.mem_append.mp hd with hd | hd
        · rcases List.mem_append.mp hd with hd | hd
          · subst hid
            obtain ⟨⟨pd, pe, hpd, hpe, hlt⟩, ⟨cd, hcd, hkd⟩⟩ := hpos e he hzK d hd
            rw [hpz] at hpe; cases hpe
            exact early pd cd hpd hlt hcd (by rw [hkd, ← hcmd]; exact hkz)
          · obtain ⟨-, -, hne, ⟨pw, pc, hpw, hpc, hle⟩, ⟨ew, ec, hw3, hc3, hconf⟩⟩ := hex3 d hd
            rw [hpz] at hpc; cases hpc
            have : pw ≠ pz := fun h => hne (recPos_inj r0 d z pw hpw (h ▸ hpz))
            have hcw := C.cmd_k3 hw3
            have hcc := C.cmd_k3 hc3
            rw [hcz] at hcc
            have hce : ec.cmd = re.cmd := (Option.some.inj hcc).symm
            rw [hce] at hconf
            exact early pw ew.cmd hpw (by omega) hcw (by rw [((conflict_iff _ _).mp hconf).1]; exact hkz)
        · obtain ⟨-, ⟨ea, hea, hea0⟩, ⟨ea', ec, hea', hec, hconf⟩⟩ := hex4 d hd
          rw [hea] at hea'; cases hea'
          have hdK : K0ok C.oldL C.U d := (C.cls_k3b hea).mp hea0
          have hcd := C.cmd_k3b hea
          have hcc := C.cmd_k3b hec
          rw [hcz] at hcc
          have hce : ec.cmd = re.cmd := (Option.some.inj hcc).symm
          rw [hce] at hconf
          refine ⟨k0_before d z ea.cmd re.cmd hdK hzK hcd hcz hconf hzx, ⟨ea.cmd, hcd, ?_⟩,
            fun h => absurd hdK h⟩
          rw [((conflict_iff _ _).mp hconf).1]; exact hkz
  have s3' : ∀ y, Reach C.k4 x y → QF C r0 x rex.cmd y := by
    intro y h
    induction h with
    | single hd => exact step _ _ (Or.inl rfl) hd
    | tail _ hd ih => exact step _ _ (Or.inr ih) hd
  obtain ⟨rx3b, rx3, hx3b, hx3, hcx3b, hcx3, hmx3b, hmx3⟩ := C.entries3 hrex
  have hx0 : rex.cls ≠ 0 := fun h => hK ((C.cls_k4 hrex).mp h)
  -- the dichotomy for two class ≠ 0 commands
  have d3 : ∀ y re, C.k4.get y = some re → ¬ K0ok C.oldL C.U y → ∀ z rz, C.k4.get z = some rz →
      ¬ K0ok C.oldL C.U z → ∀ py pz, recPos r0 y = some py → recPos r0 z = some pz → py ≤ pz →
      y ≠ z → Cmd.conflict re.cmd rz.cmd = true → Reach C.k4 z y ∨ Reach C.k4 y z := by
    intro y re hy hyK z rz hz hzK py pz hpy hpz hle hne hconf
    obtain ⟨-, ry3, -, hy3, -, -, -, hmy3⟩ := C.entries3 hy
    obtain ⟨-, rz3, -, hz3, -, hcz3, -, hmz3⟩ := C.entries3 hz
    exact G.d3b hl r0 rs hR0 z y (by rw [hz3]; rfl) ry3 rz3 pz py hy3 hz3
      (by rw [hcz3]; exact fun h => hzK ((C.cls_k4 hz).mp h)) hpz hpy hle hne
      (by rw [hmy3, hmz3]; exact hconf)
  refine ⟨hkept, hx, ?_, fun y h => (s3' y h).1, ?_, Or.inr hl⟩
  · intro y cy cx' hy hne hcy hcx' hconf
    obtain ⟨rey, hrey⟩ := Option.isSome_iff_exists.mp hy
    have hcy' := C.cmd_k4 hrey; rw [hcy] at hcy'; have hcye : rey.cmd = cy := (Option.some.inj hcy').symm
    rw [hcx] at hcx'; have hcxe : rex.cmd = cx' := Option.some.inj hcx'
    by_cases hyK : K0ok C.oldL C.U y
    · obtain ⟨ry3b, -, hy3b, -, hcy3b, -, hmy3b, -⟩ := C.entries3 hrey
      exact G.d4 x y (by rw [hx3b]; rfl) (by rw [hy3b]; rfl) ry3b rx3b hy3b hx3b
        (by rw [hcx3b]; exact hx0) (by rw [hcy3b]; exact (C.cls_k4 hrey).mpr hyK)
        (by rw [hmy3b, hmx3b, hcye, hcxe]; exact hconf)
    · obtain ⟨ey, hey, heyid, -⟩ := C.nk0_entry hl hR0 hrey hyK
      obtain ⟨py, hpy⟩ := recPos_of_mem hey
      rw [heyid] at hpy
      rcases Nat.le_total py px with hle | hle
      · exact d3 y rey hrey hyK x rex hrex hK py px hpy hpx hle hne (by rw [hcye, hcxe]; exact hconf)
      · rcases d3 x rex hrex hK y rey hrey hyK px py hpx hpy hle (Ne.symm hne)
          (by rw [hcye, hcxe, conflict_symm]; exact hconf) with h | h
        · exact Or.inr h
        · exact Or.inl h
  · intro cx' p hcx' hg hp
    rw [hcx] at hcx'; have hcxe : rex.cmd = cx' := Option.some.inj hcx'
    subst hcxe
    have hpd := C.lastPut_dep hx hcx hg hp
    have hxp : Reach C.k4 x p := by
      apply Relation.TransGen.single; unfold kdeps; rw [hrex]; simp only [Option.map_some, Option.getD_some]
      rw [hdepx]; apply List.mem_append_left; apply List.mem_append_left
      exact (hdeps ex hex hexid).mem_iff.mpr hpd
    refine ⟨hxp, ?_⟩
    intro y hy hxy hne
    obtain ⟨hyx, -, hyQ⟩ := s3' y hxy
    obtain ⟨hpxp, hpput, hlast⟩ := hp
    have hyp : precedes C.ord y p := by
      rcases hlast y hyx hy with h | h
      · exact absurd h hne
      · exact h
    obtain ⟨cy, hcy, hky, hpy⟩ := hy
    obtain ⟨cp, hcp, hkp, hpp⟩ := hpput
    have hconf : Cmd.conflict cy cp = true := by
      rw [conflict_iff]; exact ⟨hky.trans hkp.symm, Or.inl hpy⟩
    obtain ⟨rep, hrep⟩ := Option.isSome_iff_exists.mp (C.reach_kept hxp)
    have hcp' := C.cmd_k4 hrep; rw [hcp] at hcp'; have hcpe : rep.cmd = cp := (Option.some.inj hcp').symm
    by_cases hpK : K0ok C.oldL C.U p
    · exact C.chain_gd (C.gall hl p hpK) hcy hcp hconf hyp
    · obtain ⟨rey, hrey⟩ := Option.isSome_iff_exists.mp (C.reach_kept hxy)
      have hcy' := C.cmd_k4 hrey; rw [hcy] at hcy'; have hcye : rey.cmd = cy := (Option.some.inj hcy').symm
      by_cases hyK : K0ok C.oldL C.U y
      · obtain ⟨ry3b, -, hy3b, -, hcy3b, -, hmy3b, -⟩ := C.entries3 hrey
        obtain ⟨rp3b, -, hp3b, -, hcp3b, -, hmp3b, -⟩ := C.entries3 hrep
        rcases G.d4 p y (by rw [hp3b]; rfl) (by rw [hy3b]; rfl) ry3b rp3b hy3b hp3b
          (by rw [hcp3b]; exact fun h => hpK ((C.cls_k4 hrep).mp h))
          (by rw [hcy3b]; exact (C.cls_k4 hrey).mpr hyK)
          (by rw [hmy3b, hmp3b, hcye, hcpe]; exact hconf) with h | h
        · exact h
        · exact absurd (C.gK0 _ (C.reach_gd h (C.gall hl y hyK)).1) hpK
      · obtain ⟨py, px', hpy', hpx', hlt⟩ := hyQ hyK
        rw [hpx] at hpx'; cases hpx'
        obtain ⟨pp, hpp', hlt'⟩ := F3 rex.cmd p hcx hg ⟨hpxp, ⟨cp, hcp, hkp, hpp⟩, hlast⟩ y py px hyK hpy'
          hpx hlt ⟨cy, hcy, hky, hpy⟩ hne
        rcases d3 y rey hrey hyK p rep hrep hpK py pp hpy' hpp' (Nat.le_of_lt hlt') hne
          (by rw [hcye, hcpe]; exact hconf) with h | h
        · exact h
        · exfalso
          have := (C.reach_phi h (Or.inr hl)).1
          unfold phi at this; rw [if_neg hpK, if_neg hyK, hR0] at this
          simp only [hpp', hpy', Option.getD_some] at this; omega

theorem put_ne_get (c : Cmd) (hp : c.isPut = true) (hg : c.isGet = true) : False := by
  unfold Cmd.isPut at hp; unfold Cmd.isGet at hg
  simp at hp hg; rw [hp] at hg; revert hg; decide

theorem precedes_append_of_mem (O B : List CmdId) (y p : CmdId) (hp : p ∈ O) :
    precedes (O ++ B) y p ↔ precedes O y p := by
  unfold precedes
  induction O with
  | nil => simp at hp
  | cons a O ih =>
    simp only [List.cons_append, List.takeWhile_cons]
    by_cases hap : a = p
    · subst hap; simp
    · have h' : p ∈ O := by simp at hp; rcases hp with h | h; exact absurd h.symm hap; exact h
      have : (a != p) = true := by simpa using hap
      rw [if_pos this, if_pos this, List.mem_cons, List.mem_cons, ih h']

/-- The last element of a list with a property. -/
theorem exists_last (P : CmdId → Prop) (O : List CmdId) (hnd : O.Nodup) (h : ∃ y ∈ O, P y) :
    ∃ p ∈ O, P p ∧ ∀ y ∈ O, P y → y = p ∨ precedes O y p := by
  induction O using revInd with
  | h0 => simp at h
  | hs O a ih =>
    have hnd' : O.Nodup := (List.nodup_append.mp hnd).1
    have haO : a ∉ O := fun h' => (List.nodup_append.mp hnd).2.2 a h' a (by simp) rfl
    by_cases ha : P a
    · refine ⟨a, by simp, ha, ?_⟩
      intro y hy hPy
      simp at hy; rcases hy with hy | rfl
      · right; unfold precedes; rw [takeWhile_split O [] a haO]; exact hy
      · left; rfl
    · obtain ⟨p, hp, hPp, hmax⟩ := ih hnd' (by
        obtain ⟨y, hy, hPy⟩ := h; simp at hy; rcases hy with hy | rfl
        · exact ⟨y, hy, hPy⟩
        · exact absurd hPy ha)
      refine ⟨p, by simp [hp], hPp, ?_⟩
      intro y hy hPy
      simp at hy; rcases hy with hy | rfl
      · rcases hmax y hy hPy with h | h
        · exact Or.inl h
        · exact Or.inr ((precedes_append_of_mem O [a] y p hp).mpr h)
      · exact absurd hPy ha

theorem lastPut_exists (O : List CmdId) (hnd : O.Nodup) (x : CmdId) (k : w64) :
    ∃ p, S.LastPut O x k p := by
  by_cases h : ∃ y ∈ O, precedes O y x ∧ S.isPutOf k y
  · obtain ⟨p, -, ⟨hpx, hpp⟩, hmax⟩ := exists_last (fun y => precedes O y x ∧ S.isPutOf k y) O hnd h
    exact ⟨some p, hpx, hpp, fun y hy hpy => hmax y (precedes_mem O y x hy) ⟨hy, hpy⟩⟩
  · refine ⟨none, ?_⟩
    intro y hy hpy; exact h ⟨y, precedes_mem O y x hy, hy, hpy⟩

theorem resultIn_nonget (O : List CmdId) (hreg : ∀ y ∈ O, S.cmds y ≠ none) (x : CmdId) (cx : Cmd)
    (hx : x ∈ O) (hcx : S.cmds x = some cx) (hg : cx.isGet = false) : resultIn (S.seqOf O) x = [] := by
  unfold resultIn; rw [PState.cmdIn_seqOf S O x cx hx hcx hreg]; simp [hg]

/-- **`recOrder` around an `Ac` command** (D33): it is placed after what it reaches, and before
every kept command reaching it. Nothing is claimed of the rest of the kept graph. -/
theorem order_root {a : CmdId} (ha : C.Ac a) (hk : (C.k4.get a).isSome) :
    (∀ b, Reach C.k4 a b → precedes (recOrder C.k4 C.ids) b a) ∧
    (∀ y, Reach C.k4 y a → (C.k4.get y).isSome → precedes (recOrder C.k4 C.ids) a y) := by
  obtain ⟨G, hnd, hids, -⟩ := C.graph
  have hφ : ∀ c ∈ C.ids, C.Ac c → ∀ d ∈ kdeps C.k4 c, (C.k4.get d).isSome →
      d ∈ C.ids ∧ C.Ac d ∧ C.phi d < C.phi c := by
    intro c _ hc d hd hkd
    unfold kdeps at hd
    cases hce : C.k4.get c with
    | none => rw [hce] at hd; simp at hd
    | some re =>
      rw [hce] at hd
      have := C.phi_edge hce hd hc
      exact ⟨(hids d).mpr hkd, this.2, this.1⟩
  obtain ⟨l1, l2, hO, hOrd⟩ := recOrder_loc C.k4 C.ids hnd C.Ac C.phi hφ a ((hids a).mpr hk) ha
  obtain ⟨hmemO, hndO⟩ := C.order_mem
  have hOeq : recOrder C.k4 C.ids = (l1 ++ [a]) ++ l2 := by rw [hO]; simp
  have hndL : (l1 ++ [a]).Nodup := by rw [hOeq] at hndO; exact (List.nodup_append.mp hndO).1
  have hcomp : ∀ c ∈ l1 ++ [a], ∀ d ∈ kdeps C.k4 c, (C.k4.get d).isSome := by
    intro c hc d hd
    have hcO : c ∈ recOrder C.k4 C.ids := by rw [hOeq]; exact List.mem_append_left _ hc
    obtain ⟨re, hre⟩ := Option.isSome_iff_exists.mp ((hmemO c).mp hcO)
    unfold kdeps at hd; rw [hre] at hd
    exact G.complete c re hre d hd
  have hal1 : a ∉ l1 := by
    intro h; exact (List.nodup_append.mp hndL).2.2 a h a (by simp) rfl
  refine ⟨fun b h => ?_, fun y hy hky => ?_⟩
  · rw [hOeq]; exact (precedes_append_of_mem _ l2 b a (by simp)).mpr (hOrd.reach hndL hcomp (by simp) h)
  · have hyO := (hmemO y).mpr hky
    have hya : y ≠ a := by
      intro e; subst e
      have := (C.reach_phi hy ha).1; omega
    have hyL : y ∉ l1 ++ [a] := by
      intro hm
      have h1 := hOrd.reach hndL hcomp hm hy
      have hyl1 : y ∈ l1 := by
        simp at hm; rcases hm with h | h
        · exact h
        · exact absurd h hya
      have h2 : precedes (l1 ++ a :: []) y a := precedes_split l1 [] a y hal1 hyl1
      exact precedes_antisymm _ _ _ h1 h2
    have hyl2 : y ∈ l2 := by
      rw [hOeq] at hyO; rcases List.mem_append.mp hyO with h | h
      · exact absurd h hyL
      · exact h
    obtain ⟨m1, m2, hm⟩ := List.append_of_mem hyl2
    have hO2 : recOrder C.k4 C.ids = (l1 ++ [a] ++ m1) ++ y :: m2 := by rw [hOeq, hm]; simp
    have hyA : y ∉ l1 ++ [a] ++ m1 := by
      intro h
      rw [hO2] at hndO
      exact (List.nodup_append.mp hndO).2.2 y h y (by simp) rfl
    rw [hO2]; exact precedes_of_split _ m2 a y (by simp) hyA

theorem cs_eq : (recOrder C.k4 C.ids).filterMap (fun c => (C.k4.get c).map (fun e => (c, e.cmd))) =
    S.seqOf (recOrder C.k4 C.ids) := by
  have hk : ∀ c ∈ recOrder C.k4 C.ids, (C.k4.get c).isSome := fun c hc => (C.order_mem.1 c).mp hc
  unfold PState.seqOf
  have gen : ∀ l : List CmdId, (∀ c ∈ l, (C.k4.get c).isSome) →
      l.filterMap (fun c => (C.k4.get c).map (fun e => (c, e.cmd))) =
      l.filterMap (fun x => (S.cmds x).map (x, ·)) := by
    intro l hl
    induction l with
    | nil => rfl
    | cons c l ih =>
      obtain ⟨re, hre⟩ := Option.isSome_iff_exists.mp (hl c (by simp))
      simp only [List.filterMap_cons, hre, C.cmd_k4 hre, Option.map_some]
      rw [ih (fun c' h' => hl c' (by simp [h']))]
  exact gen _ hk

/-- **One recovery keeps a safe command**: in the `MSync`'s order, with the leader's result,
and after every conflicting command that was not before it in the leader's order. -/
theorem safe_sync {x : CmdId} (hs : C.Safe x) :
    x ∈ syncOrder (recoverSync N reps) ∧
    resultIn (S.seqOf (syncOrder (recoverSync N reps))) x = resultIn (S.seqOf C.ord) x ∧
    ∀ y, S.conflicts y x → precedes (syncOrder (recoverSync N reps)) y x → precedes C.ord y x := by
  obtain ⟨hmemO, hndO⟩ := C.order_mem
  let order := recOrder C.k4 C.ids
  have hreg : ∀ y ∈ order, S.cmds y ≠ none := by
    intro y hy; obtain ⟨re, hre⟩ := Option.isSome_iff_exists.mp ((hmemO y).mp hy)
    rw [C.cmd_k4 hre]; simp
  have hcsfst : (S.seqOf order).map Prod.fst = order := seqOf_fst order hreg
  have hcsnd : ((S.seqOf order).map Prod.fst).Nodup := by rw [hcsfst]; exact hndO
  obtain ⟨hmS, hndS, hpairs⟩ := syncOrder_lkAlong (S.seqOf order) hcsnd
  rw [C.sync_eq, C.cs_eq]
  rw [hcsfst] at hmS hpairs
  have hmemS : ∀ y, y ∈ syncOrder (lkAlong (S.seqOf order)) ↔ (C.k4.get y).isSome :=
    fun y => (hmS y).trans (hmemO y)
  have hregS : ∀ y ∈ syncOrder (lkAlong (S.seqOf order)), S.cmds y ≠ none := by
    intro y hy; obtain ⟨re, hre⟩ := Option.isSome_iff_exists.mp ((hmemS y).mp hy)
    rw [C.cmd_k4 hre]; simp
  -- a conflicting pair's order is the recovery's
  have pair : ∀ y z cy cz, (C.k4.get y).isSome → (C.k4.get z).isSome → S.cmds y = some cy →
      S.cmds z = some cz → y ≠ z → Cmd.conflict cy cz = true →
      (precedes (syncOrder (lkAlong (S.seqOf order))) y z ↔ precedes order y z) := by
    intro y z cy cz hy hz hcy hcz hne hconf
    obtain ⟨hk, hput⟩ := (conflict_iff cy cz).mp hconf
    apply hpairs y z cy cz ?_ ?_ hne hk hput
    · exact List.mem_filterMap.mpr ⟨y, (hmemO y).mpr hy, by simp [hcy]⟩
    · exact List.mem_filterMap.mpr ⟨z, (hmemO z).mpr hz, by simp [hcz]⟩
  obtain ⟨cx, hcx⟩ : ∃ cx, S.cmds x = some cx := by
    obtain ⟨re, hre⟩ := Option.isSome_iff_exists.mp hs.kept; exact ⟨_, C.cmd_k4 hre⟩
  -- a conflicting command before x in the MSync is reached from x
  have before_reach : ∀ y cy, S.cmds y = some cy → Cmd.conflict cy cx = true →
      precedes (syncOrder (lkAlong (S.seqOf order))) y x → Reach C.k4 x y := by
    intro y cy hcy hconf hyx
    have hy := (hmemS y).mp (precedes_mem _ _ _ hyx)
    have hne : y ≠ x := fun h => precedes_irrefl _ x (h ▸ hyx)
    have hyo := (pair y x cy cx hy hs.kept hcy hcx hne hconf).mp hyx
    rcases hs.s2 y cy cx hy hne hcy hcx hconf with h | h
    · exact h
    · exact absurd ((C.order_root hs.ac hs.kept).2 y h hy) (fun h' => precedes_antisymm _ _ _ hyo h')
  refine ⟨(hmemS x).mpr hs.kept, ?_, ?_⟩
  · cases hg : cx.isGet
    · rw [resultIn_nonget (S := S) _ hregS x cx ((hmemS x).mpr hs.kept) hcx hg,
        resultIn_nonget (S := S) _ C.ordReg x cx hs.inord hcx hg]
    · obtain ⟨p, hp⟩ := lastPut_exists (S := S) C.ord C.ordNd x cx.key
      rw [PState.resultIn_lastPut S _ C.ordNd C.ordReg x cx hs.inord hcx p hp]
      rw [PState.resultIn_lastPut S _ hndS hregS x cx ((hmemS x).mpr hs.kept) hcx p ?_]
      cases p with
      | none =>
        intro y hyx ⟨cy, hcy, hky, hpy⟩
        have hconf : Cmd.conflict cy cx = true := by rw [conflict_iff]; exact ⟨hky, Or.inl hpy⟩
        exact hp y (hs.s3 y (before_reach y cy hcy hconf hyx)) ⟨cy, hcy, hky, hpy⟩
      | some p =>
        obtain ⟨hxp, hmax⟩ := hs.s4 cx p hcx hg hp
        obtain ⟨-, ⟨cp, hcp, hkp, hpp⟩, -⟩ := hp
        have hpk := C.reach_kept hxp
        have hpne : p ≠ x := by
          intro h; subst h; rw [hcx] at hcp; cases hcp; exact put_ne_get _ hpp hg
        have hconfp : Cmd.conflict cp cx = true := by rw [conflict_iff]; exact ⟨hkp, Or.inl hpp⟩
        refine ⟨(pair p x cp cx hpk hs.kept hcp hcx hpne hconfp).mpr ((C.order_root hs.ac hs.kept).1 p hxp),
          ⟨cp, hcp, hkp, hpp⟩, ?_⟩
        intro y hyx ⟨cy, hcy, hky, hpy⟩
        have hconf : Cmd.conflict cy cx = true := by rw [conflict_iff]; exact ⟨hky, Or.inl hpy⟩
        have hxy := before_reach y cy hcy hconf hyx
        by_cases hyp : y = p
        · exact Or.inl hyp
        · right
          have hpy' := hmax y ⟨cy, hcy, hky, hpy⟩ hxy hyp
          have hconf' : Cmd.conflict cy cp = true := by
            rw [conflict_iff]; exact ⟨hky.trans hkp.symm, Or.inl hpy⟩
          exact (pair y p cy cp (C.reach_kept hxy) hpk hcy hcp hyp hconf').mpr
            ((C.order_root (C.reach_phi hxp hs.ac).2 hpk).1 y hpy')
  · intro y ⟨cy, cx', hcy, hcx', hconf⟩ hyx
    rw [hcx] at hcx'; cases hcx'
    exact hs.s3 y (before_reach y cy hcy hconf hyx)

/-- **One recovery keeps a safe get's last put** (identity-level S4, L1): the put before a safe
get `x` in the leader's order is its last put in the `MSync`'s order. -/
theorem safe_sync_lastPut {x : CmdId} (hs : C.Safe x) (cx : Cmd) (p : Option CmdId)
    (hcx : S.cmds x = some cx) (hg : cx.isGet = true) (hp : S.LastPut C.ord x cx.key p) :
    S.LastPut (syncOrder (recoverSync N reps)) x cx.key p := by
  obtain ⟨hmemO, hndO⟩ := C.order_mem
  let order := recOrder C.k4 C.ids
  have hreg : ∀ y ∈ order, S.cmds y ≠ none := by
    intro y hy; obtain ⟨re, hre⟩ := Option.isSome_iff_exists.mp ((hmemO y).mp hy)
    rw [C.cmd_k4 hre]; simp
  have hcsfst : (S.seqOf order).map Prod.fst = order := seqOf_fst order hreg
  have hcsnd : ((S.seqOf order).map Prod.fst).Nodup := by rw [hcsfst]; exact hndO
  obtain ⟨hmS, hndS, hpairs⟩ := syncOrder_lkAlong (S.seqOf order) hcsnd
  rw [C.sync_eq, C.cs_eq]
  rw [hcsfst] at hmS hpairs
  have hmemS : ∀ y, y ∈ syncOrder (lkAlong (S.seqOf order)) ↔ (C.k4.get y).isSome :=
    fun y => (hmS y).trans (hmemO y)
  have pair : ∀ y z cy cz, (C.k4.get y).isSome → (C.k4.get z).isSome → S.cmds y = some cy →
      S.cmds z = some cz → y ≠ z → Cmd.conflict cy cz = true →
      (precedes (syncOrder (lkAlong (S.seqOf order))) y z ↔ precedes order y z) := by
    intro y z cy cz hy hz hcy hcz hne hconf
    obtain ⟨hk, hput⟩ := (conflict_iff cy cz).mp hconf
    apply hpairs y z cy cz ?_ ?_ hne hk hput
    · exact List.mem_filterMap.mpr ⟨y, (hmemO y).mpr hy, by simp [hcy]⟩
    · exact List.mem_filterMap.mpr ⟨z, (hmemO z).mpr hz, by simp [hcz]⟩
  have before_reach : ∀ y cy, S.cmds y = some cy → Cmd.conflict cy cx = true →
      precedes (syncOrder (lkAlong (S.seqOf order))) y x → Reach C.k4 x y := by
    intro y cy hcy hconf hyx
    have hy := (hmemS y).mp (precedes_mem _ _ _ hyx)
    have hne : y ≠ x := fun h => precedes_irrefl _ x (h ▸ hyx)
    have hyo := (pair y x cy cx hy hs.kept hcy hcx hne hconf).mp hyx
    rcases hs.s2 y cy cx hy hne hcy hcx hconf with h | h
    · exact h
    · exact absurd ((C.order_root hs.ac hs.kept).2 y h hy) (fun h' => precedes_antisymm _ _ _ hyo h')
  cases p with
  | none =>
    intro y hyx ⟨cy, hcy, hky, hpy⟩
    have hconf : Cmd.conflict cy cx = true := by rw [conflict_iff]; exact ⟨hky, Or.inl hpy⟩
    exact hp y (hs.s3 y (before_reach y cy hcy hconf hyx)) ⟨cy, hcy, hky, hpy⟩
  | some p =>
    obtain ⟨hxp, hmax⟩ := hs.s4 cx p hcx hg hp
    obtain ⟨-, ⟨cp, hcp, hkp, hpp⟩, -⟩ := hp
    have hpk := C.reach_kept hxp
    have hpne : p ≠ x := by
      intro h; subst h; rw [hcx] at hcp; cases hcp; exact put_ne_get _ hpp hg
    have hconfp : Cmd.conflict cp cx = true := by rw [conflict_iff]; exact ⟨hkp, Or.inl hpp⟩
    refine ⟨(pair p x cp cx hpk hs.kept hcp hcx hpne hconfp).mpr ((C.order_root hs.ac hs.kept).1 p hxp),
      ⟨cp, hcp, hkp, hpp⟩, ?_⟩
    intro y hyx ⟨cy, hcy, hky, hpy⟩
    have hconf : Cmd.conflict cy cx = true := by rw [conflict_iff]; exact ⟨hky, Or.inl hpy⟩
    have hxy := before_reach y cy hcy hconf hyx
    by_cases hyp : y = p
    · exact Or.inl hyp
    · right
      have hpy' := hmax y ⟨cy, hcy, hky, hpy⟩ hxy hyp
      have hconf' : Cmd.conflict cy cp = true := by
        rw [conflict_iff]; exact ⟨hky.trans hkp.symm, Or.inl hpy⟩
      exact (pair y p cy cp (C.reach_kept hxy) hpk hcy hcp hyp hconf').mpr
        ((C.order_root (C.reach_phi hxp hs.ac).2 hpk).1 y hpy')

end Ctx

end sp

end Perennial.github_com.imdea_software.swiftpaxos

end
