/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/client/LinHelp.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The commit step (stage 1's L1, kept for L2: notes/prove-s2-e.md): committing the clients' atomic
updates in the order of the committed prefix.

* Pure: the abstract state as the puts of the committed prefix (`linPuts`, `lin.stateOf`) and a
  command's result (`resultIn`) agree (`apply_linPuts`), with `lin.keyName` injective.
* `commit_one`: committing one client's atomic update (`sp.cmdAU`) with the lock's half of
  `linOwn`'s ghost variable.
* `slots_commit`: committing the strategy's new operations `D` in order, each from its slot (an
  operation's slot: its update before it is committed, its continuation applied to its result
  after), every other slot carried from `G` to `G ++ D`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.Defs
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Model.Lin

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace sp

/-! ## Pure: the puts of a prefix and the results -/

/-- A command's put, as the abstract state's pair (none for a get). -/
def putOf (c : Cmd) : List (GoString × GoString) :=
  if c.isPut then [(lin.keyName c.key, c.val)] else []

theorem linPuts_snoc (G : Seq) (p : CmdId × Cmd) : linPuts (G ++ [p]) = linPuts G ++ putOf p.2 := by
  unfold linPuts putOf
  rw [List.filter_append, List.map_append]
  by_cases h : p.2.isPut = true <;> simp [h]

theorem stateOf_snoc (ps : List (GoString × GoString)) (q : GoString × GoString) :
    lin.stateOf (ps ++ [q]) = fun k => if k = q.1 then some q.2 else lin.stateOf ps k := by
  unfold lin.stateOf; erw [List.foldl_append]; rfl

theorem stateOf_putOf (ps : List (GoString × GoString)) (c : Cmd) :
    lin.stateOf (ps ++ putOf c) = (lin.apply c (lin.stateOf ps)).1 := by
  unfold putOf lin.apply
  by_cases h : c.isPut = true
  · simp only [h, ite_true]; rw [stateOf_snoc]
  · rw [if_neg h, if_neg h, List.append_nil]

theorem w8_toNat_lt (n : Nat) (h : n < 256) : (W8 n).toNat = n := by
  simp only [W8, BitVec.toNat_ofInt]
  omega

theorem keyName_inj {k k' : w64} (h : lin.keyName k = lin.keyName k') : k = k' := by
  unfold lin.keyName at h
  simp only [List.range, List.range.loop, List.map_cons, List.map_nil, List.cons.injEq] at h
  have e : ∀ a b : Nat, W8 ((a % 256 : Nat) : Int) = W8 ((b % 256 : Nat) : Int) →
      a % 256 = b % 256 := by
    intro a b hab
    have := congrArg BitVec.toNat hab
    simp only [W8, BitVec.toNat_ofInt] at this
    omega
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, -⟩ := h
  have := e _ _ h0; have := e _ _ h1; have := e _ _ h2; have := e _ _ h3
  have := e _ _ h4; have := e _ _ h5; have := e _ _ h6; have := e _ _ h7
  have hk := k.isLt; have hk' := k'.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [Nat.reducePow, Nat.reduceMul, Nat.pow_zero, Nat.div_one] at *
  omega

theorem stateOf_linPuts (G : Seq) (k : w64) :
    lin.stateOf (linPuts G) (lin.keyName k) =
      ((G.filter (fun p => p.2.key == k && p.2.isPut)).getLast?).map (fun p => p.2.val) := by
  suffices H : ∀ l : Seq, lin.stateOf (linPuts l.reverse) (lin.keyName k) =
      ((l.reverse.filter (fun p => p.2.key == k && p.2.isPut)).getLast?).map (fun p => p.2.val) by
    simpa using H G.reverse
  intro l
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [List.reverse_cons, linPuts_snoc]
    unfold putOf
    by_cases hp : p.2.isPut = true
    · simp only [hp, ite_true]
      rw [stateOf_snoc, List.filter_append]
      by_cases hk : p.2.key = k
      · subst hk; simp [hp]
      · have : lin.keyName k ≠ lin.keyName p.2.key := fun e => hk (keyName_inj e).symm
        simp only [this, ite_false, ih]
        have : (p.2.key == k && p.2.isPut) = false := by simp [hk]
        simp [this]
    · have hp' : p.2.isPut = false := by simpa using hp
      simp only [hp', Bool.false_eq_true, ite_false, List.append_nil]
      rw [ih, List.filter_append]
      have : (p.2.key == k && p.2.isPut) = false := by simp [hp]
      simp [this]

/-- The abstract state after the puts of `G` gives the next command its result in `G`. -/
theorem apply_linPuts (G : Seq) (x : CmdId) (c : Cmd) (hx : x ∉ G.map Prod.fst)
    (hc : c.isPut ∨ c.isGet) :
    (lin.apply c (lin.stateOf (linPuts G))).2 = resultIn (G ++ [(x, c)]) x := by
  have hcmd : cmdIn (G ++ [(x, c)]) x = some c := by
    have : ∀ (G : Seq), x ∉ G.map Prod.fst → cmdIn (G ++ [(x, c)]) x = some c := by
      intro G
      induction G with
      | nil => intro _; simp [cmdIn]
      | cons p G ih =>
        intro hx
        have hp : p.1 ≠ x := fun e => hx (by simp [e])
        have hG : x ∉ G.map Prod.fst := fun h => hx (by simp at h ⊢; exact Or.inr h)
        have := ih hG
        simp only [cmdIn] at this ⊢
        simp only [List.cons_append, List.find?_cons, show (p.1 == x) = false by simpa using hp]
        exact this
    exact this G hx
  have hbef : before (G ++ [(x, c)]) x = G := by
    have : ∀ (G : Seq), x ∉ G.map Prod.fst → before (G ++ [(x, c)]) x = G := by
      intro G
      induction G with
      | nil => intro _; simp [before]
      | cons p G ih =>
        intro hx
        have hp : p.1 ≠ x := fun e => hx (by simp [e])
        have hG : x ∉ G.map Prod.fst := fun h => hx (by simp at h ⊢; exact Or.inr h)
        simp only [before, List.cons_append, List.takeWhile_cons,
          show (p.1 != x) = true by simpa using hp, ite_true]
        exact congrArg _ (ih hG)
    exact this G hx
  unfold resultIn putsBefore lin.apply
  rw [hcmd]
  simp only [hbef]
  by_cases hput : c.isPut = true
  · have hget : c.isGet = false := by
      unfold Cmd.isPut at hput; unfold Cmd.isGet; simp at hput ⊢; rw [hput]; decide
    simp [hput, hget]
  · simp only [hput]
    by_cases hget : c.isGet = true
    · simp only [hget, ite_true, Bool.false_eq_true, ite_false]
      rw [stateOf_linPuts]
    · exact absurd (hc.resolve_left hput) hget

section vals
variable [GoGlobalContext] [go.IntoValInj w64]

theorem valW_enc (w : w64) : valW (#w) = w := by
  have h : ∃ w' : w64, (#w : val) = #w' := ⟨w, rfl⟩
  rw [valW, dif_pos h]
  exact (go.intoVal_inj (Classical.choose_spec h)).symm

theorem map_valW_enc (ws : List w64) : (ws.map (fun w => (#w : val))).map valW = ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [List.map_cons, valW_enc, ih]

/-- Resolving an event's words: the prophecy's decoding loses its head. -/
theorem decodeV_enc {e : PEv} (he : PEvWf e) (vs : List val) :
    decodeV (encV e ++ vs) = e :: decodeV vs := by
  unfold decodeV encV
  rw [List.map_append, map_valW_enc]
  exact decodeP_enc he _

end vals

/-! ## Committing one client's atomic update -/

section iris
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF] [π : NetProtoGS] [Perennial.github_com.imdea_software.swiftpaxos.sp.GobFmt]

/-- **One commit**: the lock's half of the abstract state's ghost variable (the puts `ps`)
commits a client's update of `c`: the state becomes `ps`'s with `c`'s put, the client's
continuation gets `c`'s result on `ps`'s state. At the updates' outer mask. -/
theorem commit_one (γl : GName) (c : Cmd) (Ψ : List w8 → IProp netDistGF)
    (ps : List (GoString × GoString)) :
    cmdAU γl c Ψ ∗ ghostVar γl (1 : Qp).half ps ⊢
      |={⊤ \ ↑spN}=> ghostVar γl (1 : Qp).half (ps ++ putOf c) ∗
        Ψ (lin.apply c (lin.stateOf ps)).2 := by
  unfold cmdAU
  iintro ⟨HAU, Hps⟩
  ihave Hacc := aupd_aacc $$ HAU
  unfold atomic_acc
  imod Hacc with ⟨%x, Hα, Hclose⟩
  rcases x with ⟨σ, ⟨⟩⟩
  dsimp only [Tele.app] at *
  unfold linOwn
  icases Hα with ⟨%ps', Hps', %Hσ⟩
  ihave %He := ghostVar_agree γl ps (1 : Qp).half ps' (1 : Qp).half $$ Hps Hps'
  subst He Hσ
  imod ghostVar_update_halves (ps ++ putOf c) γl ps ps $$ Hps Hps' with ⟨Hps, Hps'⟩
  icases Hclose with ⟨-, Hc⟩
  ihave Hc := (tforall_forall _).mp $$ Hc
  ispecialize Hc $$ %()
  imod Hc $$ [Hps'] with HΨ
  · iexists (ps ++ putOf c)
    iframe Hps'
    ipureintro
    exact (stateOf_putOf ps c).symm
  imodintro
  iframe

/-! ## The slots and the commits of a step -/

theorem slotL_frame (γl : GName) (G : Seq) (d : CmdId × Cmd) (k : CmdId) (cg : Cmd × GName)
    (hk : k ≠ d.1) : slotL γl G k cg ⊢ slotL γl (G ++ [d]) k cg := by
  unfold slotL
  iintro ⟨%Ψ, #Hs, H⟩
  iexists Ψ
  iframe Hs
  icases H with (⟨%hn, HAU⟩ | ⟨%hin, HΨ⟩)
  · ileft
    iframe HAU
    ipureintro
    simp only [List.map_append, List.mem_append, List.map_cons, List.map_nil,
      List.mem_singleton, not_or]
    exact ⟨hn, hk⟩
  · iright
    rw [resultIn_of_prefix ⟨[d], rfl⟩ hin]
    iframe HΨ
    ipureintro
    simp only [List.map_append, List.mem_append]
    exact Or.inl hin

/-- **One commit of a step**: the slot of `d` (not committed) commits its update; every other
slot is carried to `G ++ [d]`. -/
theorem slots_commit1 (γl : GName) (P : GMap CmdId (Cmd × GName)) (G : Seq) (d : CmdId × Cmd)
    (γΨ : GName) (hP : P.lookup d.1 = some (d.2, γΨ)) (hd : d.1 ∉ G.map Prod.fst)
    (hc : d.2.isPut ∨ d.2.isGet) :
    ([∗map] x ↦ cg ∈ P, slotL γl G x cg) ∗ ghostVar γl (1 : Qp).half (linPuts G) ⊢
      |={⊤ \ ↑spN}=> ([∗map] x ↦ cg ∈ P, slotL γl (G ++ [d]) x cg) ∗
        ghostVar γl (1 : Qp).half (linPuts (G ++ [d])) := by
  iintro ⟨Hm, Hps⟩
  ihave ⟨Hd, Hback⟩ := BigSepM.bigSepM_lookup_acc_impl
    (show Iris.Std.PartialMap.get? P d.1 = some (d.2, γΨ) from hP) $$ Hm
  ihave Hd2 : iprop(∃ Ψ : List w8 → IProp netDistGF, savedPredOwn γΨ .discard Ψ ∗
      ((⌜d.1 ∉ G.map Prod.fst⌝ ∗ cmdAU γl d.2 Ψ) ∨ (⌜d.1 ∈ G.map Prod.fst⌝ ∗
        Ψ (resultIn G d.1)))) $$ [Hd]
  · unfold slotL; iexact Hd
  icases Hd2 with ⟨%Ψ, #Hs, (⟨%_, HAU⟩ | ⟨%hin, -⟩)⟩
  · imod commit_one γl d.2 Ψ (linPuts G) $$ [HAU Hps] with ⟨Hps, HΨ⟩
    · iframe
    rw [apply_linPuts G d.1 d.2 hd hc, ← linPuts_snoc]
    imodintro
    iframe Hps
    ispecialize Hback $$ %(fun k cg => slotL γl (G ++ [d]) k cg)
    iapply Hback
    · imodintro
      iintro %k %cg %_ %hk H
      iapply slotL_frame γl G d k cg hk $$ H
    · unfold slotL
      iexists Ψ
      iframe Hs
      iright
      iframe HΨ
      ipureintro
      simp
  · exact absurd hin hd

/-- **The commits of a step** (`StepCommits`'s `D`, in order): each new operation's slot
commits its update; the abstract state's half follows the committed prefix. -/
theorem slots_commit (γl : GName) (P : GMap CmdId (Cmd × GName)) :
    ∀ (D G : Seq), (∀ p ∈ D, ∃ γΨ, P.lookup p.1 = some (p.2, γΨ)) →
    (∀ p ∈ D, p.1 ∉ G.map Prod.fst) → (D.map Prod.fst).Nodup →
    (∀ p ∈ D, p.2.isPut ∨ p.2.isGet) →
    ([∗map] x ↦ cg ∈ P, slotL γl G x cg) ∗ ghostVar γl (1 : Qp).half (linPuts G) ⊢
      |={⊤ \ ↑spN}=> ([∗map] x ↦ cg ∈ P, slotL γl (G ++ D) x cg) ∗
        ghostVar γl (1 : Qp).half (linPuts (G ++ D))
  | [], G, _, _, _, _ => by
    simp only [List.append_nil]
    iintro H
    imodintro
    iexact H
  | d :: D, G, hP, hf, hnd, hc => by
    obtain ⟨γΨ, hd⟩ := hP d (List.mem_cons_self ..)
    have hnd' : (D.map Prod.fst).Nodup := (List.nodup_cons.mp hnd).2
    have hdD : d.1 ∉ D.map Prod.fst := (List.nodup_cons.mp hnd).1
    have ih := slots_commit γl P D (G ++ [d]) (fun p hp => hP p (List.mem_cons_of_mem _ hp))
      (fun p hp => by
        simp only [List.map_append, List.mem_append, List.map_cons, List.map_nil,
          List.mem_singleton, not_or]
        exact ⟨hf p (List.mem_cons_of_mem _ hp), fun e => hdD (e ▸ List.mem_map_of_mem hp)⟩)
      hnd' (fun p hp => hc p (List.mem_cons_of_mem _ hp))
    rw [show G ++ d :: D = (G ++ [d]) ++ D by simp]
    iintro H
    imod slots_commit1 γl P G d γΨ hd (hf d (List.mem_cons_self ..)) (hc d (List.mem_cons_self ..))
      $$ H with H
    iapply ih $$ H

end iris


end sp

end Perennial.github_com.imdea_software.swiftpaxos

end
