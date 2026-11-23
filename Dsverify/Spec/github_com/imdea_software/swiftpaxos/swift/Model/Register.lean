/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/swift/Model/Register.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
A client's registration of a new command (`Inv.lean`'s `client_register`) as a step of the
protocol state: `PInv` is preserved.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Model.Defs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

namespace sp

namespace PState

/-- The state with `x` registered as `c`. -/
def register (S : PState) (x : CmdId) (c : Cmd) : PState :=
  { S with cmds := fun y => if y = x then some c else S.cmds y }

/-! ### Registering changes nothing of the registered commands (helpers) -/

section helpers
variable {S : PState} {N : Nat} {fr : Bool} {x : CmdId} {c : Cmd}

theorem register_cmds_ne (hx : S.cmds x = none) {y : CmdId} (hy : S.cmds y ≠ none) :
    (S.register x c).cmds y = S.cmds y := by
  have : y ≠ x := by rintro rfl; exact hy hx
  simp [register, this]

theorem register_seqOf (hx : S.cmds x = none) {l : List CmdId}
    (h : ∀ y ∈ l, S.cmds y ≠ none) : (S.register x c).seqOf l = S.seqOf l := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    have hy := h y (List.mem_cons_self ..)
    have ih := ih (fun z hz => h z (List.mem_cons_of_mem _ hz))
    unfold seqOf at ih ⊢
    rw [List.filterMap_cons, List.filterMap_cons, register_cmds_ne hx hy, ih]

theorem register_seqOf_loc (hI : S.PInv N fr) (hx : S.cmds x = none) (r b : Nat) :
    (S.register x c).seqOf ((S.register x c).loc r b) = S.seqOf (S.loc r b) :=
  register_seqOf hx (fun y hy => (hI.loc_ok r b).2.1 y hy)

theorem register_ordSeq (hI : S.PInv N fr) (hx : S.cmds x = none) (b : Nat) :
    (S.register x c).ordSeq N b = S.ordSeq N b :=
  register_seqOf_loc hI hx (leaderOf N b) b

theorem register_keyPrefix (hI : S.PInv N fr) (hx : S.cmds x = none) (r b : Nat) {y : CmdId}
    (hy : S.cmds y ≠ none) : (S.register x c).keyPrefix r b y = S.keyPrefix r b y := by
  have hd : ∀ n, (S.register x c).seqOf (((S.register x c).loc r b).drop n) =
      S.seqOf ((S.loc r b).drop n) := fun n =>
    register_seqOf hx (fun z hz => (hI.loc_ok r b).2.1 z (List.mem_of_mem_drop hz))
  unfold keyPrefix
  rw [register_cmds_ne hx hy, hd]
  rfl

theorem register_entryOk (hI : S.PInv N fr) (hx : S.cmds x = none) {r c' : Nat} {e : RepEntry}
    (h : S.entryOk N r c' e) : (S.register x c).entryOk N r c' e := by
  have hy : S.cmds e.id ≠ none := by rw [h.1]; simp
  unfold entryOk at h ⊢
  rw [register_cmds_ne hx hy, register_ordSeq hI hx, register_seqOf_loc hI hx]
  exact h

theorem register_repOk (hI : S.PInv N fr) (hx : S.cmds x = none) {r b : Nat} {R : Report}
    (h : S.repOk N r b R) : (S.register x c).repOk N r b R := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, fun e he => register_entryOk hI hx (h9 e he)⟩

end helpers

/-- Registering an unregistered command keeps the invariant. -/
theorem PInv_register {S : PState} {N : Nat} {fr : Bool} (hI : S.PInv N fr) (x : CmdId) (c : Cmd)
    (hx : S.cmds x = none) : (S.register x c).PInv N fr where
  loc_ok r b := ⟨(hI.loc_ok r b).1,
    fun y hy => by rw [register_cmds_ne hx ((hI.loc_ok r b).2.1 y hy)]; exact (hI.loc_ok r b).2.1 y hy,
    (hI.loc_ok r b).2.2⟩
  rs_ok := hI.rs_ok
  acc_ok r b y h := by rw [register_ordSeq hI hx]; exact hI.acc_ok r b y h
  pre_ok r b y D h := by rw [register_seqOf_loc hI hx]; exact hI.pre_ok r b y D h
  path_ok r b y P h := by
    have hp := hI.path_ok r b y P h
    rw [register_keyPrefix hI hx r b ((hI.loc_ok r b).2.1 y hp.1)]
    exact hp
  com_ok := hI.com_ok
  rep_ok r b R h := register_repOk hI hx (hI.rep_ok r b R h)
  sync_ok := hI.sync_ok
  rows_ok := hI.rows_ok
  G_ok := ⟨hI.G_ok.1, fun p hp => by
    rw [register_cmds_ne hx (by rw [hI.G_ok.2 p hp]; simp)]; exact hI.G_ok.2 p hp⟩

end PState

end sp

end Perennial.github_com.imdea_software.swiftpaxos

end
